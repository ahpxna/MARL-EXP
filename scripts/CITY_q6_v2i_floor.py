#!/usr/bin/env python3
"""Q6 (research/city_sim/PROTOCOL_CITY_Q6_V2I_FLOOR_20261002.md, written 19:3x EDT 02/10/2026): rule A in a V2I domain.  A car
chooses one of m = 8 routes, each through one renewal light (ACT = U{20..40}); SPaT records reach it through an age-first
broadcast of K records per second.  Learned message car (shared MLP over routes) vs the exact compiled-silent car (shortest
route); gain = 1 − regret(message) / regret(silent).  Channel count net = fresh − stale_τ (τ = training max age); sign rule
gain > 0 iff net/m > θ = −0.08 (frozen, E3).
Usage: CITY_q6_v2i_floor.py --out DIR [--smoke]"""
from __future__ import annotations
import argparse, hashlib, json, time
from pathlib import Path
import numpy as np
import torch
from torch import nn

M, V, LO, HI, THETA = 8, 12.0, 20, 40, -0.08
TRAIN = ['K1', 'K2', 'K4', 'K8', 'IID']; DEPLOY = [1, 2, 3, 4, 8]


def ages_age_first(n, Kspec, rng, burn=24):
    """Ages of the m records under an age-first broadcast of K per second (K fixed or iid U{1..8})."""
    a = rng.integers(0, 30, (n, M)).astype(np.int64)
    for _ in range(burn):
        a += 1; K = rng.integers(1, M + 1, n) if Kspec == 'IID' else np.full(n, int(Kspec))
        order = np.argsort(-(a + rng.random((n, M)) * 0.5), axis=1)               # oldest first, random tie-break
        rank = np.empty_like(order); np.put_along_axis(rank, order, np.arange(M)[None].repeat(n, 0), axis=1)
        a = np.where(rank < K[:, None], 0, a)
    return a


def lights(n, rng, back=40, fwd=140):
    """Renewal lights (ACT) for n decisions × M routes: switch times from −back to +fwd (stationary start)."""
    d = np.arange(LO, HI + 1); p1 = d / d.sum()
    first = rng.choice(d, size=(n, M), p=p1); e = (rng.random((n, M)) * first).astype(np.int64)
    S0 = -back - e; c0 = rng.integers(0, 2, (n, M))
    durs = rng.integers(LO, HI + 1, (n, M, 12)); durs[..., 0] = first
    sw = S0[..., None] + np.cumsum(durs, axis=-1)                                     # switch times (end of phase k)
    return S0, c0, sw


def state_at(S0, c0, sw, x):
    """colour (1 green) and time in phase at integer time x (array broadcast to (n, M))."""
    k = (sw <= x[..., None]).sum(-1); last = np.where(k > 0, np.take_along_axis(sw, np.maximum(k - 1, 0)[..., None], -1)[..., 0], S0)
    return (c0 + k) % 2, x - last


def make(n, Kspec, rng):
    dist = rng.uniform(100, 400, (n, M)); age = ages_age_first(n, Kspec, rng); S0, c0, sw = lights(n, rng)
    g_copy, t_copy = state_at(S0, c0, sw, -age)
    arr = np.round(dist / V).astype(np.int64); g_arr, _ = state_at(S0, c0, sw, arr)
    k = (sw <= arr[..., None]).sum(-1); nxt = np.take_along_axis(sw, k[..., None], -1)[..., 0]
    cost = dist / V + np.where(g_arr == 1, 0, nxt - arr)
    X = np.stack([dist / 400, g_copy, t_copy / 60, age / 10], -1).astype(np.float32)
    return X, cost.astype(np.float32), age


def fit(X, Y, seed, epochs=6):
    torch.manual_seed(seed); net = nn.Sequential(nn.Linear(4, 64), nn.ReLU(), nn.Linear(64, 64), nn.ReLU(), nn.Linear(64, 1))
    Xt = torch.as_tensor(X.reshape(-1, 4)); Yt = torch.as_tensor(Y.reshape(-1, 1) / 30); opt = torch.optim.Adam(net.parameters(), 1e-3)
    g = torch.Generator().manual_seed(seed)
    for _ in range(epochs):
        perm = torch.randperm(len(Xt), generator=g)
        for i in range(0, len(Xt), 4096):
            b = perm[i:i + 4096]; loss = ((net(Xt[b]) - Yt[b]) ** 2).mean(); opt.zero_grad(); loss.backward(); opt.step()
    return net


def evaluate(net, X, cost):
    with torch.no_grad():
        pred = net(torch.as_tensor(X.reshape(-1, 4))).numpy().reshape(cost.shape)
    best = cost.min(1); r_msg = cost[np.arange(len(cost)), pred.argmin(1)] - best
    r_sil = cost[np.arange(len(cost)), X[..., 0].argmin(1)] - best
    return float(r_msg.mean()), float(r_sil.mean())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke); torch.set_num_threads(1)
    NTR, NEV, seeds = (5000, 3000, [0]) if a.smoke else (200000, 50000, [0, 1, 2]); t0 = time.perf_counter(); cells = []
    for s in seeds:
        for tr in TRAIN:
            rng = np.random.default_rng([s, TRAIN.index(tr)]); X, Y, ag = make(NTR, 'IID' if tr == 'IID' else tr[1:], rng)
            tau = int(ag.max()); net = fit(X, Y, 100 * s + TRAIN.index(tr))
            for K in DEPLOY:
                re = np.random.default_rng([9700 + s, K]); Xe, Ce, Ae = make(NEV, str(K), re)
                rm, rs = evaluate(net, Xe, Ce); gain = 1 - rm / rs
                fresh = (Ae == 0).sum(1); stale = (Ae > tau).sum(1); net_m = float(np.mean(fresh - stale) / M)
                kmin = (1 + THETA) * M / (tau + 2)
                cells.append(dict(seed=s, train=tr, tau=tau, K=K, regret_msg=rm, regret_silent=rs, gain=gain, net_over_m=net_m, kmin=kmin))
                print(f'[{time.perf_counter() - t0:.0f}s] s{s} train {tr} (tau {tau}) K {K}: gain {gain:+.3f} net/m {net_m:+.3f} K_min {kmin:.2f}', flush=True)
    (out / 'cells.json').write_text(json.dumps(cells, indent=1))
    agg = {}
    for c in cells:
        agg.setdefault((c['train'], c['K']), []).append(c)
    L = ['Q6 gain over compiled silence (mean over seeds) by training channel (rows) and deployment K (columns); net/m in brackets',
         'train (tau) | ' + ' | '.join(f'K {K}' for K in DEPLOY)]
    hit = tot = 0; v2 = True
    for tr in TRAIN:
        row = []
        for K in DEPLOY:
            cs = agg[(tr, K)]; g = float(np.mean([c['gain'] for c in cs])); nm = float(np.mean([c['net_over_m'] for c in cs])); km = cs[0]['kmin']
            row.append(f'{g:+.3f} [{nm:+.2f}]')
            if abs(g) > 0.02:
                tot += 1; hit += (g > 0) == (nm > THETA)
            if tr != 'IID' and K <= km and g > 0.02:
                v2 = False
        L.append(f'{tr} ({agg[(tr, DEPLOY[0])][0]["tau"]}) | ' + ' | '.join(row))
    pred = {'V1 sign rule agreement >= 80 %': dict(hits=hit, cells=tot, rate=hit / max(1, tot), pass_=bool(tot and hit / tot >= 0.8)),
            'V2 no gain > 0.02 at K <= K_min (constant training channels)': dict(pass_=v2),
            'V3 IID-trained gains (reported)': dict(gains=[float(np.mean([c['gain'] for c in agg[('IID', K)]])) for K in DEPLOY], pass_=True)}
    L += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                                                       smoke=a.smoke, protocol='research/city_sim/PROTOCOL_CITY_Q6_V2I_FLOOR_20261002.md'), indent=1))


if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true'); main(ap.parse_args())
