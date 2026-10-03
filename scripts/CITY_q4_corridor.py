#!/usr/bin/env python3
"""Q4 (research/city_sim/PROTOCOL_CITY_Q4_CORRIDOR_20261002.md, written 19:1x EDT 02/10/2026): staggered corridor upgrades.
Two fixed-time 30/30 lights; the car passes light 1 at s ~ U{0..29} into its green; light 2's green starts O s later.  OLD
corridor O = 15; upgraded corridors O ∈ {20, 25, 30, 35, 45} and RANDOM.  Light 2's own timing law never changes (single-light
certificate K = 0); the corridor certificate is the TV distance between light 2's (colour, τ) start distributions.  Students
and the privileged regret metric come from scripts/CITY_c0_testbed.py (v3, imported, its sha recorded).
Modes: --panels | --seed S | --merge.   Usage: CITY_q4_corridor.py --out DIR (--panels | --seed S | --merge) [--smoke]"""
from __future__ import annotations
import argparse, hashlib, importlib.util, json, time
from pathlib import Path
import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[1]; C0P = ROOT / 'scripts' / 'CITY_c0_testbed.py'
spec = importlib.util.spec_from_file_location('c0', C0P); c0 = importlib.util.module_from_spec(spec); spec.loader.exec_module(c0)
T, XM, NA, EPS = c0.T, c0.XM, c0.NA, c0.EPS
CORR = ['OLD', '20', '25', '30', '35', '45', 'RANDOM']; OFF = {'OLD': 15}
PSEED = {k: 9400 + i for i, k in enumerate(CORR)}


def corridor_eps(spec_, n, rng):
    s = rng.integers(0, 30, n)
    O = rng.integers(0, 60, n) if spec_ == 'RANDOM' else np.full(n, OFF.get(spec_, None) if spec_ in OFF else int(spec_))
    c = ((s - O)[:, None] + np.arange(T + 2)[None]) % 60
    green = c < 30; tau = np.where(green, c, c - 30).astype(np.int32); res = (30 - tau).astype(np.int32)
    return green, tau, res, -rng.integers(150, 251, n), rng.integers(8, 13, n), (s - O) % 60


def start_hist(spec_, n=200000, seed=0):
    return np.bincount(corridor_eps(spec_, n, np.random.default_rng(seed))[5], minlength=60) / n


def collect(spec_, V, kind, n, rng, drivers, chunk=500):
    O, Y = [], []
    for c0_ in range(0, n, chunk):
        m = min(chunk, n - c0_); G, TA, RS, X0, V0, _ = corridor_eps(spec_, m, rng)
        for drive in drivers:
            x, v, alive = X0.copy(), V0.copy(), np.ones(m, bool)
            for t in range(T):
                idx = np.flatnonzero(alive)
                if len(idx) == 0:
                    break
                q = c0.table_q(V, kind, 'FT', x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t])
                O.append(np.stack([x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t]], 1).astype(np.float64)); Y.append(q)
                ai = drive(q, x[idx], v[idx], G[idx, t], TA[idx, t], RS[idx, t])
                x2, v2, _, passed, _ = c0.step(x[idx], v[idx], ai, G[idx, t + 1]); x[idx], v[idx] = x2, v2; alive[idx[passed]] = False
    return np.concatenate(O), np.concatenate(Y)


def cells_of(O):
    return (O[:, 2].astype(np.int64) * 100 + O[:, 3].astype(np.int64)) * 100000 + ((-O[:, 0]) // 10).astype(np.int64) * 100 + O[:, 1].astype(np.int64)


def run_panels(a, out, n):
    (out / 'panels').mkdir(parents=True, exist_ok=True); tb = c0.bayes_tables('FT')
    np.savez_compressed(out / 'panels' / 'FT_tables.npz', Z=tb['Z'], M=tb['M'])
    for k in CORR:
        t0 = time.perf_counter(); G, TA, R, x0, v0, _ = corridor_eps(k, n, np.random.default_rng(PSEED[k])); topt = np.empty(n)
        for i in range(0, n, 200):
            V0 = c0.dp_batch(G[i:i + 200], tab=False, dtype=np.float64); kk = np.arange(len(V0)); topt[i:i + 200] = V0[kk, x0[i:i + 200] + XM, v0[i:i + 200]]
        P = dict(green=G, tau=TA, res=R, x0=x0, v0=v0, topt=topt); np.savez_compressed(out / 'panels' / f'{k}.npz', **P)
        rz = c0.rollout(c0.table_policy(tb['Z'].astype(np.float64), 'Z', 'FT'), P)['regret']
        assert np.abs(rz).max() < 1e-6, ('Z*_FT must equal the privileged optimum on a deterministic light', k, float(np.abs(rz).max()))
        print(f'panel {k}: {n} episodes, Z*_FT regret max {float(np.abs(rz).max()):.1e} (exact)  [{time.perf_counter() - t0:.0f}s]', flush=True)


def run_seed(a, out, sizes):
    NTR, EPO = sizes; DR, ND, EPD = (1, 10, 1) if a.smoke else (2, NTR // 3, 4); s = a.seed; t0 = time.perf_counter()
    z = np.load(out / 'panels' / 'FT_tables.npz'); TB = {'Z': z['Z'].astype(np.float64), 'M': z['M'].astype(np.float64)}
    P = {k: {kk: v for kk, v in np.load(out / 'panels' / f'{k}.npz').items()} for k in CORR}
    nets, info, dens = {}, {}, None
    for k in CORR:
        for msg in (False, True):
            kind = 'M' if msg else 'Z'; nm = f'{kind}_{k}'; sdn = 100 * s + len(nets)
            rng = np.random.default_rng([1100 + s, sdn]); trng = np.random.default_rng([5100 + s, sdn])
            Od, Yd = collect(k, TB[kind], kind, NTR, rng, [c0.noisy_teacher(e, trng) for e in EPS])
            net, loss, agree = c0.train_net(Od, Yd, msg, sdn, EPO); drng = np.random.default_rng([3100 + s, sdn])
            for r in range(DR):
                O2, Y2 = collect(k, TB[kind], kind, ND, drng, [c0.student_driver(net, msg)]); Od, Yd = np.concatenate([Od, O2]), np.concatenate([Yd, Y2])
                net, loss, agree = c0.train_net(Od, Yd, msg, sdn + 1 + r, EPD, net=net)
            nets[nm] = (net, msg); info[nm] = dict(loss=loss, agree=agree, n=int(len(Yd)))
            if nm == 'Z_OLD':
                cc, cnt = np.unique(cells_of(Od), return_counts=True); dens = (cc, cnt, len(Od), int(Od[Od[:, 2] > 0.5, 3].max()), int(Od[Od[:, 2] < 0.5, 3].max()))
        print(f'seed {s}: trained {k}  [{time.perf_counter() - t0:.0f}s]', flush=True)
    REG, cells = {}, {}
    for nm, (net, msg) in nets.items():
        for k in (CORR if nm.endswith('_OLD') else [nm.split('_', 1)[1]]):
            r = c0.rollout(c0.net_policy(net, msg), P[k]); REG[f'{nm}|{k}'] = r['regret']; cells[f'{nm}|{k}'] = float(r['regret'].mean())
    cc, cnt, ntr, tmg, tmr = dens; rare = cc[cnt * 1e5 / ntr >= 5]
    for k in CORR:
        rec = []
        def pol(x, v, g, ta, rs, net=nets['Z_OLD'][0]):
            rec.append(np.stack([x, v, g.astype(np.int64), ta, rs], 1)); return c0.net_policy(net, False)(x, v, g, ta, rs)
        c0.rollout(pol, P[k]); Os = np.concatenate(rec).astype(np.float64)
        cells[f'range_monitor|{k}'] = float(np.mean(Os[:, 3] > np.where(Os[:, 2] > 0.5, tmg, tmr)))
        cells[f'density_monitor|{k}'] = float(np.mean(~np.isin(cells_of(Os), rare)))
        r = c0.rollout(c0.rule_policy, P[k]); cells[f'rule|{k}'] = float(r['regret'].mean())
    sd = out / f'seed_{s}'; sd.mkdir(parents=True, exist_ok=a.smoke)
    (sd / 'cells.json').write_text(json.dumps(dict(seed=s, c0_sha256=hashlib.sha256(C0P.read_bytes()).hexdigest(),
                                                   q4_sha256=SRC, train=info, cells=cells, elapsed_s=time.perf_counter() - t0), indent=1))
    np.savez_compressed(sd / 'regrets.npz', **REG)
    print(f'seed {s}: Z_OLD on ' + ', '.join(f'{k} {cells[f"Z_OLD|{k}"]:.2f} (spec {cells[f"Z_{k}|{k}"]:.2f})' for k in CORR) + f'  [{time.perf_counter() - t0:.0f}s]', flush=True)


def run_merge(a, out):
    seeds = sorted(int(p.name.split('_')[1]) for p in out.glob('seed_*') if (p / 'cells.json').exists())
    C = {s: json.loads((out / f'seed_{s}' / 'cells.json').read_text())['cells'] for s in seeds}
    R = {s: dict(np.load(out / f'seed_{s}' / 'regrets.npz')) for s in seeds}
    new = CORR[1:]; hO = start_hist('OLD'); tv = {k: float(0.5 * np.abs(start_hist(k) - hO).sum()) for k in new}
    D = {k: float(np.mean([R[s][f'Z_OLD|{k}'].mean() - R[s][f'Z_{k}|{k}'].mean() for s in seeds])) for k in new}
    DM = {k: float(np.mean([R[s][f'M_OLD|{k}'].mean() - R[s][f'M_{k}|{k}'].mean() for s in seeds]) ) for k in new}
    d = np.array([R[s]['Z_OLD|RANDOM'] - R[s]['Z_RANDOM|RANDOM'] for s in seeds]); ci = c0.boot(d)
    dm = {k: float(np.mean([C[s][f'density_monitor|{k}'] for s in seeds])) for k in CORR}; rm = {k: float(np.mean([C[s][f'range_monitor|{k}'] for s in seeds])) for k in CORR}
    pred = {'Q4-1 Delta(RANDOM) > 0 (Z*_FT exact on every corridor: panel self-check)': dict(mean=float(d.mean()), ci=ci, pass_=bool(ci[0] > 0)),
            'Q4-2 Spearman(corridor TV, Delta) >= 0.8': dict(value=c0.spearman([tv[k] for k in new], [D[k] for k in new]), tv=tv, delta=D,
                                                             pass_=bool(c0.spearman([tv[k] for k in new], [D[k] for k in new]) >= 0.8)),
            'Q4-3 range monitor fires 0 % (reported)': dict(range=rm, pass_=bool(max(rm.values()) == 0.0)),
            'Q4-3b Spearman(density monitor, Delta) (reported)': dict(value=c0.spearman([dm[k] for k in new], [D[k] for k in new]), density=dm, pass_=True)}
    dr = D['RANDOM']; pred['Q4-4 derived: staggered harm 2f(1-f)·Delta(RANDOM)'] = dict(f=[0, .25, .5, .75, 1], harm=[2 * f * (1 - f) * dr for f in (0, .25, .5, .75, 1)], pass_=True)
    L = [f'Q4 corridor (seeds {seeds}): Delta by corridor (Z_OLD minus specialist), corridor TV, monitors',
         'corridor | TV | Delta Z | Delta M | Z_OLD | spec Z | range mon | density mon | rule']
    for k in new:
        L.append(f'{k} | {tv[k]:.3f} | {D[k]:+.2f} | {DM[k]:+.2f} | {np.mean([C[s][f"Z_OLD|{k}"] for s in seeds]):.2f} | '
                 f'{np.mean([C[s][f"Z_{k}|{k}"] for s in seeds]):.2f} | {rm[k]:.3f} | {dm[k]:.3f} | {np.mean([C[s][f"rule|{k}"] for s in seeds]):.2f}')
    L.append(f'OLD | 0 | — | — | {np.mean([C[s]["Z_OLD|OLD"] for s in seeds]):.2f} | — | {rm["OLD"]:.3f} | {dm["OLD"]:.3f} | {np.mean([C[s]["rule|OLD"] for s in seeds]):.2f}')
    L += [f'{k}: {"SUPPORTED" if v["pass_"] else "NOT SUPPORTED"} {json.dumps({kk: vv for kk, vv in v.items() if kk != "pass_"})}' for k, v in pred.items()]
    txt = '\n'.join(L); print(txt, flush=True); (out / 'report.txt').write_text(txt + '\n')
    (out / 'result.json').write_text(json.dumps(dict(seeds=seeds, tv=tv, delta=D, deltaM=DM, predictions=pred), indent=1))


SRC = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()

if __name__ == '__main__':
    ap = argparse.ArgumentParser(); ap.add_argument('--out', required=True); ap.add_argument('--smoke', action='store_true')
    ap.add_argument('--panels', action='store_true'); ap.add_argument('--seed', type=int); ap.add_argument('--merge', action='store_true')
    a = ap.parse_args(); out = Path(a.out); out.mkdir(parents=True, exist_ok=True); torch.set_num_threads(1)
    if a.panels:
        run_panels(a, out, 60 if a.smoke else 3000)
    elif a.seed is not None:
        run_seed(a, out, (30, 2) if a.smoke else (3000, 8))
    elif a.merge:
        run_merge(a, out)
