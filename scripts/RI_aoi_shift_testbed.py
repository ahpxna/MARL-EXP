#!/usr/bin/env python3
"""Remote-inference AoI-shift testbed (02/10/2026 12:0x EDT; PROTOCOL_RI_AOI_SHIFT_20261002.md) — the second domain of the
round-10 direction, in the model of Shisher & Sun (arXiv 2404.16281): a receiver predicts the CURRENT state of a remote
process from the latest delivered sample, whose age δ (AoI) is an input, plus its own noisy local sensor.

Process: noisy damped pendulum  θ'' = −sin θ − 0.1 θ' + 0.5 ξ,  step dt = 0.1 (10 Euler–Maruyama substeps).
Remote sample X_t = (sin θ_t, cos θ_t, θ'_t) + N(0, 0.05²);  local sensor L_t = (sin θ_t, cos θ_t) + N(0, 0.5²);
target Y_t = (sin θ_t, cos θ_t).  Receiver input at time t: [L_t, X_{t−δ}, δ / 10].
Predictor f: MLP 6 → 64 → 64 → 2 (tanh), Adam 1e-3, batch 512, 20 epochs, 200 000 training samples (MSE); the SILENT
predictor f0 (compiled silence's analogue): the same MLP on L_t only.  gain = 1 − MSE(f) / MSE(f0) on 100 000 test samples
from an independent trajectory.  AoI windows: δ ~ U{a, …, a + 3}.  Training windows: fast a = 0, slow a = 4, and mix
δ ~ U{0, …, 11}.  Deployment windows a = 0 … 8.  Also, for the slow-trained predictor at a = 0 … 3: EMULATION (the receiver
uses a buffered older sample with δ' ~ U{4..7}, the exposure it was trained on) and LABEL REMAP (the true sample X_{t−δ}
with the label δ' = δ + 4 − a, i.e. the monotone map of the deployment window onto the training window).
Usage: RI_aoi_shift_testbed.py --seeds 0 1 2 3 4 --out <dir>   (--smoke: tiny sizes, prints losses only)"""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
from torch import nn


def trajectory(n, rng):
    th, om = rng.uniform(-np.pi, np.pi), 0.0; out = np.empty((n, 2)); h = 0.01
    for t in range(n):
        for _ in range(10):
            om += h * (-np.sin(th) - 0.1 * om) + 0.5 * np.sqrt(h) * rng.standard_normal(); th += h * om
        out[t] = th, om
    return out


def features(tr, rng):
    X = np.stack([np.sin(tr[:, 0]), np.cos(tr[:, 0]), tr[:, 1]], 1) + 0.05 * rng.standard_normal((len(tr), 3))
    L = np.stack([np.sin(tr[:, 0]), np.cos(tr[:, 0])], 1) + 0.5 * rng.standard_normal((len(tr), 2))
    Y = np.stack([np.sin(tr[:, 0]), np.cos(tr[:, 0])], 1)
    return X.astype(np.float32), L.astype(np.float32), Y.astype(np.float32)


def batch(X, L, Y, idx, d_true, d_label):
    return np.concatenate([L[idx], X[idx - d_true], (d_label / 10.0)[:, None]], 1).astype(np.float32), Y[idx]


def mlp(k):
    return nn.Sequential(nn.Linear(k, 64), nn.Tanh(), nn.Linear(64, 64), nn.Tanh(), nn.Linear(64, 2))


def fit(inp, out, seed, epochs, bs=512):
    torch.manual_seed(seed); net = mlp(inp.shape[1]); opt = torch.optim.Adam(net.parameters(), 1e-3); lf = nn.MSELoss()
    x = torch.as_tensor(inp); y = torch.as_tensor(out); g = torch.Generator().manual_seed(seed)
    for ep in range(epochs):
        perm = torch.randperm(len(x), generator=g); tot = 0.0
        for i in range(0, len(x), bs):
            b = perm[i:i + bs]; loss = lf(net(x[b]), y[b]); opt.zero_grad(); loss.backward(); opt.step(); tot += loss.item() * len(b)
    return net, tot / len(x)


def mse(net, inp, out):
    with torch.no_grad():
        return float(((net(torch.as_tensor(inp)) - torch.as_tensor(out)) ** 2).sum(1).mean())


def window(rng, n, a, w=4):
    return rng.integers(a, a + w, n)


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke)
    torch.set_num_threads(1); src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    NTR, NTE, EP = (4000, 2000, 2) if a.smoke else (200_000, 100_000, 20)
    res = dict(source_sha256=src, n_train=NTR, n_test=NTE, epochs=EP, seeds={}); t0 = time.perf_counter()
    for s in a.seeds:
        rng = np.random.default_rng(1000 + s); trn = features(trajectory(NTR + 20, rng), rng)
        rng2 = np.random.default_rng(5000 + s); tst = features(trajectory(NTE + 20, rng2), rng2)
        i_tr = np.arange(16, NTR + 16); i_te = np.arange(16, NTE + 16); rs = np.random.default_rng(9000 + s)
        f0, l0 = fit(trn[1][i_tr], trn[2][i_tr], s, EP); m0 = mse(f0, tst[1][i_te], tst[2][i_te])
        nets = {}
        for name, dd in (('fast', window(rs, NTR, 0)), ('slow', window(rs, NTR, 4)), ('mix', rs.integers(0, 12, NTR))):
            nets[name], loss = fit(*batch(*trn, i_tr, dd, dd.astype(np.float32)), s, EP)
            print(f'[{time.perf_counter() - t0:.0f}s] seed {s} {name} train loss {loss:.4f}', flush=True)
        R = dict(silent_mse=m0, gain={}, emulation={}, remap={})
        if not a.smoke:
            for name, net in nets.items():
                R['gain'][name] = {}
                for aw in range(9):
                    dd = window(rs, NTE, aw); R['gain'][name][aw] = 1 - mse(net, *batch(*tst, i_te, dd, dd.astype(np.float32))) / m0
            for aw in range(4):
                dd = window(rs, NTE, aw); de = window(rs, NTE, 4)
                R['emulation'][aw] = 1 - mse(nets['slow'], *batch(*tst, i_te, de, de.astype(np.float32))) / m0
                R['remap'][aw] = 1 - mse(nets['slow'], *batch(*tst, i_te, dd, (dd + 4 - aw).astype(np.float32))) / m0
        res['seeds'][s] = R
        print(f'[{time.perf_counter() - t0:.0f}s] seed {s} done (silent MSE {m0:.4f})', flush=True)
    if a.smoke:
        print('SMOKE OK (sizes tiny; no gains computed)'); return
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != src:
        raise RuntimeError('source changed during run')
    (out / 'results.json').write_text(json.dumps(res, indent=1)); (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_sha256=src, seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2, 3, 4]); p.add_argument('--out', required=True)
    p.add_argument('--smoke', action='store_true'); main(p.parse_args())
