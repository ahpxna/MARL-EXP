#!/usr/bin/env python3
"""AGE-ROLE testbed (02/10/2026 12:2x EDT; PROTOCOL_RI_AGE_ROLE_20261002.md): does the age label act as a RELIABILITY cue or as
a PROPAGATION horizon, and does that decide which repair of an upgrade works?  Same receiver as RI_aoi_shift_testbed.py,
with a source whose deterministic drift is a parameter λ:
  z_{t+1} = 0.98 R(λ) z_t + 0.3 ε_t   (R(λ) = rotation by λ rad per step; λ = 0: no drift, age is ~ only a reliability cue)
remote sample X_t = z_t + N(0, 0.05²), local sensor L_t = z_t + N(0, 1), target z_t; input [L_t, X_{t−δ}, δ/10]; MLP 5–64–64–2
tanh, Adam 1e-3, batch 512, 20 epochs, 200 000 training / 100 000 test samples; silent predictor on L only; gain =
1 − MSE/MSE(silent).  Trained on δ ~ U{4..7} ("slow"); deployed at δ ~ U{a..a+3}, a = 0..8.  For a = 0..3 (upgrades):
plain; LABEL REMAP (true X_{t−δ}, label δ + 4 − a); FULL EMULATION (buffered X_{t−δ'}, δ' ~ U{4..7}); MINIMAL EMULATION
(buffered X_{t−δ'}, δ' = max(δ, 4): the freshest in-support exposure).  λ ∈ {0, 0.1, 0.2, 0.4}; seeds 0–4.
Usage: RI_age_role_testbed.py --out <dir> [--smoke]"""
from __future__ import annotations
import argparse, hashlib, json, time
from pathlib import Path
import numpy as np
import torch
from torch import nn


def source(n, lam, rng):
    c, s = np.cos(lam), np.sin(lam); A = 0.98 * np.array([[c, -s], [s, c]]); z = np.zeros((n, 2)); x = rng.standard_normal(2)
    for t in range(n):
        x = A @ x + 0.3 * rng.standard_normal(2); z[t] = x
    X = (z + 0.05 * rng.standard_normal(z.shape)).astype(np.float32); L = (z + rng.standard_normal(z.shape)).astype(np.float32)
    return X, L, z.astype(np.float32)


def inp(X, L, Y, idx, d_true, d_label):
    return np.concatenate([L[idx], X[idx - d_true], (np.asarray(d_label, np.float32) / 10.0)[:, None]], 1).astype(np.float32), Y[idx]


def fit(x, y, seed, epochs, bs=512):
    torch.manual_seed(seed)
    net = nn.Sequential(nn.Linear(x.shape[1], 64), nn.Tanh(), nn.Linear(64, 64), nn.Tanh(), nn.Linear(64, 2))
    opt = torch.optim.Adam(net.parameters(), 1e-3); lf = nn.MSELoss(); X = torch.as_tensor(x); Y = torch.as_tensor(y)
    g = torch.Generator().manual_seed(seed); tot = 0.0
    for _ in range(epochs):
        perm = torch.randperm(len(X), generator=g); tot = 0.0
        for i in range(0, len(X), bs):
            b = perm[i:i + bs]; loss = lf(net(X[b]), Y[b]); opt.zero_grad(); loss.backward(); opt.step(); tot += loss.item() * len(b)
    return net, tot / len(X)


def mse(net, x, y):
    with torch.no_grad():
        return float(((net(torch.as_tensor(x)) - torch.as_tensor(y)) ** 2).sum(1).mean())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke); torch.set_num_threads(1)
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    NTR, NTE, EP = (4000, 2000, 2) if a.smoke else (200_000, 100_000, 20)
    res = dict(source_sha256=src, lams=a.lams, res={}); t0 = time.perf_counter()
    for lam in a.lams:
        res['res'][str(lam)] = {}
        for s in a.seeds:
            rng = np.random.default_rng(100 * s + 1); tr = source(NTR + 20, lam, rng)
            rng2 = np.random.default_rng(100 * s + 2); te = source(NTE + 20, lam, rng2)
            it = np.arange(16, NTR + 16); ie = np.arange(16, NTE + 16); rs = np.random.default_rng(100 * s + 3)
            f0, _ = fit(tr[1][it], tr[2][it], s, EP); m0 = mse(f0, te[1][ie], te[2][ie])
            dd = rs.integers(4, 8, NTR); net, loss = fit(*inp(*tr, it, dd, dd), s, EP)
            R = dict(silent=m0, train_loss=loss, plain={}, remap={}, emu_full={}, emu_min={})
            if not a.smoke:
                for aw in range(9):
                    d = rs.integers(aw, aw + 4, NTE); R['plain'][aw] = 1 - mse(net, *inp(*te, ie, d, d)) / m0
                    if aw < 4:
                        R['remap'][aw] = 1 - mse(net, *inp(*te, ie, d, d + 4 - aw)) / m0
                        de = rs.integers(4, 8, NTE); R['emu_full'][aw] = 1 - mse(net, *inp(*te, ie, de, de)) / m0
                        dm = np.maximum(d, 4); R['emu_min'][aw] = 1 - mse(net, *inp(*te, ie, dm, dm)) / m0
            res['res'][str(lam)][s] = R
            print(f'[{time.perf_counter() - t0:.0f}s] λ {lam} seed {s} train loss {loss:.4f} silent {m0:.4f}', flush=True)
    if a.smoke:
        print('SMOKE OK (tiny sizes; no gains computed)'); return
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != src:
        raise RuntimeError('source changed during run')
    (out / 'results.json').write_text(json.dumps(res, indent=1))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', args=vars(a), source_sha256=src, seconds=time.perf_counter() - t0), indent=1))
    print('COMPLETE', out, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--lams', type=float, nargs='+', default=[0.0, 0.1, 0.2, 0.4]); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2, 3, 4])
    p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
