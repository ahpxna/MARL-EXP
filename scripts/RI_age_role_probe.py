#!/usr/bin/env python3
"""AGE-ROLE PROBE on the testbed (02/10/2026 12:2x; PROTOCOL_AGE_ROLE_PROBE_20261002.md).  Re-trains, bit-identically, the
slow-trained predictor and the silent predictor of scripts/RI_age_role_testbed.py (same functions, seeds and data path) and
computes the reliability share ρ = Σ <Δ, d>² / |d|² / Σ |Δ|² on the TRAINING inputs, d = f − f_silent, Δ = f(label + 1) − f.
SELF-CHECK: the re-trained net's training loss equals the testbed's results.json train_loss (when that file exists).
Usage: RI_age_role_probe.py --out <file.json>"""
import argparse, json, sys
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.RI_age_role_testbed import source, inp, fit


def rho(net, f0, X, L, Y, idx, d):
    x, _ = inp(X, L, Y, idx, d, d); x1, _ = inp(X, L, Y, idx, d, d + 1)
    with torch.no_grad():
        f = net(torch.as_tensor(x)).numpy(); f1 = net(torch.as_tensor(x1)).numpy(); s = f0(torch.as_tensor(L[idx])).numpy()
    D = f - s; Dl = f1 - f; nd = (D ** 2).sum(1); ok = nd > 1e-6
    return float(((Dl[ok] * D[ok]).sum(1) ** 2 / nd[ok]).sum() / (Dl[ok] ** 2).sum())


def main(a):
    torch.set_num_threads(1); NTR, EP = 200_000, 20; out = {}; ref = None
    rf = ROOT / 'research/marl_budget/ri_age_role_20261002/results.json'
    if rf.exists():
        ref = json.loads(rf.read_text())
    for lam in (0.0, 0.1, 0.2, 0.4):
        out[str(lam)] = {}
        for s in range(5):
            rng = np.random.default_rng(100 * s + 1); tr = source(NTR + 20, lam, rng); it = np.arange(16, NTR + 16)
            rs = np.random.default_rng(100 * s + 3)
            f0, _ = fit(tr[1][it], tr[2][it], s, EP)
            dd = rs.integers(4, 8, NTR); net, loss = fit(*inp(*tr, it, dd, dd), s, EP)
            chk = None if ref is None else abs(ref['res'][str(lam)][str(s)]['train_loss'] - loss) < 1e-9
            if chk is False:
                raise SystemExit(f'SELF-CHECK FAIL: λ {lam} seed {s} train loss {loss} != testbed {ref["res"][str(lam)][str(s)]["train_loss"]}')
            out[str(lam)][s] = dict(rho=rho(net, f0, *tr, it, dd), train_loss=loss, identical_to_testbed=chk)
            print(f'λ {lam} seed {s} ρ {out[str(lam)][s]["rho"]:.4f} (identical: {chk})', flush=True)
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('ρ by λ (mean over seeds): ' + ', '.join(f'{l} {np.mean([v["rho"] for v in out[l].values()]):.3f}' for l in out), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--out', required=True); main(p.parse_args())
