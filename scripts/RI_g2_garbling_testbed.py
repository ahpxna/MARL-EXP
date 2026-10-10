#!/usr/bin/env python3
"""E5-G2 (03/10/2026 23:5x EDT; PROTOCOL_E3_WAVE_ALL_PENDING_20261003 E5 / DECISION_FORKS G2): in the RI age-role testbed
(scripts/RI_age_role_testbed.py, imported, not edited), add two receiver-side adapters for the UPGRADE deployments (delta ~ U{a..a+3},
a = 0..3) of the receiver trained on delta ~ U{4..7}:
  KERNEL      : the known-parameter Blackwell garbling of the fresh sample into an older-looking one.  Draw d_old ~ U{4..7},
                Delta = max(0, d_old - delta); X~ = B(Delta) X_{t-delta} + noise, B = 0.98^Delta R(-lambda Delta),
                noise ~ N(0, (p + 0.0025)(1 - 0.98^(2 Delta)) I), p = 0.09 / (1 - 0.98^2); the age label shown is delta + Delta.
  KERNEL_MEAN : the same transform without the noise (a deterministic map; NOT a garbling of the same law).
plus the Bayes floor (exact, linear-Gaussian posterior of z_t given L_t and X_{t-delta}) at the training and deployed ages.
SELF-CHECKS: the testbed's plain / remap / emu_full / emu_min gains are reproduced exactly from the same seeds and random streams
(the new arms draw from a separate generator); the Bayes MSE at delta ~ U{4..7} and U{0..3} equals the published 0.619 / 0.223 (3 d.p.).
PREDICTIONS (registered before the run): G2a at lambda in {0.2, 0.4}, MSE(KERNEL) < MSE(plain) for every a in 0..3 on 5 / 5 seeds;
G2b |MSE(KERNEL) - MSE(emu_full)| <= 5 % of MSE(emu_full) at every lambda, a (mean over seeds); G2c at lambda in {0.2, 0.4} MSE(KERNEL_MEAN)
> MSE(KERNEL) for every a (mean over seeds).  G1: the report adds the Bayes line and the intrinsic / excess split for every arm."""
from __future__ import annotations
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.RI_age_role_testbed import source, inp, fit, mse

P = 0.09 / (1 - 0.98 ** 2)


def rot(th):
    return np.array([[np.cos(th), -np.sin(th)], [np.sin(th), np.cos(th)]])


def bayes_mse(delta, lam):
    A = (0.98 ** delta) * rot(lam * delta); I = np.eye(2)
    S = np.block([[(P + 1) * I, P * A], [P * A.T, (P + 0.0025) * I]]); C = np.hstack([P * I, P * A])
    return float(np.trace(P * I - C @ np.linalg.solve(S, C.T)))


def kernel(X, delta, lam, rng, noise=True):
    d_old = rng.integers(4, 8, len(delta)); D = np.maximum(0, d_old - delta); out = np.empty_like(X)
    for k in np.unique(D):
        sel = D == k; B = (0.98 ** k) * rot(-lam * k); out[sel] = X[sel] @ B.T
        if noise and k > 0:
            out[sel] += rng.standard_normal((sel.sum(), 2)) * np.sqrt((P + 0.0025) * (1 - 0.98 ** (2 * k)))
    return out.astype(np.float32), delta + D


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=False); torch.set_num_threads(1)
    src = {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in ('scripts/RI_g2_garbling_testbed.py', 'scripts/RI_age_role_testbed.py')}
    ref = json.loads((ROOT / 'research/marl_budget/ri_age_role_20261002/results.json').read_text())
    b_tr = np.mean([bayes_mse(d, 0.0) for d in range(4, 8)]); b_up = np.mean([bayes_mse(d, 0.0) for d in range(0, 4)])
    if (round(b_tr, 3), round(b_up, 3)) != (0.619, 0.223):
        raise SystemExit(f'SELF-CHECK FAIL: Bayes MSE {b_tr:.4f} / {b_up:.4f} != 0.619 / 0.223')
    NTR, NTE, EP = 200_000, 100_000, 20; res = dict(source_sha256=src, bayes_check=[b_tr, b_up], res={}); t0 = time.perf_counter(); npar = 0
    for lam in a.lams:
        res['res'][str(lam)] = {}
        for s in a.seeds:
            rng = np.random.default_rng(100 * s + 1); tr = source(NTR + 20, lam, rng)
            rng2 = np.random.default_rng(100 * s + 2); te = source(NTE + 20, lam, rng2)
            it = np.arange(16, NTR + 16); ie = np.arange(16, NTE + 16); rs = np.random.default_rng(100 * s + 3); rk = np.random.default_rng(100 * s + 7)
            f0, _ = fit(tr[1][it], tr[2][it], s, EP); m0 = mse(f0, te[1][ie], te[2][ie])
            dd = rs.integers(4, 8, NTR); net, loss = fit(*inp(*tr, it, dd, dd), s, EP)
            R = dict(silent=m0, bayes_train=float(np.mean([bayes_mse(d, lam) for d in range(4, 8)])), arms={})
            for aw in range(9):
                d = rs.integers(aw, aw + 4, NTE); g = {'plain': 1 - mse(net, *inp(*te, ie, d, d)) / m0}
                if aw < 4:
                    g['remap'] = 1 - mse(net, *inp(*te, ie, d, d + 4 - aw)) / m0
                    de = rs.integers(4, 8, NTE); g['emu_full'] = 1 - mse(net, *inp(*te, ie, de, de)) / m0
                    dm = np.maximum(d, 4); g['emu_min'] = 1 - mse(net, *inp(*te, ie, dm, dm)) / m0
                    for nm, nz in (('kernel', True), ('kernel_mean', False)):
                        Xk, lab = kernel(te[0][ie - d], d, lam, rk, nz)
                        x = np.concatenate([te[1][ie], Xk, (lab.astype(np.float32) / 10.0)[:, None]], 1).astype(np.float32)
                        g[nm] = 1 - mse(net, x, te[2][ie]) / m0
                    st = ref['res'][str(lam)][str(s)]
                    for k in ('plain', 'remap', 'emu_full', 'emu_min'):
                        if abs(st[k][str(aw)] - g[k]) > 1e-9:
                            raise SystemExit(f'SELF-CHECK FAIL: {k} lambda {lam} seed {s} a {aw}: {g[k]} != stored {st[k][str(aw)]}')
                        npar += 1
                bd = float(np.mean([bayes_mse(x, lam) for x in range(aw, aw + 4)]))
                R['arms'][aw] = dict(gain=g, mse={k: (1 - v) * m0 for k, v in g.items()}, bayes=bd, excess={k: (1 - v) * m0 - bd for k, v in g.items()})
            res['res'][str(lam)][s] = R
            print(f'[{time.perf_counter() - t0:.0f}s] lambda {lam} seed {s}: ' + ', '.join(f"a{aw} " + ' '.join(f"{k} {v:.3f}" for k, v in R['arms'][aw]['mse'].items()) for aw in range(4)), flush=True)
    if src != {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in src}:
        raise RuntimeError('source changed during run')
    res['parity_checked'] = npar; (out / 'results.json').write_text(json.dumps(res, indent=1))
    # predictions
    L = res['res']; lines = []
    g2a = all(L[str(l)][s]['arms'][aw]['mse']['kernel'] < L[str(l)][s]['arms'][aw]['mse']['plain'] for l in (0.2, 0.4) if str(l) in L for s in L[str(l)] for aw in range(4))
    m = lambda l, aw, k: np.mean([L[str(l)][s]['arms'][aw]['mse'][k] for s in L[str(l)]])
    g2b = all(abs(m(l, aw, 'kernel') - m(l, aw, 'emu_full')) <= 0.05 * m(l, aw, 'emu_full') for l in a.lams for aw in range(4))
    g2c = all(m(l, aw, 'kernel_mean') > m(l, aw, 'kernel') for l in (0.2, 0.4) if l in a.lams for aw in range(4))
    for l in a.lams:
        for aw in range(4):
            lines.append(f"lambda {l} a {aw}: Bayes {np.mean([L[str(l)][s]['arms'][aw]['bayes'] for s in L[str(l)]]):.3f} | MSE " +
                         ', '.join(f"{k} {m(l, aw, k):.3f}" for k in ('plain', 'remap', 'emu_full', 'emu_min', 'kernel', 'kernel_mean')))
    lines += [f"G2a KERNEL < plain at lambda 0.2 / 0.4, every a, every seed -> {'SUPPORTED' if g2a else 'NOT SUPPORTED'}",
              f"G2b KERNEL within 5 % of actual emulation everywhere -> {'SUPPORTED' if g2b else 'NOT SUPPORTED'}",
              f"G2c KERNEL_MEAN worse than KERNEL at lambda 0.2 / 0.4 -> {'SUPPORTED' if g2c else 'NOT SUPPORTED'}"]
    (out / 'report.txt').write_text('\n'.join(lines) + '\n'); print('\n'.join(lines))
    (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', self_check='PASS', parity_checked=npar, args=vars(a), source_sha256=src, seconds=time.perf_counter() - t0), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument('--lams', type=float, nargs='+', default=[0.0, 0.1, 0.2, 0.4]); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2, 3, 4])
    p.add_argument('--out', required=True); main(p.parse_args())
