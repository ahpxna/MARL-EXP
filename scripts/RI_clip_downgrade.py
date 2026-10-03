#!/usr/bin/env python3
"""CLIP on a DOWNGRADE in the second domain (02/10/2026 15:1x; PROTOCOL_RI_CLIP_DOWNGRADE_20261002.md).  The age-role testbed
(scripts/RI_age_role_testbed.py: z_{t+1} = 0.98 R(λ) z + noise, remote X, local L, MLP on [L, X_{t−δ}, δ/10]; functions
imported unchanged).  A FAST receiver is trained on δ ~ U{0..3} and deployed on staler windows δ ~ U{a..a+3}, a = 4..8 (ages
it never saw).  PLAIN: the true label δ.  CLIP: the label min(δ, 3) — the out-of-range age moved to the edge of the training
range, content unchanged (the 3×3 MARL clip's analogue).  λ ∈ {0, 0.1, 0.2, 0.4}; seeds 0–4; gain = 1 − MSE/MSE(silent).
Usage: RI_clip_downgrade.py --out <dir> [--smoke]"""
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.RI_age_role_testbed import source, inp, fit, mse


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke); torch.set_num_threads(1)
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); NTR, NTE, EP = (4000, 2000, 2) if a.smoke else (200_000, 100_000, 20)
    res = dict(source_sha256=src, res={}); t0 = time.perf_counter()
    for lam in a.lams:
        res['res'][str(lam)] = {}
        for s in a.seeds:
            rng = np.random.default_rng(100 * s + 11); tr = source(NTR + 20, lam, rng)
            rng2 = np.random.default_rng(100 * s + 12); te = source(NTE + 20, lam, rng2)
            it = np.arange(16, NTR + 16); ie = np.arange(16, NTE + 16); rs = np.random.default_rng(100 * s + 13)
            f0, _ = fit(tr[1][it], tr[2][it], s, EP); m0 = mse(f0, te[1][ie], te[2][ie])
            dd = rs.integers(0, 4, NTR); net, loss = fit(*inp(*tr, it, dd, dd), s, EP)
            R = dict(silent=m0, train_loss=loss, plain={}, clip={})
            if not a.smoke:
                for aw in range(0, 9):
                    d = rs.integers(aw, aw + 4, NTE)
                    R['plain'][aw] = 1 - mse(net, *inp(*te, ie, d, d)) / m0
                    R['clip'][aw] = 1 - mse(net, *inp(*te, ie, d, np.minimum(d, 3))) / m0
            res['res'][str(lam)][s] = R
            print(f'[{time.perf_counter() - t0:.0f}s] λ {lam} seed {s} loss {loss:.4f}', flush=True)
    if a.smoke:
        print('SMOKE OK (no gains computed)'); return
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != src:
        raise RuntimeError('source changed during run')
    (out / 'results.json').write_text(json.dumps(res, indent=1)); (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=src, seconds=time.perf_counter() - t0), indent=1))
    for lam in res['res']:
        S = res['res'][lam]
        pl = [np.mean([S[s]['plain'][a_] for s in S]) for a_ in range(9)]; cl = [np.mean([S[s]['clip'][a_] for s in S]) for a_ in range(9)]
        print(f'λ {lam}: plain a4..8 ' + ' '.join(f'{v:+.3f}' for v in pl[4:]) + ' | clip ' + ' '.join(f'{v:+.3f}' for v in cl[4:]) + f' | a0 {pl[0]:+.3f}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--lams', type=float, nargs='+', default=[0.0, 0.1, 0.2, 0.4])
    p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2, 3, 4]); p.add_argument('--out', required=True); p.add_argument('--smoke', action='store_true')
    main(p.parse_args())
