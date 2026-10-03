#!/usr/bin/env python3
"""SUPPORT vs DISTANCE (02/10/2026 13:2x; PROTOCOL_RI_SUPPORT_VS_DISTANCE_20261002.md).  The remote-inference testbed of
scripts/RI_aoi_shift_testbed.py (same process, sensors, predictor, training recipe — its functions are imported unchanged),
deployment AoI δ ~ U{0..3}.  Four receivers trained on different AoI distributions, three of them at the SAME W1 = 4 from the
deployment distribution:
  A  U{4..7}                       W1 4, support disjoint from the deployment ages
  B  ½ U{0..3} + ½ U{8..11}        W1 4, support covers the deployment ages
  C  U{0..11}                      W1 4, support covers the deployment ages
  D  U{0..3}                       W1 0 (matched)
gain = 1 − MSE / MSE(silent local-only predictor) on the deployment distribution; seeds 0–4.
Usage: RI_support_vs_distance.py --out <dir> [--smoke]"""
import argparse, hashlib, json, sys, time
from pathlib import Path
import numpy as np
import torch
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.RI_aoi_shift_testbed import trajectory, features, batch, fit, mse


def draw(name, rng, n):
    if name == 'A':
        return rng.integers(4, 8, n)
    if name == 'B':
        return np.where(rng.random(n) < 0.5, rng.integers(0, 4, n), rng.integers(8, 12, n))
    if name == 'C':
        return rng.integers(0, 12, n)
    return rng.integers(0, 4, n)


def w1(d1, d2):
    h1 = np.bincount(d1, minlength=16) / len(d1); h2 = np.bincount(d2, minlength=16) / len(d2)
    return float(np.abs(np.cumsum(h1) - np.cumsum(h2)).sum())


def main(a):
    out = Path(a.out); out.mkdir(parents=True, exist_ok=a.smoke); torch.set_num_threads(1)
    src = hashlib.sha256(Path(__file__).read_bytes()).hexdigest(); NTR, NTE, EP = (4000, 2000, 2) if a.smoke else (200_000, 100_000, 20)
    res = dict(source_sha256=src, seeds={}); t0 = time.perf_counter()
    for s in a.seeds:
        rng = np.random.default_rng(1000 + s); trn = features(trajectory(NTR + 20, rng), rng)
        rng2 = np.random.default_rng(5000 + s); tst = features(trajectory(NTE + 20, rng2), rng2)
        it = np.arange(16, NTR + 16); ie = np.arange(16, NTE + 16); rs = np.random.default_rng(7000 + s)
        f0, _ = fit(trn[1][it], trn[2][it], s, EP); m0 = mse(f0, tst[1][ie], tst[2][ie])
        dep = rs.integers(0, 4, NTE); R = dict(silent=m0, gain={}, w1={})
        for name in 'ABCD':
            dd = draw(name, rs, NTR); net, loss = fit(*batch(*trn, it, dd, dd.astype(np.float32)), s, EP)
            R['w1'][name] = w1(dep, dd)
            if not a.smoke:
                R['gain'][name] = 1 - mse(net, *batch(*tst, ie, dep, dep.astype(np.float32))) / m0
            print(f'[{time.perf_counter() - t0:.0f}s] seed {s} {name} loss {loss:.4f} W1 {R["w1"][name]:.2f}', flush=True)
        res['seeds'][s] = R
    if a.smoke:
        print('SMOKE OK (no gains computed)'); return
    if hashlib.sha256(Path(__file__).read_bytes()).hexdigest() != src:
        raise RuntimeError('source changed during run')
    (out / 'results.json').write_text(json.dumps(res, indent=1)); (out / 'manifest.json').write_text(json.dumps(dict(status='COMPLETE', source_sha256=src, seconds=time.perf_counter() - t0), indent=1))
    g = {n: np.mean([res['seeds'][s]['gain'][n] for s in res['seeds']]) for n in 'ABCD'}
    print('mean gain', {n: round(v, 4) for n, v in g.items()}, flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--seeds', type=int, nargs='+', default=[0, 1, 2, 3, 4]); p.add_argument('--out', required=True)
    p.add_argument('--smoke', action='store_true'); main(p.parse_args())
