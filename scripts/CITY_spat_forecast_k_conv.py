#!/usr/bin/env python3
"""Convention check for CITY_spat_forecast_k (exit 1 on failure): on recorded traces, every forecast branch is evaluated with the TRUE durations
(true remaining of the current green, true run lengths of intermediate greens) in place of the quantiles, so only the timing convention is
tested.  ttr (current green), ttg to the k-th green ahead from a green and from a non-green phase.  All errors must be 0.
Usage (spider): CITY_m4s_run.py scripts/CITY_spat_forecast_k_conv.py <npz files>"""
import sys
from collections import Counter
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_spat_forecast as FC  # noqa: E402
import scripts.CITY_spat_forecast_k as FK  # noqa: E402
class NoPlusOne(FK.ForecastK):
    """negative control: the +1 per setPhase-ended green removed (the C-71 / C-84 error); the check must FAIL with it."""
    def chain(self, tid, c, t0, serve, rem_fn=None, full_fn=None):
        gs = self.G[tid]; k = len(gs); t = t0 - (1.0 if t0 > 0 and abs(t0 - round(t0)) < 1e-9 and False else 0.0)
        for m in range(k):
            g = gs[(c + m) % k]
            if g in serve:
                return t + FK.OBS
            t += full_fn(tid, g) + self.NG[tid][(c + m) % k]
        return None


if __name__ == '__main__':
    neg = '--neg' in sys.argv; files = [a for a in sys.argv[1:] if a != '--neg']; T = FK.fit_k(files)
    F = (NoPlusOne if neg else FK.ForecastK)(T, 0.5); err = {}; n_lights = set()
    for f in files:
        z = np.load(f, allow_pickle=True); ids = [str(x) for x in z['ids']]; P, S = z['phases'], z['spent']
        for j, tid in enumerate(ids):
            if tid not in F.G:
                continue
            gs = F.G[tid]; runs = FC.runs(P[:, j]); n_lights.add(tid)
            for r_i, (ph, st, ln, complete) in enumerate(runs):
                if not complete:
                    continue
                for i in range(st, st + ln):
                    t = i + 1; s = float(S[i, j])
                    if ph in gs:
                        err.setdefault('ttr', Counter())[round((ln - s) + FK.OBS - ((st + ln + 1) - t), 6)] += 1
                    # true-duration functions: the current run's true remaining, each following green's true run length (in order)
                    seq = [rr for rr in runs[r_i + 1:] if rr[0] in gs]
                    for m, tgt in enumerate(seq[:len(gs) - (1 if ph in gs else 0)]):   # from a non-green: up to the green that just ended
                        if not tgt[3] or any(not x[3] for x in seq[:m]):
                            break
                        lens = {x[0]: x[2] for x in seq[:m]}                     # intermediate greens (distinct within one cycle)
                        rem_true = lambda tid_, g_, s_, ln=ln: ln - s_      # noqa: E731
                        full_true = lambda tid_, g_, lens=lens: lens.get(g_, np.nan)  # noqa: E731
                        fc = F.ttg(tid, ph, s, {tgt[0]}, rem_fn=rem_true, full_fn=full_true)
                        key = f'ttg_{"green" if ph in gs else "nongreen"}_ahead{m + 1}'
                        err.setdefault(key, Counter())[round(fc - ((tgt[1] + 1) - t), 6) if fc is not None and np.isfinite(fc) else 'nan'] += 1
    ok = True
    for k, c in sorted(err.items()):
        n = sum(c.values()); z0 = c.get(0.0, 0); good = z0 == n; ok &= good
        print(f'{k:22s} n {n:8d}: error 0 on {100 * z0 / n:6.2f} % {"" if good else c.most_common(4)}')
    print('lights', len(n_lights), 'files', len(files)); print('FORECAST-K CONVENTION:', 'PASS' if ok else 'FAIL'); sys.exit(0 if ok else 1)
