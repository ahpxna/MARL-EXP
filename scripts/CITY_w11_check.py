#!/usr/bin/env python3
"""KF11-1 (PROTOCOL_CITY_WAVE11_FORL_20261005): answers served during a yellow whose next green serves the link must equal the realized time to
green on the run's phase trace (offset c = 0, as for every provider, W10-2).  Also reports the MAE of the forecast branch (descriptive).
Usage: CITY_w11_check.py <served npz> <record npz>"""
import sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w10_diag as DG  # noqa: E402
if __name__ == '__main__':
    q = np.load(sys.argv[1], allow_pickle=True); r = np.load(sys.argv[2], allow_pickle=True); ST = DG.states(DG.NETS['g4'])
    P = r['phases']; rid = {t: i for i, t in enumerate(r['ids'])}; ids = list(q['ids'])
    greens = {tid: [k for k, s in enumerate(ST[tid]) if 'G' in s or 'g' in s and 'y' not in s] for tid in ST}
    yel, fcb = [], []
    for t, j, link, ttg, ttr, v in zip(q['t'], q['j'], q['link'], q['ttg'], q['ttr'], q['valid']):
        if not v:
            continue
        tid = ids[j]; i = int(round(t)) - 1
        if i < 0 or i >= len(P):
            continue
        ph = P[i, rid[tid]]; st = ST[tid]; on = lambda k: st[P[k, rid[tid]]][link] in 'Gg'  # noqa: E731
        if on(i):
            k = next((k for k in range(i + 1, len(P)) if not on(k)), None)
            if k is not None and ttr < 900:
                fcb.append(ttr - (k - i))
            continue
        k = next((k for k in range(i, len(P)) if on(k)), None)
        if k is None:
            continue
        (yel if 'y' in st[ph] else fcb).append(ttg - (k - i))
    yel, fcb = np.array(yel), np.array(fcb)
    ok = len(yel) > 0 and bool(np.all(np.abs(yel) < 1e-6))
    print(f'KF11-1 yellow-branch answers exact: {ok} (n {len(yel)}, max |err| {np.abs(yel).max() if len(yel) else float("nan"):.3f}); '
          f'forecast-branch MAE {np.abs(fcb).mean() if len(fcb) else float("nan"):.2f} s (n {len(fcb)})')
    sys.exit(0 if ok else 1)
