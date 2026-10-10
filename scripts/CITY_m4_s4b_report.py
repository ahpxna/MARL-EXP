#!/usr/bin/env python3
"""M4 stage 4b report (Amendment M4-A7; written before any 4b panel run).  spider/s4b/eval, fresh 1020-1039, lights sp11 / sp111, F1k fleets
213 / 313 (trained under sp11), 413 / 513 (under sp111), crossed [light 2, fleet 4, traffic 20].  R_<k> = RLK + no SPaT + rule (== σ*);
RULE_<k> = zero residual + forecast-K q; F1k_s<f>_on_<k>.  GATE (= F1 §3): agent fuel upper < 0, city / agent / human TL upper < +0.5,
teleports <= R + 0.1, unfinished <= R.  Reported: RULE vs R, F1k vs RULE, own- vs cross-light cells."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
from scripts.CITY_f1a1_report import KEYS, line  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/m4_20261004/spider/s4b/eval'; S = list(range(1020, 1040)); LT = (11, 111); FL = ((213, 11), (313, 11), (413, 111), (513, 111))
if __name__ == '__main__':
    if '--dir' in sys.argv:
        D = Path(sys.argv[sys.argv.index('--dir') + 1]); S = [int(x) for x in sys.argv[sys.argv.index('--seeds') + 1:]]
    Rt = rows(D); need = [f'R_{l}' for l in LT] + [f'RULE_{l}' for l in LT] + [f'F1k_s{f}_on_{l}' for f, _ in FL for l in LT]
    bad = [t for t in need if t not in Rt or sorted(Rt[t]) != S]
    if bad:
        sys.exit(f'INCOMPLETE {bad}')
    cub = lambda A, B, k, p: np.array([[[100 * (Rt[A(l, f)][s][k] / Rt[B(l)][s][k] - 1) if p else Rt[A(l, f)][s][k] - Rt[B(l)][s][k] for s in S] for f, _ in FL] for l in LT])
    F = {k: cub(lambda l, f: f'F1k_s{f}_on_{l}', lambda l: f'R_{l}', k, p) for k, p in KEYS}; dr = R.draws((len(LT), len(FL), len(S)))
    tel = np.mean([Rt[f'F1k_s{f}_on_{l}'][s]['teleports'] for f, _ in FL for l in LT for s in S]); tel0 = np.mean([Rt[f'R_{l}'][s]['teleports'] for l in LT for s in S])
    unf = np.mean([Rt[f'F1k_s{f}_on_{l}'][s]['unfinished'] for f, _ in FL for l in LT for s in S]); unf0 = np.mean([Rt[f'R_{l}'][s]['unfinished'] for l in LT for s in S])
    out = [f'== M4 stage 4b (spider {S[0]}-{S[-1]}): F1k (fleet retrained under RLK, forecast-K q 0.1) x 2 lights, crossed; vs R (no SPaT, rule = σ*)']
    res, ln = line('F1k vs R', F, dr, f' | tele {tel:.2f} ({tel0:.2f}) unf/run {unf:.2f} ({unf0:.2f})'); out.append(ln)
    ok = res['fuel_agent'][2] < 0 and all(res[k][2] < 0.5 for k in ('timeloss', 'timeloss_agent', 'timeloss_human')) and tel <= tel0 + 0.1 and unf <= unf0
    RU = {k: np.array([[[100 * (Rt[f'RULE_{l}'][s][k] / Rt[f'R_{l}'][s][k] - 1) if p else Rt[f'RULE_{l}'][s][k] - Rt[f'R_{l}'][s][k] for s in S]] for l in LT]) for k, p in KEYS}
    out.append(line('RULE + forecast-K vs R [reported]', RU, R.draws((len(LT), 1, len(S))))[1])
    FR = {k: np.array([[[100 * (Rt[f'F1k_s{f}_on_{l}'][s][k] / Rt[f'RULE_{l}'][s][k] - 1) if p else Rt[f'F1k_s{f}_on_{l}'][s][k] - Rt[f'RULE_{l}'][s][k] for s in S] for f, _ in FL] for l in LT]) for k, p in KEYS}
    out.append(line('F1k vs RULE [reported]', FR, dr)[1])
    for nm, own in (('own-light cells', True), ('cross-light cells', False)):
        cells = [(li, fi) for li, l in enumerate(LT) for fi, (_, t) in enumerate(FL) if (l == t) == own]
        out.append(f'  {nm} (n {len(cells)}) [point]: agent fuel % {np.mean([F["fuel_agent"][c].mean() for c in cells]):+.2f} | agent TL {np.mean([F["timeloss_agent"][c].mean() for c in cells]):+.2f}')
    out.append(f'  F1-SPIDER GATE -> {"CONFIRMED" if ok else "NOT CONFIRMED"}'); t = '\n'.join(out) + '\n'; (D.parent / 'report_m4_s4b.txt').write_text(t); print(t)
