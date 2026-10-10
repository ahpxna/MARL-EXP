#!/usr/bin/env python3
"""SHIFT report (PROTOCOL_CITY_SHIFT_20261005): TSI2 / HYB vs R on traffic 740-749 (period 1.6 s), lights t4-t8 x fleets s213-s513."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_tsi2_report as T  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/shift_20261005'; T.S = list(range(740, 750))
if __name__ == '__main__':
    Rt = rows(D / 'conf'); out = ['== SHIFT: demand +25 % (period 1.6 s; traffic 740-749), TSI-2 design frozen']
    for a, b in (('TSI2', 'R'), ('HYB', 'R'), ('TSI2', 'HYB')):
        r = T.full(Rt, a, b); out.append(f'  {a} - {b}: ' + ' | '.join(f'{k} {v[0]:+.2f} [{v[1][0]:+.2f}, {v[1][1]:+.2f}] (up {v[2]:+.2f})' for k, v in r.items()))
        if (a, b) == ('TSI2', 'R'):
            ok = r['fuel_agent'][2] < 0 and all(r[q][2] < 0.5 for q in ('timeloss', 'timeloss_agent', 'timeloss_human'))
    tel = {a: np.mean([Rt[T.nm(a, t, i)][s]['teleports'] for t in T.L for i in range(4) for s in T.S]) for a in ('R', 'TSI2')}
    out += [f'  teleports per run {tel}', f'  SHIFT (descriptive): TSI2 within every M3 limit at one-sided 95 %: {ok}']
    t = '\n'.join(out) + '\n'; (D / 'report_shift.txt').write_text(t); print(t)
