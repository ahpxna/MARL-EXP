#!/usr/bin/env python3
"""W13-6a report (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): TSI recalibrated under IDM with every policy frozen.  FRESH2 t14-t18 x
s1013-s1313 x fresh 960-979, every vehicle IDM; HBEFA4 (H4) and PHEMlight5 (P5 suffix, same trajectories).  Arms: R, TSIK (the Krauss-
calibrated W8-2 TSI, as in W9-4), TSII (IDM-recalibrated TSI), F1B (W8-2 retrained fleets, trained under Krauss).
  D13-5 (alpha 0.05 one-sided): TSII meets every M3 limit vs R and TSII - R agent fuel (H4) upper < 0.
Self-checks KM13-1a / KM13-1b.  Usage: CITY_w13_idm_report.py [<dir>]  (W13_SMOKE=1, W13_SEED)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'research/city_sim/w13_20261006'
SM = os.environ.get('W13_SMOKE') == '1'
LT = (14,) if SM else (14, 15, 16, 17, 18); FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313')
S = [int(os.environ.get('W13_SEED', 860))] if SM else list(range(960, 980))
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
Rt = rows(D / 'idm' / 'conf')
for a in ('R', 'TSIK', 'TSII', 'F1B'):
    for l in LT:
        for f in FL:
            for s in S:
                h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                if any(h[q] != p[q] for q in ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')) \
                        or not (0.98 <= h['modes_ratio_all'] <= 1.02) or not h.get('w13_idm'):
                    print('KM13-1a/1b or IDM flag FAIL', a, l, f, s); sys.exit(1)
out = ['== W13-6a TSI recalibrated under IDM (FRESH2 t14-t18 x s1013-s1313 x fresh 960-979; every vehicle IDM)', 'KM13-1a PASS, KM13-1b PASS, IDM flag on every row']
r = V.paired(Rt, K('TSII'), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K('TSII'), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
out += ['-- D13-5 (alpha 0.05 one-sided)', V.line('TSII - R (H4)', r), f'  TSII all M3 limits: {ok}; {tl}',
        f'  D13-5 VERDICT: IDM-recalibrated TSI meets every limit with a fuel saving {"SHOWN" if ok else "NOT SHOWN"}', '-- descriptive (one-sided 95 %)']
for x in ('', 'P5'):
    for a, b in (('TSIK', 'R'), ('TSII', 'R'), ('F1B', 'R'), ('TSII', 'TSIK'), ('TSII', 'F1B')):
        out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, S)))
(D / 'idm' / 'conf' / 'report_idm.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
