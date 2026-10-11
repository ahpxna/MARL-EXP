#!/usr/bin/env python3
"""W13-5 report (PROTOCOL_CITY_WAVE13_20261006, Amendment A1): retraining on top of TSI.  FRESH2 t14-t18 x fleet seeds s1013-s1313 x fresh
traffic 940-959, HBEFA4 (H4) and PHEMlight5 (P5 suffix, same trajectories).  Arms: R (frozen fleet, no SPaT), TSI (frozen fleet, W8-2 TSI),
F1B (W8-2 retrained fleet, its table provider, raw light), F1BonT (F1B fleet under TSI), F1BT (fleet retrained under TSI, evaluated under TSI).
  D13-4 (alpha 0.05 one-sided, first attempt): F1BT meets every M3 limit vs R (H4) and F1BT - F1B agent fuel (H4) upper < 0.
Descriptive: F1BT - TSI, F1BT - F1BonT (training effect), F1BonT - F1B (interface effect on a retrained fleet), all under H4 and P5.
Self-checks KM13-1a / KM13-1b as in W13.  Usage: CITY_w13_f1bt_report.py [<dir>]  (W13_SMOKE=1, W13_SEED)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'research/city_sim/w13_20261006'
SM = os.environ.get('W13_SMOKE') == '1'
LT = (14,) if SM else (14, 15, 16, 17, 18); FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313')
S = [int(os.environ.get('W13_SEED', 860))] if SM else list(range(940, 960))
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
Rt = rows(D / 'f1bt_conf'); ARMS = ('R', 'TSI', 'F1B', 'F1BonT', 'F1BT')
bad = [f'{k} s{s}' for k, v in Rt.items() for s, r in v.items() if not (r.get('modes_ratio_all') and 0.98 <= r['modes_ratio_all'] <= 1.02)]
if bad:
    print('KM13-1b FAIL', bad[:10]); sys.exit(1)
for a in ARMS:
    for l in LT:
        for f in FL:
            for s in S:
                h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                if any(h[q] != p[q] for q in ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')):
                    print('KM13-1a FAIL', a, l, f, s); sys.exit(1)
out = ['== W13-5 retraining on top of TSI (FRESH2 t14-t18 x s1013-s1313 x fresh 940-959; HBEFA4 and PHEMlight5)', 'KM13-1a PASS, KM13-1b PASS']
r = V.paired(Rt, K('F1BT'), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K('F1BT'), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
d = V.paired(Rt, K('F1BT'), K('F1B'), LT, FL, S); v = ok and d['fuel_agent']['up'] < 0
out += ['-- D13-4 (alpha 0.05 one-sided)', V.line('F1BT - R (H4)', r), f'  F1BT all M3 limits: {ok}; {tl}', V.line('F1BT - F1B (H4)', d),
        f'  D13-4 VERDICT: retraining on top of TSI saves more fuel than retraining alone {"SHOWN" if v else "NOT SHOWN"}', '-- descriptive (one-sided 95 %)']
for x in ('', 'P5'):
    for a, b in (('TSI', 'R'), ('F1B', 'R'), ('F1BonT', 'R'), ('F1BT', 'R'), ('F1BT', 'TSI'), ('F1BT', 'F1BonT'), ('F1BonT', 'F1B'), ('TSI', 'F1B'), ('F1BT', 'F1B')):
        out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, S)))
(D / 'f1bt_conf' / 'report_f1bt.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
