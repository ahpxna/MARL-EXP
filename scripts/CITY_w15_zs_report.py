#!/usr/bin/env python3
"""W15-1 report (PROTOCOL_CITY_WAVE15_20261007): the zero-shot default TG = (A, B, q) = (1, 0.25, 0.1) on the newly trained FRESH3 panel
(RL-H t19-t23 x fleets s1413-s1713 x fresh traffic 1040-1059), HBEFA4 and PHEMlight5 (P5 suffix, same trajectories).
Arms: R, TG (default, no adapter / q tuning), TRB (per-light R13-RB tuning, for comparison), F1B (fleets retrained from scratch).
  D15-1  (alpha 0.05): TG meets every M3 limit vs R and TG - R fuel upper < 0 under HBEFA4 and under PHEMlight5.
  D15-1b (alpha 0.05): TG - F1B fuel (HBEFA4) upper < +0.5 pp (TG meeting every limit).
KM13-1a / KM13-1b.  Usage: CITY_w15_zs_report.py <dir>   (W15_SMOKE=1, W15_SEED)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]); SM = os.environ.get('W15_SMOKE') == '1'
LT = (19,) if SM else (19, 20, 21, 22, 23); FL = ('s1413',) if SM else ('s1413', 's1513', 's1613', 's1713')
S = [int(os.environ.get('W15_SEED', 860))] if SM else list(range(1040, 1060))
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
Rt = rows(D / 'conf'); TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
for a in ('R', 'TG', 'TRB', 'F1B'):
    for l in LT:
        for f in FL:
            for s in S:
                h, p = Rt[K(a)(l, f)][s], Rt[K(a + 'P5')(l, f)][s]
                if any(h[k] != p[k] for k in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                    print('KM13-1a/1b FAIL', a, l, f, s); sys.exit(1)
out = [f'== W15-1 zero-shot default (1, 0.25, 0.1) on FRESH3 (lights {LT}, fleets {FL}, fresh traffic {S[0]}-{S[-1]}; HBEFA4 / PHEMlight5)',
       'KM13-1a PASS, KM13-1b PASS']
r = V.paired(Rt, K('TG'), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K('TG'), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
r5 = V.paired(Rt, K('TGP5'), K('RP5'), LT, FL, S); v1 = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
d = V.paired(Rt, K('TG'), K('F1B'), LT, FL, S)
out += ['-- D15-1 (alpha 0.05 one-sided)', V.line('TG - R (H4)', r), f'  TG all M3 limits: {ok}; {tl}', V.line('TG - R (P5)', r5),
        f'  D15-1 VERDICT: zero-shot default saves fuel under both emission models on new lights and fleets {"SHOWN" if v1 else "NOT SHOWN"}',
        '-- D15-1b (alpha 0.05 one-sided)', V.line('TG - F1B (H4)', d),
        f'  D15-1b VERDICT: fuel non-inferiority to retraining {"ESTABLISHED" if ok and d["fuel_agent"]["up"] < 0.5 else "NOT ESTABLISHED"}',
        '-- descriptive (one-sided 95 %)']
for x in ('', 'P5'):
    for a, b in (('TRB', 'R'), ('TG', 'TRB'), ('F1B', 'R'), ('TRB', 'F1B'), ('TG', 'R')):
        out.append(V.line(f'{a}{x} - {b}{x}', V.paired(Rt, K(a + x), K(b + x), LT, FL, S)))
(D / 'conf' / 'report_zs.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
