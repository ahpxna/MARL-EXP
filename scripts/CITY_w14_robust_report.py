#!/usr/bin/env python3
"""W14-2 report (PROTOCOL_CITY_WAVE14_20261007): robustness of the W13 TSI (TRB: R13-RB choice, q 0.1) and of the W8-2 TSI (TW8, q 0.5) on
the W13 confirmation rows (FRESH2 t14-t18 x s1013-s1313 x 900-919, HBEFA4), under the CITY_w9_run perturbations
  LAT1 (1-s minimum delay, query cache), LOSS20 / LOSS50 (per-light per-second loss), DET80 (adapter detection 0.8), SPN1 (speed noise 1 m/s).
R and the unperturbed arms come from w13_20261006/conf; perturbed rows from <dir>/robust.  Descriptive, one-sided 95 % per arm, as W9:
per perturbation: arm - R (every M3 limit met? fuel upper < 0?) and TRB - TW8 under the same perturbation.  Usage: CITY_w14_robust_report.py
[<dir>]  (W14_SMOKE=1, W14_SEED)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
D = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'research/city_sim/w14_20261007'; SM = os.environ.get('W14_SMOKE') == '1'
W13 = Path(os.environ['W14_W13CONF']) if os.environ.get('W14_W13CONF') else ROOT / 'research/city_sim/w13_20261006/conf'
LT = (14,) if SM else (14, 15, 16, 17, 18); FL = ('s1013',) if SM else ('s1013', 's1113', 's1213', 's1313')
S = [int(os.environ.get('W14_SEED', 860))] if SM else list(range(900, 920))
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
Rt = {**rows(W13), **rows(D / 'robust')}
bad = [f'{k} s{s}' for k, v in Rt.items() for s, r in v.items() if 'modes_ratio_all' in r and not (0.98 <= r['modes_ratio_all'] <= 1.02)]
if bad:
    print('KM13-1b FAIL', bad[:10]); sys.exit(1)
out = ['== W14-2 robustness (FRESH2 t14-t18 x s1013-s1313 x 900-919, HBEFA4; descriptive, one-sided 95 % per arm)']
for m in ('', 'LAT1', 'LOSS20', 'LOSS50', 'DET80', 'SPN1'):
    out.append(f'-- {m or "unperturbed"}')
    for a in ('TRB', 'TW8'):
        r = V.paired(Rt, K(a + m), K('R'), LT, FL, S); ok, tl = V.limits(r, V.tele(Rt, K(a + m), LT, FL, S), V.tele(Rt, K('R'), LT, FL, S))
        out += [V.line(f'{a}{m} - R', r), f'    {a}{m}: every M3 limit {ok}; fuel saving shown {r["fuel_agent"]["up"] < 0}; {tl}']
    out.append(V.line(f'TRB{m} - TW8{m}', V.paired(Rt, K('TRB' + m), K('TW8' + m), LT, FL, S)))
(D / 'robust' / 'report_robust.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
