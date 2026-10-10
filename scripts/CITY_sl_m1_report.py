#!/usr/bin/env python3
"""F1-2 M1-SL (PROTOCOL_CITY_F1_SALTLAKE_20261008): Salt Lake 400S & 200W, tuned FT, recorded-demand DEV days.  Rows in <dir>:
OFF[P5]_t0_h (every car a SUMO human; fleet membership L-ACT:0, guard always) and PL[P5]_t0_s<f> (the R10-recipe fleet with exact FT SPaT).
Decision M1-SL (alpha 0.05): PL - OFF agent fuel upper < 0 under HBEFA4 and PHEMlight5, every M3 time limit, teleports not higher.
KM13-1a/1b.  Usage: CITY_sl_m1_report.py <dir>   (SL_SMOKE=1: first DEV day, fleet 13)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
from scripts.CITY_sl_build import days  # noqa: E402
D = Path(sys.argv[1]); SM = os.environ.get('SL_SMOKE') == '1'
S = [d.timetuple().tm_yday for d in days('400sX200w', 'dev')][:1 if SM else 10]; FL = ('s13',) if SM else ('s13', 's113')
K = lambda a: (lambda l, f: f'{a}_t{l}_{f}')  # noqa: E731
Rt = rows(D); TW = ('timeloss', 'timeloss_agent', 'timeloss_human', 'n', 'teleports', 'unfinished', 'action_digest')
for x in ('', 'P5'):
    for f in FL:
        Rt[f'OFF{x}_t0_{f}'] = Rt[f'OFF{x}_t0_h']
for a, fs in (('OFF', ('h',)), ('PL', FL)):
    for f in fs:
        for s in S:
            h, p = Rt[K(a)(0, f)][s], Rt[K(a + 'P5')(0, f)][s]
            if any(h[t] != p[t] for t in TW) or not (0.98 <= h['modes_ratio_all'] <= 1.02):
                print('KM13-1a/1b FAIL', a, f, s); sys.exit(1)
r = V.paired(Rt, K('PL'), K('OFF'), (0,), FL, S); ok, tl = V.limits(r, V.tele(Rt, K('PL'), (0,), FL, S), V.tele(Rt, K('OFF'), (0,), FL, S))
r5 = V.paired(Rt, K('PLP5'), K('OFFP5'), (0,), FL, S); m1 = ok and r['fuel_agent']['up'] < 0 and r5['fuel_agent']['up'] < 0
out = [f'== F1-2 M1-SL, Salt Lake 400S & 200W, tuned FT, recorded demand DEV days {S[0]}-{S[-1]} (fleets {FL})', 'KM13-1a PASS, KM13-1b PASS',
       V.line('PL - OFF (H4)', r), f'  all M3 limits: {ok}; {tl}', V.line('PL - OFF (P5)', r5), f'  M1-SL VERDICT: {"SHOWN" if m1 else "NOT SHOWN"}']
(D / 'report_m1sl.txt').write_text('\n'.join(out) + '\n'); (D / 'm1sl.json').write_text(json.dumps(dict(M1_SL=m1))); print('\n'.join(out))
