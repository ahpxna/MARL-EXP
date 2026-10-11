#!/usr/bin/env python3
"""W10-4 SPIDER-2L report (PROTOCOL_CITY_WAVE10_20261005, Amendment A2): preconditions P1 (RLK vs FT, SUMO drivers, DEV 100-104) and
P2 (rule fleet GLOSAL:0.3 vs sigma* under FT, DEV), then TSIK / HYBK / ADPK vs R on 1110-1129 (lights 11 / 111 x the rule fleet; crossed
bootstrap over light x traffic).  Usage: CITY_w10_sp2l_report.py   (W10_SMOKE=<dir>: smoke, seeds 100 / 1110)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W10_SMOKE')); W = Path(os.environ['W10_SMOKE']) if SM else ROOT / 'research/city_sim/w10_20261005'
D = W / 'sp2l'; DEV = [100] if SM else [100, 101, 102, 103, 104]; CONF = [1110] if SM else list(range(1110, 1130)); L = (11, 111); F = ('rule',)
out = ['== W10-4 SPIDER-2L (spider geometry with 2 lanes per edge; inner-ring signals B1-B6 have 2 greens instead of 3 (disclosed); rule fleet; '
       'RLK lights and TSI recalibrated from scratch)']
P = rows(D / 'pre')
p1 = V.unpaired(P, lambda l, f: f'RLK{l}_h', L, lambda l, f: 'FT_h', ('x',), F, DEV, metrics=('timeloss',)); ok1 = p1['timeloss']['up'] < 0   # human-only runs: city TL only
out += [V.line('P1 RLK - FT (SUMO drivers, DEV; city TL)', p1), f'  P1 learned light beneficial (city TL upper < 0): {ok1}']
p2 = V.paired(P, lambda l, f: 'GLOSAL_FT', lambda l, f: 'SIG_FT', ('x',), F, DEV); ok2 = p2['fuel_agent']['up'] < 0
out += [V.line('P2 rule fleet - sigma* under FT (DEV)', p2), f'  P2 fleet benefit to protect (agent fuel upper < 0): {ok2}']
out.append(f'  FT city TL on spider-2L (DEV mean): {sum(P["FT_h"][s]["timeloss"] for s in DEV) / len(DEV):.2f} s/veh (1-lane spider FT, C-76: 93.67)')
Rt = rows(D / 'conf'); K = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
for a in ('TSIK', 'HYBK', 'ADPK'):
    r = V.paired(Rt, K(a), K('R'), L, F, CONF); ok, tl = V.limits(r, V.tele(Rt, K(a), L, F, CONF), V.tele(Rt, K('R'), L, F, CONF))
    out += [V.line(f'{a} - R', r), f'  {a}: all M3 limits (incl. teleports, unfinished): {ok}; {tl}']
    if a == 'TSIK':
        v = ok
g = lambda a: sum(Rt[f'{a}_{l}'][s]['green_mean'] for l in L for s in CONF) / (len(L) * len(CONF))  # noqa: E731
out.append('  mean green (s): ' + '; '.join(f'{a} {g(a):.1f}' for a in ('R', 'HYBK', 'TSIK', 'ADPK')) + '   (1-lane spider attempt 1: R 18.9, HYBK 28.7, TSIK 17.3)')
out.append(f'  W10-4 SPIDER-2L VERDICT (TSIK meets every M3 limit vs R, alpha 0.05 one-sided): {"PASS" if v else "FAIL"}'
           + ('' if ok1 and ok2 else '  [conditional: a precondition failed]'))
(D / 'report_sp2l.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
