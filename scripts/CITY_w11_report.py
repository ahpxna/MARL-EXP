#!/usr/bin/env python3
"""W11 FoRL report (PROTOCOL_CITY_WAVE11_FORL_20261005 + A1).  (a) FORL vs R_F, every M3 limit (registered, alpha 0.05); (b) the cost of
anticipatability, city TL HUM_F vs HUM_R (unpaired light sets); (c) the systems, TSI2 (RL-H + TSI) vs FORL (FoRL light + own forecast), unpaired
light sets with fleets and traffic shared.  Usage: CITY_w11_report.py   (W11_SMOKE=<dir> W11_SEED=<s>)"""
import json, os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W11_SMOKE')); D = Path(os.environ['W11_SMOKE']) if SM else ROOT / 'research/city_sim/w11_20261005/forl'
S = [int(os.environ.get('W11_SEED', 860))] if SM else list(range(860, 880)); LF = ('s1',) if SM else ('s1', 's2', 's3', 's4', 's5')
LR = (4,) if SM else (4, 5, 6, 7, 8); FL = ('s213',) if SM else ('s213', 's313', 's413', 's513')
Rt = rows(D / 'conf'); out = ['== W11 FoRL (Gerner et al. 2026, port at the authors\' tls settings: L 5, kappa -0.25, beta 0.95, lambda 0; '
                              'FoRL lights s1-s5 retrained, the frozen R10 fleets s213-s513; fresh grid4 860-879)']
K = lambda a: (lambda l, f: f'{a}_{l}_{f}')  # noqa: E731
r = V.paired(Rt, K('FORL'), K('R_F'), LF, FL, S); ok, tl = V.limits(r, V.tele(Rt, K('FORL'), LF, FL, S), V.tele(Rt, K('R_F'), LF, FL, S))
out += [V.line('FORL - R_F', r), f'  FORL: all M3 limits vs R_F (incl. teleports, unfinished): {ok}; {tl}']
r2 = V.paired(Rt, K('TSI2'), K('R'), LR, FL, S); ok2, tl2 = V.limits(r2, V.tele(Rt, K('TSI2'), LR, FL, S), V.tele(Rt, K('R'), LR, FL, S))
out += [V.line('TSI2 - R (same traffic)', r2), f'  TSI2: all M3 limits vs R: {ok2}; {tl2}']
H = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
hb = V.unpaired(Rt, H('HUM_F'), LF, H('HUM_R'), LR, ('x',), S, metrics=('timeloss',))
out.append(V.line('(b) HUM_F - HUM_R (FoRL light vs RL-H, SUMO drivers, city TL)', hb))
sy = V.unpaired(Rt, K('FORL'), LF, K('TSI2'), LR, FL, S)
out.append(V.line('(c) FORL system - TSI2 system (absolute levels; fuel % of TSI2)', sy))
rf = V.unpaired(Rt, K('R_F'), LF, K('R'), LR, FL, S)
out.append(V.line('    R_F - R (the two lights without SPaT, fleets as sigma*)', rf))
st = {}
for l in LF:
    for f in FL:
        p = D / 'conf' / f'FORL_{l}_{f}_forl.json'
        if p.exists():
            for k, v in (json.loads(p.read_text()).get('provider') or {}).items():
                st[k] = st.get(k, 0) + v
out.append(f'  FoRL provider counters (all FORL runs): {st}')
out.append(f'  W11 (a) FORL MEETS EVERY M3 LIMIT vs R_F (alpha 0.05 one-sided): {"PASS" if ok else "FAIL"}')
(D / 'report_forl.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
