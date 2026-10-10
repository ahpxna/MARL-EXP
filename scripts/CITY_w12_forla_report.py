#!/usr/bin/env python3
"""W12-1c report (PROTOCOL_CITY_WAVE12_20261006, Amendment A1): FoRL and PPO-0 retrained with the authors' reward scale (halting vehicle-seconds).
(a) registered: FORLA_SP meets every M3 limit vs R_FA (alpha 0.05); (a') collapse (mean green <= 7.0 s on >= 4 of 5 seeds); (b) city TL with SUMO
drivers HUM_FA - HUM_R, HUM_P0A - HUM_R, HUM_FA - HUM_P0A (unpaired); (c) FORLA_SP system vs TSI2 (unpaired); provider counters.
W11 rows (R, TSI2, HUM_R) are read unchanged.  Usage: CITY_w12_forla_report.py   (W12_SMOKE=<dir> W12_SEED=<s>)"""
import json, os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W12_SMOKE')); D = Path(os.environ['W12_SMOKE']) if SM else ROOT / 'research/city_sim/w12_20261006/forla'
W11 = ROOT / 'research/city_sim/w11_20261005/forl/conf'
S = [int(os.environ.get('W12_SEED', 860))] if SM else list(range(860, 880)); LF = ('s1',) if SM else ('s1', 's2', 's3', 's4', 's5')
LR = (4,) if SM else (4, 5, 6, 7, 8); FL = ('s213',) if SM else ('s213', 's313', 's413', 's513')
Rt = rows(D / 'conf'); Rt.update({k: {s: v[s] for s in S if s in v} for k, v in rows(W11).items() if k not in Rt})
H = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
K = lambda a: (lambda l, f: f'{a}_{l}_{f}')  # noqa: E731
out = ["== W12-1c FoRL / PPO-0 with the authors' reward scale (halting vehicle-seconds per decision interval); fresh grid4 860-879"]
r = V.paired(Rt, K('FORLA_SP'), K('R_FA'), LF, FL, S); ok, tl = V.limits(r, V.tele(Rt, K('FORLA_SP'), LF, FL, S), V.tele(Rt, K('R_FA'), LF, FL, S))
out += [V.line('FORLA_SP - R_FA', r), f'  FORLA_SP: all M3 limits vs R_FA (incl. teleports, unfinished): {ok}; {tl}']
for arm in ('HUM_FA', 'HUM_P0A'):
    g = {l: float(np.mean([Rt[f'{arm}_{l}'][s]['green_mean'] for s in S])) for l in LF}; c = sum(v <= 7.0 for v in g.values())
    out.append(f"  (a') {arm} mean green per seed: " + ', '.join(f'{l} {v:.2f}' for l, v in g.items()) + f' -> collapse: {c >= (1 if SM else 4)} ({c}/{len(LF)})')
out.append(V.line('(b) HUM_FA - HUM_R (city TL, SUMO drivers)', V.unpaired(Rt, H('HUM_FA'), LF, H('HUM_R'), LR, ('x',), S, metrics=('timeloss',))))
out.append(V.line('(b) HUM_P0A - HUM_R', V.unpaired(Rt, H('HUM_P0A'), LF, H('HUM_R'), LR, ('x',), S, metrics=('timeloss',))))
out.append(V.line('(b) HUM_FA - HUM_P0A', V.unpaired(Rt, H('HUM_FA'), LF, H('HUM_P0A'), LF, ('x',), S, metrics=('timeloss',))))
out.append(V.line('(c) FORLA_SP system - TSI2 system (absolute levels; fuel % of TSI2)', V.unpaired(Rt, K('FORLA_SP'), LF, K('TSI2'), LR, FL, S)))
out.append(V.line('    R_FA - R (the two signals without SPaT, fleets as sigma*)', V.unpaired(Rt, K('R_FA'), LF, K('R'), LR, FL, S)))
out.append(V.line('    R_P0A - R', V.unpaired(Rt, K('R_P0A'), LF, K('R'), LR, FL, S)))
st = {}
for l in LF:
    for f in FL:
        p = D / 'conf' / f'FORLA_SP_{l}_{f}_forl.json'
        if p.exists():
            for k, v in (json.loads(p.read_text()).get('provider') or {}).items():
                st[k] = st.get(k, 0) + v
out.append(f'  provider counters (all FORLA_SP runs): {st}; forecast-branch share of valid answers {st.get("forl", 0) / max(1, st.get("valid", 0)):.4f}')
out.append(f'  W12-1c (a) FORLA_SP MEETS EVERY M3 LIMIT vs R_FA (alpha 0.05 one-sided): {"PASS" if ok else "FAIL"}')
(D / 'report_forla.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
