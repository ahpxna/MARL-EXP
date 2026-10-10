#!/usr/bin/env python3
"""W12-1 PPO-0 control report (PROTOCOL_CITY_WAVE12_20261006).  (a) collapse: mean green of each PPO-0 signal over its HUM_P0 runs (collapse iff
<= 7.0 s on >= 4 of 5 seeds); (b) signal quality, city TL with SUMO drivers: HUM_P0 - HUM_R and HUM_P0 - HUM_F (unpaired light sets, shared
traffic); descriptive R_P0 - R_F and R_P0 - R (fleets as sigma*); (c) the registered decision.  W11 rows (R, R_F, HUM_F, HUM_R) are read from
the W11 directory, unchanged.  Usage: CITY_w12_ppo0_report.py   (W12_SMOKE=<dir> W12_SEED=<s>)"""
import os, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W12_SMOKE')); D = Path(os.environ['W12_SMOKE']) if SM else ROOT / 'research/city_sim/w12_20261006/ppo0'
W11 = ROOT / 'research/city_sim/w11_20261005/forl/conf'
S = [int(os.environ.get('W12_SEED', 860))] if SM else list(range(860, 880)); LP = ('s1',) if SM else ('s1', 's2', 's3', 's4', 's5')
LR = (4,) if SM else (4, 5, 6, 7, 8); FL = ('s213',) if SM else ('s213', 's313', 's413', 's513')
Rt = rows(D / 'conf'); Rt.update({k: {s: v[s] for s in S if s in v} for k, v in rows(W11).items() if k not in Rt})   # W11 rows restricted to this panel's seeds
H = lambda a: (lambda l, f: f'{a}_{l}')  # noqa: E731
K = lambda a: (lambda l, f: f'{a}_{l}_{f}')  # noqa: E731
out = ['== W12-1 PPO-0 control (CITY_forl with kappa 0: same architecture, observation, reward, seeds, budget as the W11 FoRL signals; fresh grid4 860-879)']
g = {l: float(np.mean([Rt[f'HUM_P0_{l}'][s]['green_mean'] for s in S])) for l in LP}
gf = {l: float(np.mean([Rt[f'HUM_F_{l}'][s]['green_mean'] for s in S])) for l in LP if f'HUM_F_{l}' in Rt}
col = sum(v <= 7.0 for v in g.values()); collapse = col >= (1 if SM else 4)
out.append('  (a) mean green per seed, PPO-0: ' + ', '.join(f'{l} {v:.2f}' for l, v in g.items()) + ' | FoRL: ' + ', '.join(f'{l} {v:.2f}' for l, v in gf.items())
           + f' -> {col}/{len(LP)} at or below 7.0 s: PPO-0 collapses too: {collapse}')
hr = V.unpaired(Rt, H('HUM_P0'), LP, H('HUM_R'), LR, ('x',), S, metrics=('timeloss',)); out.append(V.line('(b) HUM_P0 - HUM_R (city TL, SUMO drivers)', hr))
hf = V.unpaired(Rt, H('HUM_P0'), LP, H('HUM_F'), LP, ('x',), S, metrics=('timeloss',)); out.append(V.line('(b) HUM_P0 - HUM_F (city TL, SUMO drivers)', hf))
out.append(V.line('    R_P0 - R_F (no SPaT, fleets as sigma*)', V.unpaired(Rt, K('R_P0'), LP, K('R_F'), LP, FL, S)))
out.append(V.line('    R_P0 - R (no SPaT, fleets as sigma*)', V.unpaired(Rt, K('R_P0'), LP, K('R'), LR, FL, S)))
better = hf['timeloss']['up'] < 0
dec = ('the W11 failure is attributed to the shared recipe of this port, not to the penalty; next: a recipe repair (registered separately)' if collapse else
       ('the penalty causes the trade-off in this setting; next: W12-1b PPO-0 + TSI vs FoRL + provider (to be registered)' if better else
        'PPO-0 does not collapse but is not better than FoRL on city TL: no attribution; report descriptively'))
out.append(f'  (c) W12-1 DECISION: {dec}')
(D / 'report_ppo0.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
