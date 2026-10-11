#!/usr/bin/env python3
"""W9-3b (PROTOCOL_CITY_WAVE9_20261005, Amendment A1): the R10 fleet's own benefit under the fixed-time signal with PHEMlight5 vs HBEFA4.
Self-check KW9-3b: R_FT_EM2 / PL_FT_EM2 time losses and counts == the W9-6 R_FT / PL_FT rows.  Usage: CITY_w9_emft_report.py  (W9_SMOKE=<dir> W9_SEED=s)"""
import os, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
import scripts.CITY_w6_report_v2 as V  # noqa: E402
from scripts.CITY_w6_validation import rows  # noqa: E402
SM = bool(os.environ.get('W9_SMOKE')); W = Path(os.environ['W9_SMOKE']) if SM else ROOT / 'research/city_sim/w9_20261005'
S = [int(os.environ.get('W9_SEED', 820))] if SM else list(range(820, 840)); FL = ('s613',) if SM else ('s613', 's713', 's813', 's913'); L = ('FT',)
Rt = {}
for d in (W / 'emft' / 'conf', Path(os.environ.get('W9_MPCONF', ROOT / 'research/city_sim/w9_20261005/mp/conf'))):
    for k, v in rows(d).items():
        Rt[k] = {s: r for s, r in v.items() if s in S}
K = lambda a: (lambda l, f: f'{a}_{f}')  # noqa: E731
bad = [(a, f, s, q) for a, b in (('R_FT_EM2', 'R_FT'), ('PL_FT_EM2', 'PL_FT')) for f in FL for s in S for q in ('timeloss', 'timeloss_agent', 'timeloss_human', 'n')
       if abs(Rt[f'{a}_{f}'][s][q] - Rt[f'{b}_{f}'][s][q]) > 1e-9]
out = ['== W9-3b EMFT: the fleet\'s own benefit under FT with PHEMlight5/PC_EU4_G vs HBEFA4 (W7-1 fleets s613-s913 x traffic 820-839; one light: bootstrap over fleet x traffic)',
       f'  KW9-3b self-check (time losses and counts identical to the HBEFA4 rows): {not bad} {bad[:3]}']
out.append(V.line('PL_FT - R_FT (HBEFA4)', V.paired(Rt, K('PL_FT'), K('R_FT'), L, FL, S)))
out.append(V.line('PL_FT_EM2 - R_FT_EM2 (PHEMlight5)', V.paired(Rt, K('PL_FT_EM2'), K('R_FT_EM2'), L, FL, S)))
(W / 'emft').mkdir(parents=True, exist_ok=True); (W / 'emft' / 'report_emft.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))
