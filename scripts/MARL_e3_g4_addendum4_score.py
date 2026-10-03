#!/usr/bin/env python3
"""Score of PROTOCOL_E3_G4_CONSTK_ADDENDUM4_20261001.md (written 01/10 23:23:49, before any 4x4 const-K target run) on the
const-K target panel 3301-3364.  This scorer is written 02/10/2026 11:4x EDT, BEFORE the target report exists (the 4x4
scheduler is still running seed 8).  Input: research/marl_budget/e3_g4_constk_report_20261001.json (gain per seed and the
two-level bootstrap interval per capacity, from scripts/MARL_e3_g4_constk_report.py).
C-rel (training-relative staleness, H-C): K = 1 negative; K = 2, 3 positive.   C-abs (stale = age > 2): K = 1, 2, 3 negative.
The provisioning rule A (PROTOCOL_E3_NET_COUNT Part 3) gives the same signs: K_min = 1.25 (relative) vs 3.45 (absolute).
A cell whose 95 % interval covers 0 is "no sign": reported, not scored (as the addendum says)."""
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); f = M / 'e3_g4_constk_report_20261001.json'
if not f.exists():
    raise SystemExit('const-K target report not written yet')
R = json.loads(f.read_text())
PRED = {'C-rel': {1: -1, 2: +1, 3: +1}, 'C-abs': {1: -1, 2: -1, 3: -1}}
L = [f'seeds {R["seeds"]}']; obs = {}
for K in (1, 2, 3):
    g = float(np.mean(R['gain'][str(K)])); lo, hi = R['ci'][str(K)]
    obs[K] = 0 if lo <= 0 <= hi else int(np.sign(g))
    L.append(f'K = {K}: mean gain {g:+.2f} % [{lo:+.2f}, {hi:+.2f}] -> ' + {1: 'positive', -1: 'negative', 0: 'no sign (not scored)'}[obs[K]])
for name, p in PRED.items():
    scored = [K for K in (1, 2, 3) if obs[K] != 0]; hit = [K for K in scored if obs[K] == p[K]]
    L.append(f'{name}: {len(hit)}/{len(scored)} scored cells correct (cells {scored}; correct {hit})')
disc = [K for K in (2, 3) if obs[K] != 0]
L.append('discriminating cells K = 2, 3: ' + (', '.join(f'K={K} favours {"C-rel" if obs[K] == 1 else "C-abs"}' for K in disc) if disc else 'no sign'))
text = '\n'.join(L); print(text); (M / 'e3_g4_addendum4_score_20261002.txt').write_text(text + '\n')
