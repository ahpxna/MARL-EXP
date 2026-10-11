#!/usr/bin/env python3
"""S14 (Amendment A1): DEV-report logic on synthetic inputs.  Exit 1 on failure.
  (a) a missing seed in any row set -> SystemExit (no silent COMPLETE);  (b) selection prefers a FEASIBLE setting even when an infeasible one
  has lower fuel; (c) all-infeasible -> the best fuel is returned and marked infeasible;  (d) feasibility uses the bootstrap UPPER bound,
  not the point (a point below +0.5 with an upper above +0.5 is infeasible)."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_m3_dev_report as DR  # noqa: E402
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
bad = []
row = lambda tl, ta, th, f, tel=0, unf=0: dict(timeloss=tl, timeloss_agent=ta, timeloss_human=th, fuel_agent=f, fuel=f, teleports=tel, unfinished=unf)
Rt = {}
for k in DR.KS:
    for fl in DR.FLS:
        Rt[DR.tag(k, fl, 'R')] = {s: row(20, 20, 20, 1000) for s in DR.S}
        rng = np.random.default_rng(k * 10 + len(fl))
        Rt[DR.tag(k, fl, 'X')] = {s: row(20 + 0.3 + rng.normal(0, 1.5), 20, 20, 990) for s in DR.S}     # point +0.3, noisy -> upper > 0.5
        Rt[DR.tag(k, fl, 'Y')] = {s: row(20.1, 20, 20, 995) for s in DR.S}                            # feasible, smaller gain
dr = R.draws((2, 2, len(DR.S)))
okx, tlx, _, _ = DR.feasible(Rt, 'X', dr); oky, _, _, _ = DR.feasible(Rt, 'Y', dr)
print('X city TL point', round(tlx['timeloss']['p'], 2), 'upper', round(tlx['timeloss']['up'], 2), 'feasible', okx, '| Y feasible', oky)
if okx or not oky:
    bad.append('S14d feasibility must use the upper bound')
best, feas = DR.select({'X': (okx, -1.0), 'Y': (oky, -0.5)})
if best != 'Y' or not feas:
    bad.append('S14b selection must prefer the feasible setting')
best, feas = DR.select({'X': (False, -1.0), 'Z': (False, -0.2)})
if best != 'X' or feas:
    bad.append('S14c all-infeasible handling')
Rt2 = dict(Rt); Rt2[DR.tag(0, 's13', 'Y')] = {s: v for s, v in Rt[DR.tag(0, 's13', 'Y')].items() if s != 100}
try:
    DR.feasible(Rt2, 'Y', dr); bad.append('S14a missing seed not detected')
except SystemExit as e:
    print('S14a missing seed ->', e)
print('M3 S14', 'PASS' if not bad else 'FAIL ' + '; '.join(bad)); sys.exit(1 if bad else 0)
