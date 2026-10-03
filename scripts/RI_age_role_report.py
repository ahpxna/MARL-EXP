#!/usr/bin/env python3
"""Report of PROTOCOL_RI_AGE_ROLE_20261002.md (written before the full run).  AR1 h(λ) strictly rising; AR2 at λ = 0 remap >= 0
at a = 0..3 and |h(0)| <= 0.02; AR3 minimal emulation >= full emulation at every λ, a = 0..3; reported r(λ)."""
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); R = json.loads((M / 'ri_age_role_20261002/results.json').read_text())
lams = [str(l) for l in R['lams']]; L = []
def mean(lam, key, a):
    return float(np.mean([R['res'][lam][s][key][str(a)] for s in R['res'][lam]]))
h = {}; ar2 = True; ar3 = True
for lam in lams:
    pl = [mean(lam, 'plain', a) for a in range(9)]; rm = [mean(lam, 'remap', a) for a in range(4)]
    ef = [mean(lam, 'emu_full', a) for a in range(4)]; em = [mean(lam, 'emu_min', a) for a in range(4)]
    h[lam] = float(np.mean([pl[a] - rm[a] for a in range(4)]))
    if float(lam) == 0.0:
        ar2 = all(v >= 0 for v in rm) and abs(h[lam]) <= 0.02
    ar3 = ar3 and all(em[a] >= ef[a] for a in range(4))
    L += [f'λ = {lam}: plain a=0..8 ' + ' '.join(f'{v:+.3f}' for v in pl),
          f'   a=0..3 remap ' + ' '.join(f'{v:+.3f}' for v in rm) + ' | full emulation ' + ' '.join(f'{v:+.3f}' for v in ef)
          + ' | minimal emulation ' + ' '.join(f'{v:+.3f}' for v in em),
          f'   remap harm h = {h[lam]:+.3f}; upgrade regression r = plain(a=4) − plain(a=0) = {pl[4] - pl[0]:+.3f}']
hs = [h[l] for l in lams]; ar1 = all(hs[i] < hs[i + 1] for i in range(len(hs) - 1))
L += [f'AR1 remap harm rises with λ: ' + ', '.join(f'{l} {h[l]:+.3f}' for l in lams) + f' -> {"SUPPORTED" if ar1 else "NOT SUPPORTED"}',
      f'AR2 driftless safety (λ = 0: remap >= 0 at a = 0..3, |h| <= 0.02) -> {"SUPPORTED" if ar2 else "NOT SUPPORTED"}',
      f'AR3 minimal emulation >= full emulation at every λ, a = 0..3 -> {"SUPPORTED" if ar3 else "NOT SUPPORTED"}']
text = '\n'.join(L); print(text); (M / 'ri_age_role_report_20261002.txt').write_text(text + '\n')
