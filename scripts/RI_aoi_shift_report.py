#!/usr/bin/env python3
"""Report of PROTOCOL_RI_AOI_SHIFT_20261002.md (written before the full run).  Reads research/marl_budget/ri_aoi_shift_20261002/
results.json.  UR1 slow gain(a=0) < gain(a=4) in the mean and >= 4/5 seeds; UR2 crossing; UR3 mix >= max(fast, slow) - 0.02 at
every a; UR4 emulation within +-0.01 of slow's a = 4 gain; reported: W1 slopes, label remap, mixture premium."""
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); R = json.loads((M / 'ri_aoi_shift_20261002/results.json').read_text())
S = sorted(R['seeds'], key=int); A = range(9)
g = {n: np.array([[R['seeds'][s]['gain'][n][str(a)] for a in A] for s in S]) for n in ('fast', 'slow', 'mix')}
em = np.array([[R['seeds'][s]['emulation'][str(a)] for a in range(4)] for s in S]); rm = np.array([[R['seeds'][s]['remap'][str(a)] for a in range(4)] for s in S])
m = {n: v.mean(0) for n, v in g.items()}
L = ['gain vs silent (1 - MSE/MSE_silent), mean over seeds; deployment window a = 0..8 (δ ~ U{a..a+3})']
for n in g:
    L.append(f'{n:4s}: ' + ' '.join(f'{v:+.3f}' for v in m[n]))
L.append('slow + emulation a=0..3: ' + ' '.join(f'{v:+.3f}' for v in em.mean(0)) + ' | slow + label remap a=0..3: ' + ' '.join(f'{v:+.3f}' for v in rm.mean(0)))
UR1 = m['slow'][0] < m['slow'][4] and int((g['slow'][:, 0] < g['slow'][:, 4]).sum()) >= 4
UR2 = m['fast'][0] > m['slow'][0] and m['slow'][4] > m['fast'][4]
UR3 = all(m['mix'][a] >= max(m['fast'][a], m['slow'][a]) - 0.02 for a in A)
UR4 = bool(np.all(np.abs(em.mean(0) - m['slow'][4]) <= 0.01))
up = np.polyfit([4 - a for a in range(5)], [m['slow'][a] for a in range(5)], 1)[0]   # gain per unit W1, upgrade side
dn = np.polyfit([a - 4 for a in range(4, 9)], [m['slow'][a] for a in range(4, 9)], 1)[0]
L += [f'UR1 upgrade regression: slow a=0 {m["slow"][0]:+.3f} vs a=4 {m["slow"][4]:+.3f}; seeds with a=0 < a=4: {int((g["slow"][:, 0] < g["slow"][:, 4]).sum())}/5 -> {"SUPPORTED" if UR1 else "NOT SUPPORTED"}',
      f'UR2 crossing: a=0 fast {m["fast"][0]:+.3f} vs slow {m["slow"][0]:+.3f}; a=4 slow {m["slow"][4]:+.3f} vs fast {m["fast"][4]:+.3f} -> {"SUPPORTED" if UR2 else "NOT SUPPORTED"}',
      f'UR3 mixture covers: min over a of mix - max(fast, slow) = {min(m["mix"][a] - max(m["fast"][a], m["slow"][a]) for a in A):+.3f} (need >= -0.02) -> {"SUPPORTED" if UR3 else "NOT SUPPORTED"}',
      f'UR4 emulation: max |emulation - slow(a=4)| = {float(np.max(np.abs(em.mean(0) - m["slow"][4]))):.4f} (need <= 0.01) -> {"SUPPORTED" if UR4 else "NOT SUPPORTED"}',
      f'reported: slow-trained slope of gain per unit W1 — upgrade side (a = 4 -> 0) {up:+.4f}, downgrade side (a=4 -> 8) {dn:+.4f}',
      f'reported: mixture premium (mix - specialist): a=0 {m["mix"][0] - m["fast"][0]:+.3f}, a=4 {m["mix"][4] - m["slow"][4]:+.3f}; label remap - plain (slow, a=0..3): '
      + ' '.join(f'{v:+.3f}' for v in (rm.mean(0) - m['slow'][:4]))]
text = '\n'.join(L); print(text); (M / 'ri_aoi_shift_report_20261002.txt').write_text(text + '\n')
