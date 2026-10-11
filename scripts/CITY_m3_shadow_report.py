#!/usr/bin/env python3
"""M3 Addendum A2 report (descriptive): per E arm, cube [k 0/1, shadow fleet s13/s113, traffic 15], crossed bootstrap.
  M3-4clean = (E + shadow) vs (RL-H:k + σ*)   [R_k{k}_sig rows of the DEV screen]   city TL, city fuel %, agent fuel %
  M3-3clean = (E + R10 driving) vs (E + shadow)                                        agent fuel %, agent TL, human TL
  plus gridlock count (runs with > 10 teleports) under the shadow vs the old σ*-car rows (C-68)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
B = Path(__file__).resolve().parents[1] / 'research/city_sim/m3_20261004'; S = [100, 101, 102, 103, 104] + list(range(200, 210))
ARMS = ['E_E0q_lam0', 'E_E0p_lam0'] + [f'E_{a}_lam{l}' for a in ('uniform', 'eta', 'active', 'receiver') for l in (1, 4)]
if __name__ == '__main__':
    Sh, Dv = rows(B / 'shadow'), rows(B / 'dev'); dr = R.draws((2, 2, len(S))); out = ['== M3 A2 clean decomposition (DESCRIPTIVE): E light with deployment-equivalent inputs (shadow R10), DEV']

    def cube(F, Bf, key, pct):
        c = np.zeros((2, 2, len(S)))
        for i, k in enumerate((0, 1)):
            for j, fl in enumerate(('s13', 's113')):
                f, b = F(k, fl), Bf(k, fl)
                if sorted(f) != S or sorted(b) != S:
                    raise SystemExit('INCOMPLETE')
                c[i, j] = [100 * (f[s][key] / b[s][key] - 1) if pct else f[s][key] - b[s][key] for s in S]
        return R.crossed(c, dr)
    fmt = lambda x: f'{x[0]:+.2f} [{x[1][0]:+.2f}, {x[1][1]:+.2f}]'
    for a in ARMS:
        sh = lambda k, fl, a=a: Sh[f'{a}_k{k}_{fl}']; rs = lambda k, fl: Dv[f'R_k{k}_sig']; fd = lambda k, fl, a=a: Dv[f'{a}_k{k}_{fl}']
        c4t, c4f, c4a = cube(sh, rs, 'timeloss', False), cube(sh, rs, 'fuel', True), cube(sh, rs, 'fuel_agent', True)
        c3f, c3a, c3h = cube(fd, sh, 'fuel_agent', True), cube(fd, sh, 'timeloss_agent', False), cube(fd, sh, 'timeloss_human', False)
        g_sh = sum(1 for k in (0, 1) for fl in ('s13', 's113') for s in S if sh(k, fl)[s]['teleports'] > 10)
        g_old = sum(1 for k in (0, 1) for s in S if Dv[f'{a}_k{k}_sig'][s]['teleports'] > 10)
        out.append(f'  {a:18s} M3-4clean city TL {fmt(c4t)} city fuel % {fmt(c4f)} | M3-3clean agent fuel % {fmt(c3f)} agent TL {fmt(c3a)} human TL {fmt(c3h)} '
                   f'| gridlock runs shadow {g_sh}/60 (old σ*-car rows {g_old}/30)')
    t = '\n'.join(out) + '\n'; (B / 'report_m3_shadow.txt').write_text(t); print(t)
