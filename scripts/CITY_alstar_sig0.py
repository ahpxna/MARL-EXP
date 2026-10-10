#!/usr/bin/env python3
"""Z-4d (PROTOCOL_CITY_B6 §B6-Z amendment, DESCRIPTIVE; written 04/10/2026 wake 8 before jobs 047 / 048 ran): the A-L* fleet F* under the
learned light versus the non-learned perfect-driver comparator Z-sig0 (SUMO driving the agent cars with sigma 0, CITY_eval4_sig0) under
the SAME light, on VALIDATION 200-209 (job 048 rows) — the Z-4b question asked after the light upgrade.  Crossed bootstrap light-seed x
fleet-seed x traffic-seed (Z-sig0 has no fleet seed: its row is shared by the four F* seeds).  No verdict: reported beside AL*-2.
  plan    print the CITY_eval4_sig0 lines (one per RL-H_i, seeds 200-209) for job 048z
  report  write wave2_20261004/report_z4d.txt"""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_wave2_report_v2 as R  # noqa: E402
from scripts.CITY_alstar_validation import rows, T, VAL, W  # noqa: E402


def plan():
    for i in T:
        print(f"--light RL-H:{i} --fleet L-ACT:0 --guard always --seeds {' '.join(map(str, VAL))} --tag Z-sig0_RL-H-{i}")


def report():
    c = dict(l.split('=') for l in (W / '048' / 'CHOSEN.txt').read_text().split()); N, gd = c['F*'], c['guard']
    A, Z = rows(W / '048'), rows(W / '048z'); out = [f'== Z-4d (descriptive) VALIDATION 200-209: F* = {N} under RL-H_i vs Z-sig0 (perfect SUMO driver) under the same light']
    dr = R.draws((4, 4, 10))
    for g in sorted({gd, 'none'}):
        tag = lambda t, i: f"{N}_t{t}_RL-H-{i}_{g}".replace('+', 'P')
        cube = lambda k, pct=False: np.array([[[(100 * (A[(tag(t, i), s)][k] / Z[(f'Z-sig0_RL-H-{i}', s)][k] - 1)) if pct else
                                                (A[(tag(t, i), s)][k] - Z[(f'Z-sig0_RL-H-{i}', s)][k]) for s in VAL] for t in T] for i in T])
        out.append(f'guard {g}: agent TL {R.fmt(*R.crossed(cube("timeloss_agent"), dr))}; agent fuel % {R.fmt(*R.crossed(cube("fuel_agent", True), dr))}; '
                   f'human TL {R.fmt(*R.crossed(cube("timeloss_human"), dr))}')
    zo = np.array([[Z[(f'Z-sig0_RL-H-{i}', s)]['timeloss_agent'] - A[(f'OFF_RL-H-{i}', s)]['timeloss_agent'] for s in VAL] for i in T])
    out.append(f'Z-sig0 - always-SUMO under RL-H (agent TL): {R.fmt(*R.crossed(zo, R.draws((4, 10))))}')
    (W / 'report_z4d.txt').write_text('\n'.join(out) + '\n'); print('\n'.join(out))


if __name__ == '__main__':
    {'plan': plan, 'report': report}[sys.argv[1]]()
