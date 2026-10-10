#!/usr/bin/env python3
"""HYB report (PROTOCOL_CITY_N4_SERVICE_GATE_20261005 Amendment A2)."""
import sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import scripts.CITY_n2_report as N  # noqa: E402
import scripts.CITY_n2m_report as M  # noqa: E402
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'
if __name__ == '__main__':
    Rt = {**rows(CS / 'n1_20261005/g4'), **rows(CS / 'n2_20261005/dev'), **rows(CS / 'n2m_20261005/dev'), **rows(CS / 'n4_20261005/hyb')}; nm = lambda p: (lambda k, f: f'{p}_k{k}_{f}')
    out = ['== HYB: N2 with exact yellow answers (c2), with / without the light adapter q:1:0']; res = {}
    for a, b in (('HYB', 'R'), ('HYBQ', 'R'), ('HYB', 'N2q05'), ('HYBQ', 'N2q10')):
        res[(a, b)] = M.full(Rt, nm(a), nm(b)); out.append(M.line(f'{a} - {b}', res[(a, b)]))
    tel = {p: np.mean([Rt[f'{p}_k{k}_{f}'][s]['teleports'] for k in N.K for f in N.FL for s in N.S]) for p in ('R', 'HYB', 'HYBQ')}; out.append(f'  teleports per run {tel}')
    h = res[('HYB', 'N2q05')]; helps = (h['timeloss_agent'][2] < 0 and h['fuel_agent'][0] <= 0.5) or (h['fuel_agent'][2] < 0 and h['timeloss_agent'][0] <= 0.5)
    out.append(f'  HYBRID FIX HELPS: {helps}')
    for a in ('HYB', 'HYBQ'):
        v = res[(a, 'R')]; out.append(f'  {a} CANDIDATE (all M3 limits vs R): {v["fuel_agent"][2] < 0 and all(v[q][2] < 0.5 for q in ("timeloss", "timeloss_agent", "timeloss_human")) and tel[a] <= tel["R"] + 0.1}')
    t = '\n'.join(out) + '\n'; (CS / 'n4_20261005/report_hyb.txt').write_text(t); print(t)
