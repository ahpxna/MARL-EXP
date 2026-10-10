#!/usr/bin/env python3
"""TSI variants report (PROTOCOL_CITY_TSI_VARIANTS_20261005): SELECT 650-655 points vs R for TSI, HYBD, HYBNL, HYBDNL (adapter q:2:0)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; S = list(range(650, 656))
if __name__ == '__main__':
    Rt = {**rows(CS / 'n4_20261005/sel'), **rows(CS / 'tsi_20261005/sel'), **rows(CS / 'tsiv_20261005/sel')}; tab = {}
    for nm, tg in (('TSI', lambda k: f'T_a2_b0_k{k}'), ('HYBD', lambda k: f'HYBD_k{k}'), ('HYBNL', lambda k: f'HYBNL_k{k}'), ('HYBDNL', lambda k: f'HYBDNL_k{k}')):
        fa = np.mean([100 * (np.mean([Rt[tg(k)][s]['fuel_agent'] for s in S]) / np.mean([Rt[f'R_k{k}'][s]['fuel_agent'] for s in S]) - 1) for k in (0, 1)])
        d = {q: float(np.mean([Rt[tg(k)][s][q] - Rt[f'R_k{k}'][s][q] for k in (0, 1) for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')}
        tab[nm] = dict(fuel=float(fa), **d)
    out = ['== TSI variants on SELECT 650-655 (points vs R)'] + [f'  {n:7s} fuel {v["fuel"]:+6.2f} | city {v["timeloss"]:+5.2f} agent {v["timeloss_agent"]:+5.2f} human {v["timeloss_human"]:+5.2f}' for n, v in tab.items()]
    t0 = tab['TSI']
    for n in ('HYBD', 'HYBNL', 'HYBDNL'):
        v = tab[n]; imp = v['timeloss_agent'] <= t0['timeloss_agent'] - 0.15 and v['fuel'] <= t0['fuel'] + 0.30 and v['timeloss'] <= 0.2 and v['timeloss_human'] <= 0.2
        out.append(f'  {n} IMPROVES ON TSI: {imp}')
    t = '\n'.join(out) + '\n'; (CS / 'tsiv_20261005/report_tsiv.txt').write_text(t); print(t)
