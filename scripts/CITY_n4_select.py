#!/usr/bin/env python3
"""N4 selection on SELECT 650-655 (PROTOCOL_CITY_N4_SERVICE_GATE_20261005): J = agent fuel % vs R + 5 * sum max(0, dTL) (city, agent, human),
pooled over k 0 / 1 (fleet s13).  Writes n4_20261005/sel/choice.json: G* (argmin over all), Wbest, Hbest, p (G* activation)."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/n4_20261005'; S = list(range(650, 656)); GRID = ['all', 'w:3', 'w:6', 'w:10', 'h:10', 'h:20', 'h:30'] + [f'wh:{a},{b}' for a in (3, 6, 10) for b in (10, 20, 30)]
tag = lambda g, k: f'S_{g.replace(":", "").replace(",", "_")}_k{k}'
if __name__ == '__main__':
    Rt = rows(D / 'sel'); out = {}
    for g in GRID:
        fa = np.mean([100 * (np.mean([Rt[tag(g, k)][s]['fuel_agent'] for s in S]) / np.mean([Rt[f'R_k{k}'][s]['fuel_agent'] for s in S]) - 1) for k in (0, 1)])
        pen = sum(max(0.0, np.mean([Rt[tag(g, k)][s][q] - Rt[f'R_k{k}'][s][q] for k in (0, 1) for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human'))
        act = np.mean([json.load(open(D / 'sel' / f'{tag(g, k)}_n4.json'))['activation'] for k in (0, 1)])
        dta = np.mean([Rt[tag(g, k)][s]['timeloss_agent'] - Rt[f'R_k{k}'][s]['timeloss_agent'] for k in (0, 1) for s in S])
        out[g] = dict(J=float(fa + 5 * pen), fuel=float(fa), pen=float(pen), dTL_agent=float(dta), activation=float(act)); print(f'{g:10s} J {fa + 5 * pen:+7.3f} fuel {fa:+6.2f} pen {pen:5.2f} dTLa {dta:+5.2f} act {act:.3f}')
    best = lambda fam: min((g for g in GRID if fam(g)), key=lambda g: out[g]['J'])
    ch = dict(G=best(lambda g: True), W=best(lambda g: g.startswith('w:')), H=best(lambda g: g.startswith('h:'))); ch['p'] = round(out[ch['G']]['activation'], 3); ch['table'] = out
    (D / 'sel' / 'choice.json').write_text(json.dumps(ch, indent=1)); print('CHOICE', {k: v for k, v in ch.items() if k != 'table'})
