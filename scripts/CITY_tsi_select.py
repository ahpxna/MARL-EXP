#!/usr/bin/env python3
"""TSI selection on SELECT 650-655 (PROTOCOL_CITY_TSI_20261005).  Rows tsi_20261005/sel/T_a<A>_b<B>_k<k>; R from n4_20261005/sel/R_k<k>.
Rule: among configs with agent TL <= +0.20 and city / human TL <= +0.20 (points vs R, pooled k), the most negative agent fuel; else min agent TL."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'tsi_20261005'; S = list(range(650, 656))
GRID = [(0, 0), (1, 0), (1.5, 0), (2, 0), (1, 0.25), (1, 0.5), (1.5, 0.25), (2, 0.25)]; tag = lambda a, b, k: f'T_a{a:g}_b{b:g}_k{k}'.replace('.', 'p')
if __name__ == '__main__':
    Rt = {**rows(CS / 'n4_20261005/sel'), **rows(D / 'sel')}; tab = {}
    for a, b in GRID:
        fa = np.mean([100 * (np.mean([Rt[tag(a, b, k)][s]['fuel_agent'] for s in S]) / np.mean([Rt[f'R_k{k}'][s]['fuel_agent'] for s in S]) - 1) for k in (0, 1)])
        d = {q: float(np.mean([Rt[tag(a, b, k)][s][q] - Rt[f'R_k{k}'][s][q] for k in (0, 1) for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')}
        tab[f'{a:g},{b:g}'] = dict(fuel=float(fa), **d); print(f'A {a:g} B {b:g}: fuel {fa:+6.2f} | city {d["timeloss"]:+5.2f} agent {d["timeloss_agent"]:+5.2f} human {d["timeloss_human"]:+5.2f}')
    ok = [c for c, v in tab.items() if v['timeloss_agent'] <= 0.2 and v['timeloss'] <= 0.2 and v['timeloss_human'] <= 0.2]
    key = lambda c: sum(float(x) for x in c.split(','))
    ch = min(ok, key=lambda c: (tab[c]['fuel'], key(c))) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], key(c)))
    (D / 'sel' / 'choice.json').write_text(json.dumps(dict(choice=ch, qualified=ok, table=tab), indent=1)); print('CHOICE', ch, '(qualified:', ok, ')')
