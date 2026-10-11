#!/usr/bin/env python3
"""TSI Amendment A1: one-shot vs refit forecaster at (A*, B*) on SELECT 650-655, by the TSI selection rule."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
CS = Path(__file__).resolve().parents[1] / 'research/city_sim'; D = CS / 'tsi_20261005'; S = list(range(650, 656))
if __name__ == '__main__':
    ch = json.load(open(D / 'sel/choice.json'))['choice']; a, b = (float(x) for x in ch.split(',')); Rt = {**rows(CS / 'n4_20261005/sel'), **rows(D / 'sel')}; tab = {}
    for nm, pre in (('one-shot', 'T'), ('refit', 'TR')):
        tg = lambda k: f'{pre}_a{a:g}_b{b:g}_k{k}'.replace('.', 'p')
        fa = np.mean([100 * (np.mean([Rt[tg(k)][s]['fuel_agent'] for s in S]) / np.mean([Rt[f'R_k{k}'][s]['fuel_agent'] for s in S]) - 1) for k in (0, 1)])
        d = {q: float(np.mean([Rt[tg(k)][s][q] - Rt[f'R_k{k}'][s][q] for k in (0, 1) for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')}
        tab[nm] = dict(fuel=float(fa), **d); print(f'{nm:9s}: fuel {fa:+6.2f} | city {d["timeloss"]:+5.2f} agent {d["timeloss_agent"]:+5.2f} human {d["timeloss_human"]:+5.2f}')
    ok = [c for c, v in tab.items() if v['timeloss_agent'] <= 0.2 and v['timeloss'] <= 0.2 and v['timeloss_human'] <= 0.2]
    pick = min(ok, key=lambda c: (tab[c]['fuel'], c != 'one-shot')) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], c != 'one-shot'))
    (D / 'sel' / 'variant.json').write_text(json.dumps(dict(choice=ch, variant=pick, qualified=ok, table=tab), indent=1)); print('VARIANT', pick)
