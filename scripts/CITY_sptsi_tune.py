#!/usr/bin/env python3
"""Spider TSI per-light calibration (PROTOCOL_CITY_SPIDER_TSI_20261005): TUNE 1100-1103; rule as TSI-2."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
import os
D = Path(__file__).resolve().parents[1] / 'research/city_sim/sptsi_20261005'; S = [1100, 1101, 1102, 1103]; TD = os.environ.get('TUNE_DIR', 'tune')
GRID = [(0, 0), (1, 0), (2, 0), (1, 0.25), (1.5, 0.25), (1, 0.5), (2, 0.5)] if os.environ.get('TUNE_DIR', 'tune') == 'tune' else [(1, 0.75), (2, 0.75), (1, 1.0), (2, 1.0), (1, 0.5), (2, 0.5)]; tag = lambda k, a, b: f'T_{k}_a{a:g}_b{b:g}'.replace('.', 'p')
if __name__ == '__main__':
    Rt = {**rows(D / 'tune'), **rows(D / TD)}; out = {}
    for k in (11, 111):
        R = Rt[f'R_{k}']; tab = {}
        for a, b in GRID:
            X = Rt[tag(k, a, b)]; fa = 100 * (np.mean([X[s]['fuel_agent'] for s in S]) / np.mean([R[s]['fuel_agent'] for s in S]) - 1)
            tab[f'{a:g},{b:g}'] = dict(fuel=float(fa), **{q: float(np.mean([X[s][q] - R[s][q] for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, v in tab.items() if v['timeloss_agent'] <= -0.25 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        key = lambda c: sum(float(x) for x in c.split(','))
        ch = min(ok, key=lambda c: (tab[c]['fuel'], key(c))) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], key(c)))
        out[k] = dict(choice=ch, qualified=ok, table=tab); print(f'RLK{k}: choice {ch} (qualified {len(ok)}) -> ' + ' '.join(f'{kk}:{v:+.2f}' for kk, v in tab[ch].items()))
        for c, v in tab.items():
            print(f'   {c:9s} ' + ' '.join(f'{kk}:{vv:+.2f}' for kk, vv in v.items()))
    (D / TD / 'choice.json').write_text(json.dumps(out, indent=1))
