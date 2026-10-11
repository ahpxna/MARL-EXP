#!/usr/bin/env python3
"""W10-6 adapter calibration with an extended grid (PROTOCOL_CITY_WAVE10_20261005, A3): CITY_w7_tune.py's registered rule unchanged (agent TL
<= -0.25, city / human TL <= 0 vs R -> max fuel saving; else min agent TL; ties smaller A + B), the grid from env W10_GRID ("a:b,a:b,...").
Usage: W10_GRID=... CITY_w10_tune_grid.py <dir containing tune/> <t> [<t> ...]   (W10_TUNE_SEEDS=660 for a smoke)"""
import json, os, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
S = [int(x) for x in os.environ.get('W10_TUNE_SEEDS', '660,661,662,663').split(',')]
GRID = [tuple(float(v) for v in x.split(':')) for x in os.environ['W10_GRID'].split(',')]
tag = lambda t, a, b: f'T_t{t}_a{a:g}_b{b:g}'.replace('.', 'p')  # noqa: E731
if __name__ == '__main__':
    D = Path(sys.argv[1]); LT = [int(x) for x in sys.argv[2:]]; Rt = rows(D / 'tune'); out = {}
    for t in LT:
        R = Rt[f'R_t{t}']; tab = {}
        for a, b in GRID:
            X = Rt[tag(t, a, b)]; fa = 100 * (np.mean([X[s]['fuel_agent'] for s in S]) / np.mean([R[s]['fuel_agent'] for s in S]) - 1)
            tab[f'{a:g},{b:g}'] = dict(fuel=float(fa), **{q: float(np.mean([X[s][q] - R[s][q] for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, v in tab.items() if v['timeloss_agent'] <= -0.25 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        key = lambda c: sum(float(x) for x in c.split(','))  # noqa: E731
        ch = min(ok, key=lambda c: (tab[c]['fuel'], key(c))) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], key(c)))
        out[t] = dict(choice=ch, qualified=ok, table=tab, grid=os.environ['W10_GRID'])
        print(f't{t}: choice {ch} (qualified {len(ok)}) -> ' + ' '.join(f'{k}:{v:+.2f}' for k, v in tab[ch].items()))
    (D / 'tune' / 'choice.json').write_text(json.dumps(out, indent=1))
