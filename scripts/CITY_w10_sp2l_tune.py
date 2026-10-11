#!/usr/bin/env python3
"""W10-4 per-light adapter calibration on spider-2L (PROTOCOL_CITY_WAVE10_20261005, A2): CITY_sptsi_tune.py's rule and attempt-1 grid, with the
directory as an argument.  Usage: CITY_w10_sp2l_tune.py <dir with tune/>   (W10_TUNE_SEEDS=1100 for a smoke)"""
import json, os, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
S = [int(x) for x in os.environ.get('W10_TUNE_SEEDS', '1100,1101,1102,1103').split(',')]
GRID = [(0, 0), (1, 0), (2, 0), (1, 0.25), (1.5, 0.25), (1, 0.5), (2, 0.5)]
tag = lambda k, a, b: f'T_{k}_a{a:g}_b{b:g}'.replace('.', 'p')  # noqa: E731
if __name__ == '__main__':
    D = Path(sys.argv[1]); Rt = rows(D / 'tune'); out = {}
    for k in (11, 111):
        if f'R_{k}' not in Rt:
            continue
        R = Rt[f'R_{k}']; tab = {}
        for a, b in GRID:
            X = Rt[tag(k, a, b)]; fa = 100 * (np.mean([X[s]['fuel_agent'] for s in S]) / np.mean([R[s]['fuel_agent'] for s in S]) - 1)
            tab[f'{a:g},{b:g}'] = dict(fuel=float(fa), **{q: float(np.mean([X[s][q] - R[s][q] for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, v in tab.items() if v['timeloss_agent'] <= -0.25 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        key = lambda c: sum(float(x) for x in c.split(','))  # noqa: E731
        ch = min(ok, key=lambda c: (tab[c]['fuel'], key(c))) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], key(c)))
        out[k] = dict(choice=ch, qualified=ok, table=tab); print(f'{k}: choice {ch} (qualified {len(ok)}) -> ' + ' '.join(f'{q}:{v:+.2f}' for q, v in tab[ch].items()))
    (D / 'tune' / 'choice.json').write_text(json.dumps(out, indent=1))
