#!/usr/bin/env python3
"""TSI-2 per-light adapter tuning (PROTOCOL_CITY_TSI2_20261005): TUNE seeds 660-663, fleet s13; rows tsi2_20261005/tune/{R_t<t>, T_t<t>_a<A>_b<B>}.
Rule per light: agent TL <= -0.25 and city / human TL <= 0 (points vs R) -> max fuel saving; else min agent TL; ties smaller A + B."""
import json, sys
from pathlib import Path
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from scripts.CITY_spatp_report import rows  # noqa: E402
D = Path(__file__).resolve().parents[1] / 'research/city_sim/tsi2_20261005'; S = [660, 661, 662, 663]
GRID = [(1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5)]
tag = lambda t, a, b: f'T_t{t}_a{a:g}_b{b:g}'.replace('.', 'p')
if __name__ == '__main__':
    Rt = rows(D / 'tune'); out = {}
    for t in (4, 5, 6, 7, 8):
        R = Rt[f'R_t{t}']; tab = {}
        for a, b in GRID:
            X = Rt[tag(t, a, b)]; fa = 100 * (np.mean([X[s]['fuel_agent'] for s in S]) / np.mean([R[s]['fuel_agent'] for s in S]) - 1)
            tab[f'{a:g},{b:g}'] = dict(fuel=float(fa), **{q: float(np.mean([X[s][q] - R[s][q] for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')})
        ok = [c for c, v in tab.items() if v['timeloss_agent'] <= -0.25 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
        key = lambda c: sum(float(x) for x in c.split(','))
        ch = min(ok, key=lambda c: (tab[c]['fuel'], key(c))) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], key(c)))
        out[t] = dict(choice=ch, qualified=ok, table=tab); print(f't{t}: choice {ch} (qualified {len(ok)}) -> ' + ' '.join(f'{k}:{v:+.2f}' for k, v in tab[ch].items()))
    (D / 'tune' / 'choice.json').write_text(json.dumps(out, indent=1))
