#!/usr/bin/env python3
"""W9-5 (c) calibration budget (PROTOCOL_CITY_WAVE9_20261005), offline: the registered per-light selection rule of CITY_tsi2_tune / CITY_w7_tune
(agent TL <= -0.25 and city / human TL <= 0 vs R -> max fuel saving; else min agent TL; ties smaller A + B), re-applied on every subset of 1, 2 and 3
of the 4 TUNE seeds (660-663), for every light with a complete 4-seed grid.  Reports the share of subsets that reproduce the 4-seed choice and the
share whose choice lies in the 4-seed qualified set; also, per light, whether the global (1, 0.5) is qualified with all 4 seeds.  Descriptive."""
import itertools, sys
from pathlib import Path
import numpy as np
ROOT = Path(__file__).resolve().parents[1]; sys.path.insert(0, str(ROOT))
from scripts.CITY_spatp_report import rows  # noqa: E402
GRID = [(1, 0), (1.5, 0), (2, 0), (1, 0.25), (1.5, 0.25), (2, 0.25), (1, 0.5), (1.5, 0.5), (2, 0.5), (3, 0.5)]; S4 = [660, 661, 662, 663]
tag = lambda t, a, b: f'T_t{t}_a{a:g}_b{b:g}'.replace('.', 'p')  # noqa: E731
CS = ROOT / 'research/city_sim'
SETS = [('TSI-2 (t4-t8)', CS / 'tsi2_20261005', (4, 5, 6, 7, 8)), ('W7-1 (t9-t13)', CS / 'w7_20261005/fpr', (9, 10, 11, 12, 13)),
        ('W8-2 (t14-t18)', CS / 'w8_20261005/fresh2', (14, 15, 16, 17, 18))]


def select(Rt, t, S):
    R = Rt[f'R_t{t}']; tab = {}
    for a, b in GRID:
        X = Rt[tag(t, a, b)]; fa = 100 * (np.mean([X[s]['fuel_agent'] for s in S]) / np.mean([R[s]['fuel_agent'] for s in S]) - 1)
        tab[f'{a:g},{b:g}'] = dict(fuel=fa, **{q: float(np.mean([X[s][q] - R[s][q] for s in S])) for q in ('timeloss', 'timeloss_agent', 'timeloss_human')})
    ok = [c for c, v in tab.items() if v['timeloss_agent'] <= -0.25 and v['timeloss'] <= 0 and v['timeloss_human'] <= 0]
    key = lambda c: sum(float(x) for x in c.split(','))  # noqa: E731
    ch = min(ok, key=lambda c: (tab[c]['fuel'], key(c))) if ok else min(tab, key=lambda c: (tab[c]['timeloss_agent'], key(c)))
    return ch, ok


if __name__ == '__main__':
    out = ['== W9-5 (c) calibration budget: the registered selection rule on subsets of the 4 TUNE seeds (descriptive)']
    tot = {n: [0, 0, 0] for n in (1, 2, 3)}; gq = []
    for name, D, LT in SETS:
        if not (D / 'tune').exists():
            out.append(f'  {name}: no tuning directory'); continue
        Rt = rows(D / 'tune')
        if not all(f'R_t{t}' in Rt and all(tag(t, a, b) in Rt for a, b in GRID) and all(s in Rt[f'R_t{t}'] for s in S4) for t in LT):
            out.append(f'  {name}: grid incomplete, skipped'); continue
        for t in LT:
            c4, q4 = select(Rt, t, S4); gq.append('1,0.5' in q4); line = []
            for n in (1, 2, 3):
                sub = list(itertools.combinations(S4, n)); same = sum(select(Rt, t, list(c))[0] == c4 for c in sub); inq = sum(select(Rt, t, list(c))[0] in q4 for c in sub)
                tot[n][0] += same; tot[n][1] += inq; tot[n][2] += len(sub); line.append(f'{n} seed(s): same {same}/{len(sub)}, in qualified set {inq}/{len(sub)}')
            out.append(f'  {name} t{t}: 4-seed choice {c4} (qualified {len(q4)}; (1, 0.5) qualified: {"1,0.5" in q4}) | ' + ' | '.join(line))
    for n in (1, 2, 3):
        s, q, m = tot[n]; out.append(f'  ALL lights, {n} of 4 TUNE seeds: same choice {s}/{m} ({100 * s / max(1, m):.0f} %), choice qualified with 4 seeds {q}/{m} ({100 * q / max(1, m):.0f} %)')
    out.append(f'  global (1, 0.5) qualified on {sum(gq)}/{len(gq)} lights with the 4 TUNE seeds')
    print('\n'.join(out))
