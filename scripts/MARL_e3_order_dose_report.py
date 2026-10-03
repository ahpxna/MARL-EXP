#!/usr/bin/env python3
"""Report of PROTOCOL_E3_ORDER_DOSE_20261001.md (EXPLORATORY): doses and decision flips per (order, capacity) cell vs the
closed-loop gains of the same students (reserved panel 2701 for iid / cap4 / low; panels 2801/3001/3101 for const K)."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget')


def cell_stats(paths):
    v = {k: [] for k in ('b3', 'never', 'flip', 'netz')}
    for p in paths:
        z = np.load(p); v['b3'].append(z['b3'].mean() if 'b3' in z.files else np.nan)
        v['never'].append((z['n_nbr'] - z['n_fresh'] - z['n_relay']).mean()); v['flip'].append((z['zok'] & ~z['protoS']).mean())
        v['netz'].append(z['protoS'].mean() - z['zok'].mean())
    return {k: float(np.nanmean(x)) for k, x in v.items()}


def main():
    rp = json.loads((M / 'e3_ten_seed_panel_report_20261001.json').read_text())
    S = range(10)
    gain = {('agefirst', c): float(np.mean([-rp['per_seed'][str(s)]['cells'][c][0] for s in S])) for c in ('iid', 'cap4', 'low')}
    gain.update({('prefix', c): float(np.mean([-rp['secondary'][f'congestion order vs Z/{c}']['per_seed'][str(s)] for s in S])) for c in ('iid', 'cap4', 'low')})
    G1 = {int(s): v for s, v in json.loads((M / 'e3_demand_frontier_report_20261001.json').read_text())['gain'].items()}
    for K in (1, 2, 3):
        gain[('agefirst', f'const{K}')] = float(np.mean([G1[s][K - 1] for s in S]))
    cells = {}
    for o, c in [('prefix', 'iid'), ('prefix', 'cap4'), ('prefix', 'low'), ('agefirst', 'cap4'), ('agefirst', 'low')]:
        ps = [M / f'e3_order_dose_20261001/{o}_{c}_s{s}/flags.npz' for s in S]
        if not all(p.exists() for p in ps):
            print('INCOMPLETE', o, c); return
        cells[(o, c)] = cell_stats(ps)
    cells[('agefirst', 'iid')] = cell_stats([M / f'e3_viewstats_v2_20261001/s{s}_K0/flags.npz' for s in S])
    for K in (1, 2, 3):
        cells[('agefirst', f'const{K}')] = cell_stats([M / f'e3_viewstats_v2_20261001/s{s}_K{K}/flags.npz' for s in S])
    L = ['order | capacity | B_3 | never-heard | flip_Z | net_Z | closed-loop gain vs Z']
    keys = list(cells)
    for k in keys:
        x = cells[k]; L.append(f'{k[0]} | {k[1]} | {x["b3"]:.2f} | {x["never"]:.2f} | {x["flip"]:.3f} | {x["netz"]:+.3f} | {gain[k]:+.2f} %')
    r_flip = float(spearmanr([cells[k]['flip'] for k in keys], [gain[k] for k in keys]).correlation)
    r_netz = float(spearmanr([cells[k]['netz'] for k in keys], [gain[k] for k in keys]).correlation)
    r_b3 = float(spearmanr([cells[k]['b3'] for k in keys], [gain[k] for k in keys]).correlation)
    L += [f'(i) Spearman(flip_Z, gain) over {len(keys)} cells = {r_flip:+.3f} (predicted <= -0.6) | net_Z {r_netz:+.3f} | B_3 {r_b3:+.3f}',
          '(ii) congestion vs age-first at cap4 / low: B_3 ' + ', '.join(f'{c}: {cells[("prefix", c)]["b3"]:.2f} vs {cells[("agefirst", c)]["b3"]:.2f}' for c in ('cap4', 'low'))
          + ' | never-heard ' + ', '.join(f'{c}: {cells[("prefix", c)]["never"]:.2f} vs {cells[("agefirst", c)]["never"]:.2f}' for c in ('cap4', 'low'))]
    text = '\n'.join(L); print(text)
    (M / 'e3_order_dose_report_20261001.txt').write_text('EXPLORATORY\n' + text + '\n')


if __name__ == '__main__':
    main()
