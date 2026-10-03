#!/usr/bin/env python3
"""Report of PROTOCOL_E3_HOLD_DOSE_20261001.md (EXPLORATORY): gain vs Z by (K, r) against the channel-only burden B_3."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); P = M / 'e3_hold_dose_20261001'
DEV = [f'seed{s}_load{h}' for s in (901, 902, 903, 904) for h in (8, 16)]
B3 = {(1, 1): 8.48, (2, 1): 1.64, (2, 2): 2.21, (2, 3): 5.31, (2, 4): 8.10, (2, 6): 11.95, (3, 1): 0.0, (3, 4): 3.20, (3, 6): 5.95}


def tot(path, rule=None):
    return sum(x['queue_sum'] for x in json.loads(Path(path).read_text()) if (rule is None or x.get('rule') == rule) and x['episode'] in DEV)


def main():
    Z = {s: tot(M / f'e3_dev_Z_20261001/Z_s{s}/rows.json', 'none') for s in range(10)}
    L = ['K | r | B_3 | mean gain vs Z | seeds < 0 | per seed']; cells = {}
    for (K, r), b in B3.items():
        g = []
        for s in range(10):
            f = (M / f'e3_negflip_20261001/s{s}_K{K}/rows.json') if r == 1 else (P / f'K{K}_r{r}_s{s}/rows.json')
            if r != 1 and not (P / f'K{K}_r{r}_s{s}/manifest.json').exists():
                print('INCOMPLETE', K, r, s); return
            g.append(-(tot(f) / Z[s] - 1) * 100)
        cells[(K, r)] = g
        L.append(f'{K} | {r} | {b:.2f} | {np.mean(g):+.2f} % | {sum(x < 0 for x in g)}/10 | ' + ' '.join(f'{x:+.2f}' for x in g))
    keys = list(B3); rho = float(spearmanr([B3[k] for k in keys], [np.mean(cells[k]) for k in keys]).correlation)
    k24 = cells[(2, 4)]
    L += [f'Spearman(B_3, mean gain) over {len(keys)} cells = {rho:+.3f} (kill if > -0.5)',
          f'K = 2 / r = 4: mean {np.mean(k24):+.2f} %, positive on {sum(x > 0 for x in k24)}/10 seeds (kill if >= 7)']
    text = '\n'.join(L); print(text)
    (M / 'e3_hold_dose_report_20261001.json').write_text(json.dumps({f'K{k[0]}_r{k[1]}': v for k, v in cells.items()} | {'rho': rho}, indent=1))
    (M / 'e3_hold_dose_report_20261001.txt').write_text('EXPLORATORY\n' + text + '\n')


if __name__ == '__main__':
    main()
