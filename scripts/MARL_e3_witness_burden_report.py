#!/usr/bin/env python3
"""Report of PROTOCOL_E3_COMPAT_MAP_20261001.md Part C (written before the runs; EXPLORATORY: the cell gains are known).
Per order x capacity cell (seeds 0-9, development episodes): D = mean over receiver-steps of sum_j witness_j (a_j - 3)+,
B_3 from the parity flags, witness rate by age, D / B_3; W1: |Spearman(D, gain)| >= |Spearman(B_3, gain)| over the nine
cells and D / B_3 smaller for the congestion cells than for the age-first cells.  Gains as MARL_e3_order_dose_report.py."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); W = M / 'e3_witness_burden_20261001'; S = range(10); STEPS = 1872
CELLS = [('prefix', 'iid'), ('prefix', 'cap4'), ('prefix', 'low'), ('agefirst', 'cap4'), ('agefirst', 'low'), ('agefirst', 'iid'),
         ('agefirst', 'const1'), ('agefirst', 'const2'), ('agefirst', 'const3')]


def parity_dir(o, c, s):
    if (o, c) in CELLS[:5]:
        return M / f'e3_order_dose_20261001/{o}_{c}_s{s}'
    return M / f'e3_viewstats_v2_20261001/s{s}_K{0 if c == "iid" else int(c[5:])}'


def gains():
    rp = json.loads((M / 'e3_ten_seed_panel_report_20261001.json').read_text())
    g = {('agefirst', c): float(np.mean([-rp['per_seed'][str(s)]['cells'][c][0] for s in S])) for c in ('iid', 'cap4', 'low')}
    g.update({('prefix', c): float(np.mean([-rp['secondary'][f'congestion order vs Z/{c}']['per_seed'][str(s)] for s in S])) for c in ('iid', 'cap4', 'low')})
    G1 = {int(s): v for s, v in json.loads((M / 'e3_demand_frontier_report_20261001.json').read_text())['gain'].items()}
    for K in (1, 2, 3):
        g[('agefirst', f'const{K}')] = float(np.mean([G1[s][K - 1] for s in S]))
    return g


def main():
    g = gains(); L = ['order | capacity | B_3 | D (witness burden) | D / B_3 | witness rate a=1-2 / 3-4 / 5-8 / >=9 | gain vs Z']; out = {}
    for o, c in CELLS:
        ds = [W / f'{o}_{c}_s{s}' for s in S]
        if not all((d / 'manifest.json').exists() for d in ds):
            L.append(f'{o} | {c} | INCOMPLETE'); continue
        D, B, rates = [], [], {k: [] for k in ('1-2', '3-4', '5-8', '>=9')}
        for s, d in zip(S, ds):
            z = np.load(d / 'witness.npz'); f = np.load(parity_dir(o, c, s) / 'flags.npz')
            D.append(float((z['witness'] * np.maximum(z['age'] - 3, 0)).sum() / STEPS)); B.append(float(f['b3'].mean()))
            for k, (lo, hi) in {'1-2': (1, 2), '3-4': (3, 4), '5-8': (5, 8), '>=9': (9, 99)}.items():
                sel = (z['age'] >= lo) & (z['age'] <= hi)
                if sel.sum() >= 50:
                    rates[k].append(float(z['witness'][sel].mean()))
        Dm, Bm = float(np.mean(D)), float(np.mean(B)); rr = {k: (float(np.mean(v)) if v else None) for k, v in rates.items()}
        out[(o, c)] = dict(D=Dm, B3=Bm, ratio=(Dm / Bm if Bm > 1e-9 else None), rates=rr, gain=g[(o, c)])
        L.append(f'{o} | {c} | {Bm:.2f} | {Dm:.3f} | ' + (f'{Dm / Bm:.3f}' if Bm > 1e-9 else '-') + ' | '
                 + ' / '.join('-' if v is None else f'{v:.3f}' for v in rr.values()) + f' | {g[(o, c)]:+.2f} %')
    if len(out) == len(CELLS):
        ks = list(out); gg = [out[k]['gain'] for k in ks]
        rD = float(spearmanr([out[k]['D'] for k in ks], gg).correlation); rB = float(spearmanr([out[k]['B3'] for k in ks], gg).correlation)
        rc = [out[k]['ratio'] for k in ks if k[0] == 'prefix' and k[1] in ('cap4', 'low')]
        ra = [out[k]['ratio'] for k in ks if k[0] == 'agefirst' and out[k]['ratio'] is not None]
        W1 = abs(rD) >= abs(rB) and rc and ra and max(rc) < min(ra)
        L += [f'Spearman(D, gain) {rD:+.3f} vs Spearman(B_3, gain) {rB:+.3f}; D/B_3 congestion cap4/low {rc} vs age-first {ra}',
              f'W1 -> {"SUPPORTED" if W1 else "NOT SUPPORTED"} (exploratory: gains known)']
    text = '\n'.join(L); print(text); (M / 'e3_witness_burden_report_20261001.txt').write_text(text + '\n')
    (M / 'e3_witness_burden_report_20261001.json').write_text(json.dumps({f'{o}|{c}': v for (o, c), v in out.items()}, indent=1))


if __name__ == '__main__':
    main()
