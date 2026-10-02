#!/usr/bin/env python3
"""Report of PROTOCOL_E3_HOLD_PROSPECTIVE_20261001.md (written before the runs).
HD1 relay(K=2, r=4) vs relay(K=2, r=1) mean < 0, upper bound < 0; HD2 relay(K=2, r=4) vs Z mean < 0; HD3 Spearman(B_3, mean gain)
over six cells <= -0.6; HD4 Spearman over seeds of gain(K=2, r=4) with the mean const-K=1 gain over 2801/3001/3101 >= 0.5.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); P = M / 'e3_hold_prospective_20261001'; SEEDS = list(range(10))
EPS = [f'seed{s}_load{h}' for s in range(3501, 3565) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
CELLS = {(2, 1): 1.64, (2, 3): 5.31, (2, 4): 8.10, (2, 6): 11.95, (3, 1): 0.0, (3, 6): 5.95}


def load(tag, rule, ckpt):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    assert f'{ckpt}/ckpt_best.pt' in str(m.get('args')), tag
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
    assert sorted(rows) == sorted(EPS), f'{tag}: {len(rows)} episodes'
    return np.array([rows[e] for e in EPS], float)


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


def boot(X, Y):
    rng = np.random.default_rng(0); bs = []
    for _ in range(4000):
        ss = rng.choice(SEEDS, len(SEEDS))
        bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [float(v) for v in np.percentile(bs, [2.5, 97.5])]


def main():
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in SEEDS}
    R = {(s, K, r): load(f'R_s{s}_K{K}_r{r}', f'hold{r}', f'relay6Cage_st_s{s}') for s in SEEDS for (K, r) in CELLS}
    if any(v is None for v in Z.values()) or any(v is None for v in R.values()):
        print('INCOMPLETE'); return
    L = ['K | r | B_3 | gain vs Z (mean, 95 %) | per seed']; out = {}
    for (K, r), b in CELLS.items():
        X = {s: R[(s, K, r)] for s in SEEDS}; g = [gain(X[s], Z[s]) for s in SEEDS]; ci = boot(X, Z)
        out[f'K{K}_r{r}'] = dict(gain=g, ci=ci, B3=b)
        L.append(f'{K} | {r} | {b:.2f} | {np.mean(g):+.2f} % {ci} | ' + ' '.join(f'{x:+.2f}' for x in g))
    X4 = {s: R[(s, 2, 4)] for s in SEEDS}; X1 = {s: R[(s, 2, 1)] for s in SEEDS}
    d41 = [gain(X4[s], X1[s]) for s in SEEDS]; ci41 = boot(X4, X1)
    HD1 = np.mean(d41) < 0 and ci41[1] < 0; HD2 = np.mean(out['K2_r4']['gain']) < 0
    rho = float(spearmanr([CELLS[k] for k in CELLS], [np.mean(out[f'K{k[0]}_r{k[1]}']['gain']) for k in CELLS]).correlation); HD3 = rho <= -0.6
    G1 = {int(s): v for s, v in json.loads((M / 'e3_demand_frontier_report_20261001.json').read_text())['gain'].items()}
    G3 = {int(s): v for s, v in json.loads((M / 'e3_harm_prospective_report_20261001.json').read_text())['gain'].items()}
    A = json.loads((M / 'e3_ageclip_prospective_report_20261001.json').read_text())['const K = 1']['none_vs_Z']
    k1 = [np.mean([G1[s][0], G3[s][0], A[s]]) for s in SEEDS]
    r4 = float(spearmanr(out['K2_r4']['gain'], k1).correlation); HD4 = r4 >= 0.5
    L += [f'HD1 relay r=4 vs r=1 at K=2: {np.mean(d41):+.2f} % {ci41} -> {"SUPPORTED" if HD1 else "NOT SUPPORTED"}',
          f'HD2 relay(K=2, r=4) vs Z: {np.mean(out["K2_r4"]["gain"]):+.2f} % -> {"SUPPORTED" if HD2 else "NOT SUPPORTED"}',
          f'HD3 Spearman(B_3, mean gain) over 6 cells {rho:+.3f} <= -0.6 -> {"SUPPORTED" if HD3 else "NOT SUPPORTED"}',
          f'HD4 Spearman(gain(K=2, r=4), mean const-K=1 gain) {r4:+.3f} >= 0.5 -> {"SUPPORTED" if HD4 else "NOT SUPPORTED"}']
    out.update(HD1=bool(HD1), HD2=bool(HD2), HD3=bool(HD3), HD4=bool(HD4), d41=d41, ci41=ci41, rho=rho, r4=r4)
    text = '\n'.join(L); print(text)
    (M / 'e3_hold_prospective_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_hold_prospective_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
