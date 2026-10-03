#!/usr/bin/env python3
"""Report of PROTOCOL_E3_MISMATCH_LAW_20261002.md (written before the runs).  ML1–ML4 as in the protocol."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); P = M / 'e3_mismatch_law_20261002'; SEEDS = (0, 1, 2, 3)
EPS = [f'seed{s}_load{h}' for s in range(3701, 3765) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
CAPS = (1, 2, 3, 0); NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}
X = {'relay6Cage_st': {1: 2.837, 2: 1.107, 3: 0.366, 0: 0.0}, 'relayCK1_st': {1: 0.0, 2: 1.730, 3: 2.472, 0: 2.837}}


def load(tag, rule):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
    assert sorted(rows) == sorted(EPS), f'{tag}: {len(rows)} episodes'
    return np.array([rows[e] for e in EPS], float)


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


def boot(Xs, Ys):
    rng = np.random.default_rng(0); bs = []
    for _ in range(4000):
        ss = rng.choice(SEEDS, len(SEEDS))
        bs.append(np.mean([gain(Xs[s], Ys[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]


def main():
    Z = {s: load(f'Z_s{s}', 'none') for s in SEEDS}
    R = {(a, s, K): load(f'R_{a}_s{s}_K{K}', 'prefix') for a in X for s in SEEDS for K in CAPS}
    if any(v is None for v in Z.values()) or any(v is None for v in R.values()):
        print('INCOMPLETE'); return
    G = {}; L = ['student | capacity | mismatch x | gain vs Z (mean, 95 %) | per seed']
    for a in X:
        for K in CAPS:
            g = [gain(R[(a, s, K)], Z[s]) for s in SEEDS]; G[(a, K)] = float(np.mean(g))
            L.append(f'{a} | {NAME[K]} | {X[a][K]:.3f} | {np.mean(g):+.2f} % {boot({s: R[(a, s, K)] for s in SEEDS}, Z)} | ' + ' '.join(f'{v:+.2f}' for v in g))
    r = {a: float(spearmanr([X[a][K] for K in CAPS], [G[(a, K)] for K in CAPS]).correlation) for a in X}
    ML1 = all(v <= -0.8 for v in r.values())
    ML2 = G[('relayCK1_st', 0)] < G[('relayCK1_st', 2)] < G[('relayCK1_st', 1)]
    ML3 = G[('relayCK1_st', 1)] > G[('relay6Cage_st', 1)] and all(G[('relay6Cage_st', K)] > G[('relayCK1_st', K)] for K in (2, 3, 0))
    rp = float(spearmanr([X[a][K] for a in X for K in CAPS], [G[(a, K)] for a in X for K in CAPS]).correlation); ML4 = rp <= -0.7
    L += [f'ML1 Spearman(x, gain) per student: ' + ', '.join(f'{a} {v:+.3f}' for a, v in r.items()) + f' -> {"SUPPORTED" if ML1 else "NOT SUPPORTED"}',
          f'ML2 relayCK1 iid {G[("relayCK1_st", 0)]:+.2f} < K=2 {G[("relayCK1_st", 2)]:+.2f} < K=1 {G[("relayCK1_st", 1)]:+.2f} -> {"SUPPORTED" if ML2 else "NOT SUPPORTED"}',
          f'ML3 crossing between K = 1 and K = 2 -> {"SUPPORTED" if ML3 else "NOT SUPPORTED"}',
          f'ML4 pooled Spearman(x, gain) over 8 cells {rp:+.3f} (need <= -0.7) -> {"SUPPORTED" if ML4 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (M / 'e3_mismatch_law_report_20261002.txt').write_text(text + '\n')
    (M / 'e3_mismatch_law_report_20261002.json').write_text(json.dumps({f'{a}|{K}': v for (a, K), v in G.items()}, indent=1))


if __name__ == '__main__':
    main()
