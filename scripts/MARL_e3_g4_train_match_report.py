#!/usr/bin/env python3
"""Report of PROTOCOL_E3_G4_TRAIN_MATCH_20261002.md (written 12:54:59 EDT, before any run).  4x4, panel 4201-4264, seeds 0-9.
GTM1 relayCK1 vs Z at K = 1 (mean >= 0, lower > -0.5); GTM2 relayCK1 vs relayCage at K = 1 (lower > 0); GTM3 relayCK1 iid < K = 1;
GTM4 Pearson(predicted, observed) of d(K) - d(K1) >= 0.9 (predicted 0 / 2.56 / 6.53 / 9.23); GTM5 onefresh vs plain at iid > 0
with recovery < 0.5 (exploratory)."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_g4_train_match_20261002'; SEEDS = list(range(10))
EPS = [f'seed{s}_load{h}' for s in range(4201, 4265) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}; PRED = {1: 0.0, 2: 2.56, 3: 6.53, 0: 9.23}


def load(tag, rule, ckpt_name):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    assert f'{ckpt_name}/ckpt_best.pt' in str(m.get('args')), tag
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
    return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]


def main():
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in SEEDS}
    R = {(a, s, K): load(f'R_{a}_s{s}_K{K}', 'prefix', f'{a}_s{s}') for a in ('relayCK1_st', 'relayCage_st') for s in SEEDS for K in (1, 2, 3, 0)}
    J = {(s, K): load(f'J_relayCK1_st_s{s}_K{K}', 'projectonefresh', f'relayCK1_st_s{s}') for s in SEEDS for K in (2, 3, 0)}
    allv = list(Z.values()) + list(R.values()) + list(J.values())
    if any(v is None for v in allv):
        print(f'INCOMPLETE: {sum(v is None for v in allv)} of {len(allv)} items missing'); return
    G = {}; L = ['arm | capacity | gain vs Z (95 %) | per seed']
    for a in ('relayCK1_st', 'relayCage_st'):
        for K in (1, 2, 3, 0):
            g = [gain(R[(a, s, K)], Z[s]) for s in SEEDS]; G[(a, K)] = float(np.mean(g))
            L.append(f'{a} | {NAME[K]} | {np.mean(g):+.2f} % {boot({s: R[(a, s, K)] for s in SEEDS}, Z)} | ' + ' '.join(f'{v:+.2f}' for v in g))
    c1 = boot({s: R[('relayCK1_st', s, 1)] for s in SEEDS}, Z)
    m12 = [gain(R[('relayCK1_st', s, 1)], R[('relayCage_st', s, 1)]) for s in SEEDS]
    c12 = boot({s: R[('relayCK1_st', s, 1)] for s in SEEDS}, {s: R[('relayCage_st', s, 1)] for s in SEEDS})
    GTM1 = G[('relayCK1_st', 1)] >= 0 and c1[0] > -0.5; GTM2 = c12[0] > 0; GTM3 = G[('relayCK1_st', 0)] < G[('relayCK1_st', 1)]
    d = {K: G[('relayCage_st', K)] - G[('relayCK1_st', K)] for K in (1, 2, 3, 0)}; dc = {K: d[K] - d[1] for K in d}
    o = np.array([dc[K] for K in (1, 2, 3, 0)]); p = np.array([PRED[K] for K in (1, 2, 3, 0)])
    r = float(np.corrcoef(o, p)[0, 1]); GTM4 = r >= 0.9
    xdiff = {1: 3.688, 2: 1.642, 3: -1.530, 0: -3.688}; slope = float(np.polyfit([xdiff[K] for K in (1, 2, 3, 0)], [d[K] for K in (1, 2, 3, 0)], 1)[0])
    ej = [gain(J[(s, 0)], R[('relayCK1_st', s, 0)]) for s in SEEDS]; gj = float(np.mean([gain(J[(s, 0)], Z[s]) for s in SEEDS]))
    fr = (gj - G[('relayCK1_st', 0)]) / (G[('relayCage_st', 0)] - G[('relayCK1_st', 0)]); GTM5 = float(np.mean(ej)) > 0 and fr < 0.5
    L += [f'relayCK1 vs relayCage at K = 1: {np.mean(m12):+.2f} % {c12} | ' + ' '.join(f'{v:+.2f}' for v in m12),
          'd(K) - d(K1) observed / predicted: ' + ', '.join(f'{NAME[K]} {dc[K]:+.2f} / {PRED[K]:+.2f}' for K in (1, 2, 3, 0)),
          'onefresh vs plain (relayCK1): ' + ', '.join(f'{NAME[K]} {np.mean([gain(J[(s, K)], R[("relayCK1_st", s, K)]) for s in SEEDS]):+.2f} %' for K in (2, 3, 0)),
          f'GTM1 rescue at K = 1: {G[("relayCK1_st", 1)]:+.2f} % {c1} -> {"SUPPORTED" if GTM1 else "NOT SUPPORTED"}',
          f'GTM2 matching helps at K = 1 (lower > 0) -> {"SUPPORTED" if GTM2 else "NOT SUPPORTED"}',
          f'GTM3 upgrade hurts: relayCK1 iid {G[("relayCK1_st", 0)]:+.2f} < K = 1 {G[("relayCK1_st", 1)]:+.2f} -> {"SUPPORTED" if GTM3 else "NOT SUPPORTED"}',
          f'GTM4 W1 law (Pearson {r:+.3f}, need >= 0.9) -> {"SUPPORTED" if GTM4 else "NOT SUPPORTED"}; fitted 4x4 slope {-slope:.3f} % per W1 unit (3x3: 1.252)',
          f'GTM5 onefresh at iid: effect {np.mean(ej):+.2f} %, recovery {fr:.2f} (need effect > 0, recovery < 0.5) -> {"SUPPORTED" if GTM5 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (M / 'e3_g4_train_match_report_20261002.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
