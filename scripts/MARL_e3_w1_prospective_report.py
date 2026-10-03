#!/usr/bin/env python3
"""Report of PROTOCOL_E3_W1_PROSPECTIVE_20261002.md (written 02/10/2026 11:44:41 EDT, before any run).  Panel 3901-3964 x 8/16,
seeds 0-4.  d(K) = gain(relayCK2) - gain(relay6Cage), e(K) = gain(relayCK2) - gain(relayCK1) (gains vs Z, mean over seeds).
W1a signs of d(K) - d(iid) for K = 1, 2, 3; W1b Pearson >= 0.9 and max |error| <= 1.0 for d - d(iid) and for e - e(K1);
W1c |d(K1) - d(K2)| < |d(K2) - d(K3)|; W1d (reported) the K at which relayCK2's own gain vs Z peaks."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_w1_prospective_20261002'; SEEDS = list(range(5))
EPS = [f'seed{s}_load{h}' for s in range(3901, 3965) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
CAPS = (1, 2, 3, 0); NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}; ARMS = ('relayCK2_st', 'relay6Cage_st', 'relayCK1_st')
PRED_D = {1: 2.77, 2: 2.77, 3: 0.92, 0: 0.0}; PRED_E = {1: 0.0, 2: 4.34, 3: 4.34, 0: 4.34}   # frozen in the protocol


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


def score(obs, pred):
    o = np.array([obs[K] for K in CAPS]); p = np.array([pred[K] for K in CAPS])
    return float(np.corrcoef(o, p)[0, 1]), float(np.max(np.abs(o - p)))


def main():
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in SEEDS}
    R = {(a, s, K): load(f'R_{a}_s{s}_K{K}', 'prefix', f'{a}_s{s}') for a in ARMS for s in SEEDS for K in CAPS}
    miss = [k for k, v in list(Z.items()) + list(R.items()) if v is None]
    if miss:
        print(f'INCOMPLETE: {len(miss)} of {len(Z) + len(R)} items missing'); return
    G = {}; L = ['arm | capacity | gain vs Z mean (95 %) | per seed']
    for a in ARMS:
        for K in CAPS:
            g = [gain(R[(a, s, K)], Z[s]) for s in SEEDS]; G[(a, K)] = float(np.mean(g))
            L.append(f'{a} | {NAME[K]} | {np.mean(g):+.2f} % {boot({s: R[(a, s, K)] for s in SEEDS}, Z)} | ' + ' '.join(f'{v:+.2f}' for v in g))
    d = {K: G[('relayCK2_st', K)] - G[('relay6Cage_st', K)] for K in CAPS}; e = {K: G[('relayCK2_st', K)] - G[('relayCK1_st', K)] for K in CAPS}
    dc = {K: d[K] - d[0] for K in CAPS}; ec = {K: e[K] - e[1] for K in CAPS}
    W1a = all(dc[K] > 0 for K in (1, 2, 3))
    rd, md = score(dc, PRED_D); re_, me = score(ec, PRED_E); W1b = rd >= 0.9 and md <= 1.0 and re_ >= 0.9 and me <= 1.0
    W1c = abs(d[1] - d[2]) < abs(d[2] - d[3])
    peak = max(CAPS, key=lambda K: G[('relayCK2_st', K)])
    L += ['d(K) - d(iid) observed / predicted: ' + ', '.join(f'{NAME[K]} {dc[K]:+.2f} / {PRED_D[K]:+.2f}' for K in CAPS),
          'e(K) - e(K1) observed / predicted: ' + ', '.join(f'{NAME[K]} {ec[K]:+.2f} / {PRED_E[K]:+.2f}' for K in CAPS),
          f'W1a signs d(K) - d(iid) > 0 at K = 1, 2, 3 -> {"SUPPORTED" if W1a else "NOT SUPPORTED"}',
          f'W1b d: Pearson {rd:+.3f}, max error {md:.2f}; e: Pearson {re_:+.3f}, max error {me:.2f} (need >= 0.9 and <= 1.0) -> {"SUPPORTED" if W1b else "NOT SUPPORTED"}',
          f'W1c |d(K1) - d(K2)| {abs(d[1] - d[2]):.2f} < |d(K2) - d(K3)| {abs(d[2] - d[3]):.2f} -> {"SUPPORTED" if W1c else "NOT SUPPORTED"}',
          f'W1d relayCK2 gain vs Z peaks at {NAME[peak]} (' + ', '.join(f'{NAME[K]} {G[("relayCK2_st", K)]:+.2f}' for K in CAPS) + ')']
    text = '\n'.join(L); print(text); (M / 'e3_w1_prospective_report_20261002.txt').write_text(text + '\n')
    (M / 'e3_w1_prospective_report_20261002.json').write_text(json.dumps(dict(G={f'{a}|{NAME[K]}': v for (a, K), v in G.items()}, d=d, e=e,
                                                                              W1a=W1a, W1b=W1b, W1c=W1c, peak=NAME[peak]), indent=1, default=float))


if __name__ == '__main__':
    main()
