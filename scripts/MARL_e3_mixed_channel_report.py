#!/usr/bin/env python3
"""Report of PROTOCOL_E3_MIXED_CHANNEL_20261001.md (draft 01/10 21:53, Addendum 1 = activation 02/10 01:48, both before the
runs).  Panel 3801-3864 x 8/16; capacities K = 1, 2, 3 and iid (K = 0).
MX1 relayMIX vs Z at K = 1 (seeds 0-9): mean >= 0 and bootstrap lower bound > -0.5 %.
MX2 relayMIX vs relay6Cage at iid (seeds 0-9): mean >= -0.3 %.
MX3 (seeds 0-4) relayMIX vs relayCK1 at iid mean >= 0 AND at K = 1 mean >= -0.3 %.
MX4 (exploratory) spread max_K - min_K of the mean gain vs Z: relayMIX < relay6Cage and relayMIX < relayCK1 (seeds 0-4 for
the relayCK1 comparison, 0-9 otherwise)."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_mixed_channel_20261002'; S10 = list(range(10)); S5 = list(range(5))
EPS = [f'seed{s}_load{h}' for s in range(3801, 3865) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
CAPS = (1, 2, 3, 0); NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}
ARMS = {'relayMIX_st': S10, 'relay6Cage_st': S10, 'relayCK1_st': S5}


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


def boot(X, Y, seeds):
    rng = np.random.default_rng(0); bs = []
    for _ in range(4000):
        ss = rng.choice(seeds, len(seeds))
        bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]


def main():
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in S10}
    R = {(a, s, K): load(f'R_{a}_s{s}_K{K}', 'prefix', f'{a}_s{s}') for a, ss in ARMS.items() for s in ss for K in CAPS}
    miss = [k for k, v in list(Z.items()) + list(R.items()) if v is None]
    if miss:
        print(f'INCOMPLETE: {len(miss)} of {len(Z) + len(R)} items missing'); return
    L = ['arm | capacity | gain vs Z mean (95 %) | per seed']; G = {}; out = {}
    for a, ss in ARMS.items():
        for K in CAPS:
            g = [gain(R[(a, s, K)], Z[s]) for s in ss]; G[(a, K)] = float(np.mean(g)); out[f'{a}|{NAME[K]}|vsZ'] = g
            L.append(f'{a} | {NAME[K]} | {np.mean(g):+.2f} % {boot({s: R[(a, s, K)] for s in ss}, Z, ss)} | ' + ' '.join(f'{v:+.2f}' for v in g))
    G5 = {(a, K): float(np.mean([gain(R[(a, s, K)], Z[s]) for s in S5])) for a in ARMS for K in CAPS}
    mix = {s: {K: R[('relayMIX_st', s, K)] for K in CAPS} for s in S10}
    k1 = {s: mix[s][1] for s in S10}; ci1 = boot(k1, Z, S10); m1 = G[('relayMIX_st', 1)]
    MX1 = m1 >= 0 and ci1[0] > -0.5
    v6 = [gain(mix[s][0], R[('relay6Cage_st', s, 0)]) for s in S10]; MX2 = float(np.mean(v6)) >= -0.3
    vc0 = [gain(mix[s][0], R[('relayCK1_st', s, 0)]) for s in S5]; vc1 = [gain(mix[s][1], R[('relayCK1_st', s, 1)]) for s in S5]
    MX3 = float(np.mean(vc0)) >= 0 and float(np.mean(vc1)) >= -0.3
    spread = {a: max(G[(a, K)] for K in CAPS) - min(G[(a, K)] for K in CAPS) for a in ARMS}
    spread5 = {a: max(G5[(a, K)] for K in CAPS) - min(G5[(a, K)] for K in CAPS) for a in ARMS}
    MX4 = spread['relayMIX_st'] < spread['relay6Cage_st'] and spread5['relayMIX_st'] < spread5['relayCK1_st']
    for K in CAPS:
        d6 = [gain(mix[s][K], R[('relay6Cage_st', s, K)]) for s in S10]; dc = [gain(mix[s][K], R[('relayCK1_st', s, K)]) for s in S5]
        out[f'MIX_vs_6Cage|{NAME[K]}'] = d6; out[f'MIX_vs_CK1|{NAME[K]}'] = dc
        L.append(f'relayMIX vs relay6Cage at {NAME[K]} {np.mean(d6):+.2f} % ({sum(v > 0 for v in d6)}/10 > 0) | vs relayCK1 (s0-4) {np.mean(dc):+.2f} % ({sum(v > 0 for v in dc)}/5 > 0)')
    L += [f'MX1 relayMIX vs Z at K = 1: {m1:+.2f} % {ci1} (need mean >= 0, lower > -0.5) -> {"SUPPORTED" if MX1 else "NOT SUPPORTED"}',
          f'MX2 relayMIX vs relay6Cage at iid: {np.mean(v6):+.2f} % (need >= -0.3) -> {"SUPPORTED" if MX2 else "NOT SUPPORTED"}',
          f'MX3 relayMIX vs relayCK1 (s0-4): iid {np.mean(vc0):+.2f} % (need >= 0), K = 1 {np.mean(vc1):+.2f} % (need >= -0.3) -> {"SUPPORTED" if MX3 else "NOT SUPPORTED"}',
          f'MX4 (exploratory) spread of the mean gain vs Z over K: ' + ', '.join(f'{a} {v:.2f}' for a, v in spread.items())
          + ' | seeds 0-4: ' + ', '.join(f'{a} {v:.2f}' for a, v in spread5.items()) + f' -> {"SUPPORTED" if MX4 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (M / 'e3_mixed_channel_report_20261002.txt').write_text(text + '\n')
    (M / 'e3_mixed_channel_report_20261002.json').write_text(json.dumps(dict(per_seed=out, MX=dict(MX1=MX1, MX2=MX2, MX3=MX3, MX4=MX4)), indent=1))


if __name__ == '__main__':
    main()
