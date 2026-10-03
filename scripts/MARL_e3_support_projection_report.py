#!/usr/bin/env python3
"""Report of PROTOCOL_E3_SUPPORT_PROJECTION_20261002.md (written 12:43:58 EDT, before any run).  Panel 4101-4164, seeds 0-4.
SP1 onefresh vs plain at iid lower bound > 0; SP2 onefresh >= plain at K = 2, 3; SP3 onefresh at iid >= plain at K = 1;
reported: recovery fraction at iid.  Identity self-check: onefresh at K = 1 = plain rows."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_support_projection_20261002'; SEEDS = list(range(5))
EPS = [f'seed{s}_load{h}' for s in range(4101, 4165) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}


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
    PL = {(s, K): load(f'P_relayCK1_st_s{s}_K{K}', 'prefix', f'relayCK1_st_s{s}') for s in SEEDS for K in (1, 2, 3, 0)}
    J = {(s, K): load(f'J_relayCK1_st_s{s}_K{K}', 'projectonefresh', f'relayCK1_st_s{s}') for s in SEEDS for K in (2, 3, 0)}
    I = {s: load(f'I_relayCK1_st_s{s}_K1', 'projectonefresh', f'relayCK1_st_s{s}') for s in SEEDS}
    S6 = {s: load(f'P_relay6Cage_st_s{s}_K0', 'prefix', f'relay6Cage_st_s{s}') for s in SEEDS}
    allv = list(Z.values()) + list(PL.values()) + list(J.values()) + list(I.values()) + list(S6.values())
    if any(v is None for v in allv):
        print(f'INCOMPLETE: {sum(v is None for v in allv)} of {len(allv)} items missing'); return
    if not all(np.array_equal(I[s], PL[(s, 1)]) for s in SEEDS):
        print('IDENTITY SELF-CHECK FAIL'); return
    g = lambda D, K: float(np.mean([gain(D[(s, K)], Z[s]) for s in SEEDS]))
    L = ['identity self-check (onefresh at K = 1 = plain rows, 5 evaluations): PASS',
         'relayCK1 plain vs Z: ' + ', '.join(f'{NAME[K]} {g(PL, K):+.2f}' for K in (1, 2, 3, 0)),
         'relayCK1 onefresh vs Z: ' + ', '.join(f'{NAME[K]} {g(J, K):+.2f}' for K in (2, 3, 0)),
         f'relay6Cage plain vs Z at iid: {np.mean([gain(S6[s], Z[s]) for s in SEEDS]):+.2f}']
    eff = {}
    for K in (2, 3, 0):
        e = [gain(J[(s, K)], PL[(s, K)]) for s in SEEDS]; eff[K] = float(np.mean(e))
        L.append(f'onefresh vs plain at {NAME[K]}: {np.mean(e):+.2f} % {boot({s: J[(s, K)] for s in SEEDS}, {s: PL[(s, K)] for s in SEEDS})} | ' + ' '.join(f'{v:+.2f}' for v in e))
    ci = boot({s: J[(s, 0)] for s in SEEDS}, {s: PL[(s, 0)] for s in SEEDS})
    SP1 = eff[0] > 0 and ci[0] > 0; SP2 = eff[2] >= 0 and eff[3] >= 0; SP3 = g(J, 0) >= g(PL, 1)
    g6 = float(np.mean([gain(S6[s], Z[s]) for s in SEEDS])); fr = (g(J, 0) - g(PL, 0)) / (g6 - g(PL, 0))
    L += [f'SP1 projection repairs the upgrade at iid (lower > 0) -> {"SUPPORTED" if SP1 else "NOT SUPPORTED"}',
          f'SP2 onefresh >= plain at K = 2 ({eff[2]:+.2f}) and K = 3 ({eff[3]:+.2f}) -> {"SUPPORTED" if SP2 else "NOT SUPPORTED"}',
          f'SP3 onefresh at iid {g(J, 0):+.2f} >= plain K = 1 {g(PL, 1):+.2f} -> {"SUPPORTED" if SP3 else "NOT SUPPORTED"}',
          f'reported: recovery fraction at iid (vs the retrained iid specialist) {fr:.2f}; transport comparator (L-266, panel 4001): remap vs plain −5.21 %']
    text = '\n'.join(L); print(text); (M / 'e3_support_projection_report_20261002.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
