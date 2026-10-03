#!/usr/bin/env python3
"""Report of PROTOCOL_E3_G4_TIME_PROJECTION_20261002.md (written 13:05:43 EDT, before any run).  4x4, panel 4301-4364, seeds 0-9.
TP1 timecov vs plain at K = 1 lower bound > 0; TP2 at iid the 95 % interval inside [-0.5, +0.5]; reported timecov vs Z at K = 1."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_g4_time_projection_20261002'; SEEDS = list(range(10))
EPS = [f'seed{s}_load{h}' for s in range(4301, 4365) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}


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
    PL = {(s, K): load(f'P_s{s}_K{K}', 'prefix', f'relayCage_st_s{s}') for s in SEEDS for K in (1, 0)}
    TC = {(s, K): load(f'T_s{s}_K{K}', 'projecttimecov', f'relayCage_st_s{s}') for s in SEEDS for K in (1, 0)}
    allv = list(Z.values()) + list(PL.values()) + list(TC.values())
    if any(v is None for v in allv):
        print(f'INCOMPLETE: {sum(v is None for v in allv)} of {len(allv)} items missing'); return
    L = []
    for K, nm in ((1, 'K=1'), (0, 'iid')):
        e = [gain(TC[(s, K)], PL[(s, K)]) for s in SEEDS]; ci = boot({s: TC[(s, K)] for s in SEEDS}, {s: PL[(s, K)] for s in SEEDS})
        gp = float(np.mean([gain(PL[(s, K)], Z[s]) for s in SEEDS])); gt = float(np.mean([gain(TC[(s, K)], Z[s]) for s in SEEDS]))
        L.append(f'{nm}: plain vs Z {gp:+.2f} % | timecov vs Z {gt:+.2f} % {boot({s: TC[(s, K)] for s in SEEDS}, Z)} | timecov vs plain {np.mean(e):+.2f} % {ci} | ' + ' '.join(f'{v:+.2f}' for v in e))
        if K == 1:
            TP1 = np.mean(e) > 0 and ci[0] > 0
        else:
            TP2 = ci[0] >= -0.5 and ci[1] <= 0.5
    L += [f'TP1 timecov repairs K = 1 (lower > 0) -> {"SUPPORTED" if TP1 else "NOT SUPPORTED"}',
          f'TP2 no harm at iid (interval inside [-0.5, 0.5]) -> {"SUPPORTED" if TP2 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (M / 'e3_g4_time_projection_report_20261002.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
