#!/usr/bin/env python3
"""Report of PROTOCOL_E3_GATE_PROSPECTIVE_20261001.md (written before the runs).
GT1 never worse than silence: gate vs Z lower bound > -0.5 % at every K in {1, 2, 3, iid};
GT2 the gate keeps communication where the view is in range: fallback share <= 2 % at K = 2, 3 and iid;
GT3 repair at K = 1: gate vs plain relay mean > 0 with lower bound > 0;
GT4 (reported) gate vs Z and plain vs Z at every K, per seed.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_gate_prospective_20261001'; SEEDS = list(range(10)); KS = (1, 2, 3, 0)
EPS = [f'seed{s}_load{h}' for s in range(3401, 3465) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
NAME = {1: 'K = 1', 2: 'K = 2', 3: 'K = 3', 0: 'iid'}


def load(tag, ckpt_name):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None, None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    assert f'{ckpt_name}/ckpt_best.pt' in str(m.get('args')), tag
    rows = {r['episode']: r for r in json.loads((d / 'rows.json').read_text())}
    assert sorted(rows) == sorted(EPS), f'{tag}: {len(rows)} episodes'
    return np.array([rows[e]['queue_sum'] for e in EPS], float), rows


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


def boot(X, Y):
    rng = np.random.default_rng(0); bs = []
    for _ in range(4000):
        ss = rng.choice(SEEDS, len(SEEDS))
        bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [float(v) for v in np.percentile(bs, [2.5, 97.5])]


def main():
    Z = {s: load(f'Z_s{s}', f'distill_none_s{s}')[0] for s in SEEDS}
    R = {(s, K): load(f'R_s{s}_K{K}', f'relay6Cage_st_s{s}')[0] for s in SEEDS for K in KS}
    G = {(s, K): load(f'G_s{s}_K{K}', f'relay6Cage_st_s{s}') for s in SEEDS for K in KS}
    if any(v is None for v in Z.values()) or any(v is None for v in R.values()) or any(v[0] is None for v in G.values()):
        print('INCOMPLETE'); return
    out = {}; L = []; gt1 = True; gt2 = True
    for K in KS:
        g = {s: G[(s, K)][0] for s in SEEDS}; r = {s: R[(s, K)] for s in SEEDS}
        fb = float(np.mean([sum(x['fallback_decisions'] for x in G[(s, K)][1].values()) / (len(EPS) * 26 * 9) for s in SEEDS]))
        o = dict(gate_vs_Z=[gain(g[s], Z[s]) for s in SEEDS], plain_vs_Z=[gain(r[s], Z[s]) for s in SEEDS], gate_vs_plain=[gain(g[s], r[s]) for s in SEEDS],
                 ci_gate_vs_Z=boot(g, Z), ci_plain_vs_Z=boot(r, Z), ci_gate_vs_plain=boot(g, r), fallback=fb)
        out[NAME[K]] = o; gt1 = gt1 and o['ci_gate_vs_Z'][0] > -0.5
        if K != 1:
            gt2 = gt2 and fb <= 0.02
        L.append(f'{NAME[K]}: gate vs Z {np.mean(o["gate_vs_Z"]):+.2f} % {o["ci_gate_vs_Z"]} | plain vs Z {np.mean(o["plain_vs_Z"]):+.2f} % '
                 f'{o["ci_plain_vs_Z"]} | gate vs plain {np.mean(o["gate_vs_plain"]):+.2f} % {o["ci_gate_vs_plain"]} | fallback {fb:.3f}')
        L.append('   per seed gate vs Z: ' + ' '.join(f'{v:+.2f}' for v in o['gate_vs_Z']))
    k1 = out['K = 1']; gt3 = np.mean(k1['gate_vs_plain']) > 0 and k1['ci_gate_vs_plain'][0] > 0
    L += [f'GT1 never worse than silence (gate vs Z lower bound > -0.5 % at every K): {"SUPPORTED" if gt1 else "NOT SUPPORTED"}',
          f'GT2 fallback share <= 2 % at K = 2, 3, iid: {"SUPPORTED" if gt2 else "NOT SUPPORTED"}',
          f'GT3 repair at K = 1 (gate vs plain lower bound > 0): {"SUPPORTED" if gt3 else "NOT SUPPORTED"}']
    out.update(GT1=bool(gt1), GT2=bool(gt2), GT3=bool(gt3))
    text = '\n'.join(L); print(text)
    (M / 'e3_gate_prospective_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_gate_prospective_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
