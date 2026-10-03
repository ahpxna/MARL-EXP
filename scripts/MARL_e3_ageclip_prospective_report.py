#!/usr/bin/env python3
"""Report of PROTOCOL_E3_AGECLIP_PROSPECTIVE_20261001.md (written 01/10/2026 12:14:15 EDT, before the runs).
A1 clip effect at const K = 1 > 0 (bootstrap lower bound > 0); A2 R_clip vs Z at K = 1 lower bound > -0.5 % ("reversed" if > 0);
A3 iid clip effect 95 % interval inside [-0.5, +0.5] %; A4 Spearman(dev decision-level clip gain, clip effect at K = 1) >= 0.5.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); P = M / 'e3_ageclip_prospective_20261001'; SEEDS = range(10)
EPS = [f'seed{s}_load{h}' for s in range(3101, 3165) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
A4 = {0: 0.046, 1: 0.000, 2: 0.081, 3: 0.041, 4: 0.017, 5: 0.012, 6: 0.037, 7: 0.037, 8: 0.016, 9: 0.015}


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
        ss = rng.choice(list(SEEDS), 10)
        bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [float(v) for v in np.percentile(bs, [2.5, 97.5])]


def main():
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in SEEDS}
    R = {(s, K, A): load(f'R_s{s}_K{K}_A{A}', 'prefix' if A == '-1' else 'clip2', f'relay6Cage_st_s{s}')
         for s in SEEDS for K in (1, 0) for A in ('2', '-1')}
    miss = [k for k, v in list(Z.items()) + list(R.items()) if v is None]
    if miss:
        print(f'INCOMPLETE: {len(miss)} arms missing'); return
    out = {}; L = []
    for K, name in ((1, 'const K = 1'), (0, 'iid')):
        C = {s: R[(s, K, '2')] for s in SEEDS}; N = {s: R[(s, K, '-1')] for s in SEEDS}
        ce = [gain(C[s], N[s]) for s in SEEDS]; gc = [gain(C[s], Z[s]) for s in SEEDS]; gn = [gain(N[s], Z[s]) for s in SEEDS]
        out[name] = dict(clip_effect=ce, clip_vs_Z=gc, none_vs_Z=gn, ci_clip_effect=boot(C, N), ci_clip_vs_Z=boot(C, Z), ci_none_vs_Z=boot(N, Z))
        o = out[name]
        L.append(f'{name}: clip effect {np.mean(ce):+.2f} % {o["ci_clip_effect"]} | R_clip vs Z {np.mean(gc):+.2f} % {o["ci_clip_vs_Z"]} | '
                 f'R_none vs Z {np.mean(gn):+.2f} % {o["ci_none_vs_Z"]}')
        L.append('   per seed clip effect: ' + ' '.join(f'{v:+.2f}' for v in ce))
        L.append('   per seed R_clip vs Z: ' + ' '.join(f'{v:+.2f}' for v in gc))
    k1, iid = out['const K = 1'], out['iid']
    A1 = np.mean(k1['clip_effect']) > 0 and k1['ci_clip_effect'][0] > 0
    A2 = k1['ci_clip_vs_Z'][0] > -0.5; rev = k1['ci_clip_vs_Z'][0] > 0
    A3 = -0.5 <= iid['ci_clip_effect'][0] and iid['ci_clip_effect'][1] <= 0.5
    r4 = float(spearmanr([A4[s] for s in SEEDS], k1['clip_effect']).correlation); A4ok = r4 >= 0.5
    L += [f'A1 clip effect at K = 1 > 0 (lower bound > 0): {"SUPPORTED" if A1 else "NOT SUPPORTED"}',
          f'A2 R_clip vs Z at K = 1, lower bound > -0.5 %: {"SUPPORTED" if A2 else "NOT SUPPORTED"} (reversed, lower bound > 0: {rev})',
          f'A3 iid clip effect inside [-0.5, +0.5] %: {"SUPPORTED" if A3 else "NOT SUPPORTED"}',
          f'A4 Spearman(dev decision-level clip gain, clip effect at K = 1) {r4:+.3f} >= 0.5: {"SUPPORTED" if A4ok else "NOT SUPPORTED"}']
    out.update(A1=bool(A1), A2=bool(A2), A2_reversed=bool(rev), A3=bool(A3), A4=bool(A4ok), A4_rho=r4)
    text = '\n'.join(L); print(text)
    (M / 'e3_ageclip_prospective_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_ageclip_prospective_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
