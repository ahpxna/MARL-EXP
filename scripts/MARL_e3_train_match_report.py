#!/usr/bin/env python3
"""Report of PROTOCOL_E3_TRAIN_MATCH_K1_20261001.md (written 01/10/2026 12:18:45 EDT, before training / evaluation).
TM1 relayCK1 vs Z at const K = 1: mean >= 0 and lower bound > -0.5 %; TM2 relayCK1 vs relay6Cage at const K = 1: mean > 0, lower
bound > 0; TM3 iid comparisons reported; TM4 mean dev net_Z of relayCK1 at K = 1 > 0 (against relay6Cage's from e3_negflip).
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_train_match_20261001'; SEEDS = range(5)
EPS = [f'seed{s}_load{h}' for s in range(3201, 3265) for h in (8, 16)]
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
        ss = rng.choice(list(SEEDS), len(SEEDS))
        bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [float(v) for v in np.percentile(bs, [2.5, 97.5])]


def netz(d):
    z = np.load(d / 'flags.npz'); return float(z['protoS'].mean() - z['zok'].mean())


def main():
    Z = {s: load(f'Z_s{s}', 'none', f'distill_none_s{s}') for s in SEEDS}
    R = {(a, s, K): load(f'R_{a}_s{s}_K{K}', 'prefix', f'{a}_s{s}') for a in ('relayCK1_st', 'relay6Cage_st') for s in SEEDS for K in (1, 0)}
    nf = {s: (P / f'NF_s{s}_K1') for s in SEEDS}
    miss = [k for k, v in list(Z.items()) + list(R.items()) if v is None] + [s for s, d in nf.items() if not (d / 'manifest.json').exists()]
    if miss:
        print(f'INCOMPLETE: {len(miss)} items missing'); return
    out = {}; L = []
    for K, name in ((1, 'const K = 1'), (0, 'iid')):
        C = {s: R[('relayCK1_st', s, K)] for s in SEEDS}; I = {s: R[('relay6Cage_st', s, K)] for s in SEEDS}
        o = dict(ck1_vs_Z=[gain(C[s], Z[s]) for s in SEEDS], iid_vs_Z=[gain(I[s], Z[s]) for s in SEEDS], ck1_vs_iid=[gain(C[s], I[s]) for s in SEEDS],
                 ci_ck1_vs_Z=boot(C, Z), ci_iid_vs_Z=boot(I, Z), ci_ck1_vs_iid=boot(C, I)); out[name] = o
        L.append(f'{name}: K1-trained vs Z {np.mean(o["ck1_vs_Z"]):+.2f} % {o["ci_ck1_vs_Z"]} | iid-trained vs Z {np.mean(o["iid_vs_Z"]):+.2f} % '
                 f'{o["ci_iid_vs_Z"]} | K1-trained vs iid-trained {np.mean(o["ck1_vs_iid"]):+.2f} % {o["ci_ck1_vs_iid"]}')
        for k in ('ck1_vs_Z', 'iid_vs_Z', 'ck1_vs_iid'):
            L.append(f'   per seed {k}: ' + ' '.join(f'{v:+.2f}' for v in o[k]))
    k1 = out['const K = 1']
    TM1 = np.mean(k1['ck1_vs_Z']) >= 0 and k1['ci_ck1_vs_Z'][0] > -0.5
    TM2 = np.mean(k1['ck1_vs_iid']) > 0 and k1['ci_ck1_vs_iid'][0] > 0
    nz = {s: netz(nf[s]) for s in SEEDS}; nz0 = {s: netz(M / f'e3_negflip_20261001/s{s}_K1') for s in SEEDS}
    TM4 = float(np.mean(list(nz.values()))) > 0
    L += [f'TM1 rescue (K1-trained vs Z at K = 1, mean >= 0 and lower bound > -0.5 %): {"SUPPORTED" if TM1 else "NOT SUPPORTED"}',
          f'TM2 matching helps (K1-trained vs iid-trained at K = 1, lower bound > 0): {"SUPPORTED" if TM2 else "NOT SUPPORTED"}',
          f'TM4 dev net_Z at K = 1: K1-trained {np.mean(list(nz.values())):+.4f} ({" ".join(f"{v:+.3f}" for v in nz.values())}) vs iid-trained '
          f'{np.mean(list(nz0.values())):+.4f} -> {"SUPPORTED" if TM4 else "NOT SUPPORTED"}']
    out.update(TM1=bool(TM1), TM2=bool(TM2), TM4=bool(TM4), netZ_ck1=nz, netZ_iid=nz0)
    text = '\n'.join(L); print(text)
    (M / 'e3_train_match_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_train_match_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
