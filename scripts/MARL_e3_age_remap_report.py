#!/usr/bin/env python3
"""Report of PROTOCOL_E3_AGE_REMAP_20261002.md (written 02/10/2026 11:58:38 EDT, before any run).  Panel 4001-4064 x 8/16,
seeds 0-4; gains vs Z; two-level bootstrap.  RM1 relayCK1 remap vs plain at iid lower bound > 0; RM2 remap >= plain for relayCK1
at K = 2, 3, iid; RM3 recovery fraction f >= 0.7 (relayCK1 at iid) and <= 0.5 (relay6Cage at K = 1); RM4 (sign) relay6Cage
remap vs plain at K = 1, with the clip; RM5 relayCK1 remap at iid >= its plain K = 1 gain.  Identity checks must be exact."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_age_remap_20261002'; SEEDS = list(range(5))
EPS = [f'seed{s}_load{h}' for s in range(4001, 4065) for h in (8, 16)]
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
    A = ('relayCK1_st', 'relay6Cage_st')
    PL = {(a, s, K): load(f'P_{a}_s{s}_K{K}', 'prefix', f'{a}_s{s}') for a in A for s in SEEDS for K in (1, 2, 3, 0)}
    RM = {('relayCK1_st', s, K): load(f'M_relayCK1_st_s{s}_K{K}', 'remap1', f'relayCK1_st_s{s}') for s in SEEDS for K in (2, 3, 0)}
    RM.update({('relay6Cage_st', s, K): load(f'M_relay6Cage_st_s{s}_K{K}', 'remap0', f'relay6Cage_st_s{s}') for s in SEEDS for K in (1, 2, 3)})
    ID = {s: (load(f'I_relayCK1_st_s{s}_K1', 'remap1', f'relayCK1_st_s{s}'), load(f'I_relay6Cage_st_s{s}_K0', 'remap0', f'relay6Cage_st_s{s}')) for s in SEEDS}
    CL = {s: load(f'C_relay6Cage_st_s{s}_K1', 'clip2', f'relay6Cage_st_s{s}') for s in SEEDS}
    allv = list(Z.values()) + list(PL.values()) + list(RM.values()) + [x for p in ID.values() for x in p] + list(CL.values())
    if any(v is None for v in allv):
        print(f'INCOMPLETE: {sum(v is None for v in allv)} of {len(allv)} items missing'); return
    idok = all(np.array_equal(ID[s][0], PL[('relayCK1_st', s, 1)]) and np.array_equal(ID[s][1], PL[('relay6Cage_st', s, 0)]) for s in SEEDS)
    if not idok:
        print('IDENTITY SELF-CHECK FAIL: the remap at the training channel does not reproduce the plain rows'); return
    G = lambda D, a, K: float(np.mean([gain(D[(a, s, K)], Z[s]) for s in SEEDS]))
    L = ['identity self-check (remap at the training channel = plain rows, 10 evaluations): PASS', 'student | capacity | plain vs Z | remap vs Z | remap vs plain (95 %) | per seed']
    eff = {}
    for a, Ks in (('relayCK1_st', (2, 3, 0)), ('relay6Cage_st', (1, 2, 3))):
        for K in Ks:
            e = [gain(RM[(a, s, K)], PL[(a, s, K)]) for s in SEEDS]; eff[(a, K)] = float(np.mean(e))
            L.append(f'{a} | {NAME[K]} | {G(PL, a, K):+.2f} % | {G(RM, a, K):+.2f} % | {np.mean(e):+.2f} % '
                     f'{boot({s: RM[(a, s, K)] for s in SEEDS}, {s: PL[(a, s, K)] for s in SEEDS})} | ' + ' '.join(f'{v:+.2f}' for v in e))
    for a in A:
        L.append(f'{a} plain vs Z: ' + ', '.join(f'{NAME[K]} {G(PL, a, K):+.2f}' for K in (1, 2, 3, 0)))
    clip = float(np.mean([gain(CL[s], PL[('relay6Cage_st', s, 1)]) for s in SEEDS]))
    ci1 = boot({s: RM[('relayCK1_st', s, 0)] for s in SEEDS}, {s: PL[('relayCK1_st', s, 0)] for s in SEEDS})
    RM1 = eff[('relayCK1_st', 0)] > 0 and ci1[0] > 0
    RM2 = all(eff[('relayCK1_st', K)] >= 0 for K in (2, 3, 0))
    fu = (G(RM, 'relayCK1_st', 0) - G(PL, 'relayCK1_st', 0)) / (G(PL, 'relay6Cage_st', 0) - G(PL, 'relayCK1_st', 0))
    fd = (G(RM, 'relay6Cage_st', 1) - G(PL, 'relay6Cage_st', 1)) / (G(PL, 'relayCK1_st', 1) - G(PL, 'relay6Cage_st', 1))
    RM3 = fu >= 0.7 and fd <= 0.5
    RM5 = G(RM, 'relayCK1_st', 0) >= G(PL, 'relayCK1_st', 1)
    L += [f'RM1 upgrade repaired (relayCK1 at iid, remap vs plain {eff[("relayCK1_st", 0)]:+.2f} % {ci1}, lower > 0) -> {"SUPPORTED" if RM1 else "NOT SUPPORTED"}',
          f'RM2 remap >= plain for relayCK1 at K = 2, 3, iid -> {"SUPPORTED" if RM2 else "NOT SUPPORTED"}',
          f'RM3 recovery fraction: upgrade f = {fu:.2f} (need >= 0.7), downgrade f = {fd:.2f} (need <= 0.5) -> {"SUPPORTED" if RM3 else "NOT SUPPORTED"}',
          f'RM4 (sign) relay6Cage at K = 1: remap vs plain {eff[("relay6Cage_st", 1)]:+.2f} %, clip A = 2 vs plain {clip:+.2f} %',
          f'RM5 relayCK1 remap at iid {G(RM, "relayCK1_st", 0):+.2f} % vs its plain K = 1 {G(PL, "relayCK1_st", 1):+.2f} % -> {"SUPPORTED" if RM5 else "NOT SUPPORTED"}']
    text = '\n'.join(L); print(text); (M / 'e3_age_remap_report_20261002.txt').write_text(text + '\n')
    (M / 'e3_age_remap_report_20261002.json').write_text(json.dumps(dict(effect={f'{a}|{NAME[K]}': v for (a, K), v in eff.items()}, fu=fu, fd=fd,
                                                                        clip=clip, RM1=RM1, RM2=RM2, RM3=RM3, RM5=RM5), indent=1, default=float))


if __name__ == '__main__':
    main()
