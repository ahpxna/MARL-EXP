#!/usr/bin/env python3
"""Report of PROTOCOL_E3_JOINT_THROTTLE_20261003.md (written 10:5x EDT 03/10, before any panel run).
JT1 THR > PLAIN at iid (4x4 relayCK1; lower > 0, >= 7/10); JT2 THR > THRLAB at iid (same); JT3 MASK below Z (upper < 0) for
relayCK1 at K1 and the iid-trained receiver at iid, both nets; JT4 3x3 signs of JT1, JT2 in >= 4/5.  Check: THR == PLAIN at K = 1.
Usage: MARL_e3_joint_throttle_report.py [--smoke]"""
import argparse, json
from pathlib import Path
import numpy as np
ROOT = Path('research/marl_budget/e3_joint_throttle_20261003'); NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}


def load(P, tag, eps, key, val, ckpt):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text()); assert m.get('status') == 'COMPLETE', tag
    assert f'{ckpt}/ckpt_best.pt' in str(m.get('args')), tag
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r.get(key) == val}
    assert sorted(rows) == sorted(eps), f'{tag} {val}: {len(rows)}'
    return np.array([rows[e] for e in eps], float)


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


def main(a):
    out = []; V = {}
    for net, seeds, cage in (('4x4', range(10), 'relayCage_st'), ('3x3', range(5), 'relay6Cage_st')):
        P = ROOT / ('smoke_pipe' if a.smoke else '') / net
        panel = (9001, 9002) if a.smoke else tuple(range(5201, 5265))
        eps = [f'seed{s}_load{h}' for s in panel for h in (8, 16)]
        TS = sorted({e.split('_')[0] for e in eps}); IDX = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in TS}
        Z = {s: load(P, f'Z_s{s}', eps, 'rule', 'none', f'distill_none_s{s}') for s in seeds}
        R = {}
        for s in seeds:
            for K in (0, 1, 2, 3):
                for md in ('plain', 'thr', 'thrlab', 'mask'):
                    R[('relayCK1_st', s, K, md)] = load(P, f'JT_relayCK1_st_s{s}_K{K}', eps, 'mode', md, f'relayCK1_st_s{s}')
            for K in (0, 1):
                for md in ('plain', 'mask'):
                    R[(cage, s, K, md)] = load(P, f'JT_{cage}_s{s}_K{K}', eps, 'mode', md, f'{cage}_s{s}')
        S = [s for s in seeds if Z[s] is not None and all(R[k] is not None for k in R if k[1] == s)]
        out.append(f'== {net}: complete seeds {S}')
        if not S:
            continue
        for s in S:                                                     # check: nothing to drop at K = 1
            assert np.array_equal(R[('relayCK1_st', s, 1, 'thr')], R[('relayCK1_st', s, 1, 'plain')]), f'THR != PLAIN at K=1, seed {s}'

        def boot(f):
            rng = np.random.default_rng(0); bs = []
            for _ in range(2000):
                ss = rng.choice(S, len(S)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
                bs.append(np.mean([f(s, ii) for s in ss]))
            return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]

        def g(arm, s, K, md, ii=None):
            return gain(R[(arm, s, K, md)], Z[s], ii)

        def diff(arm, K, m1, m2):
            per = [g(arm, s, K, m1) - g(arm, s, K, m2) for s in S]
            return float(np.mean(per)), boot(lambda s, ii: g(arm, s, K, m1, ii) - g(arm, s, K, m2, ii)), sum(x > 0 for x in per)

        for K in (1, 0, 2, 3):
            gm = {md: np.mean([g('relayCK1_st', s, K, md) for s in S]) for md in ('plain', 'thr', 'thrlab', 'mask')}
            tp = diff('relayCK1_st', K, 'thr', 'plain'); tl = diff('relayCK1_st', K, 'thr', 'thrlab')
            mz = (float(np.mean([g('relayCK1_st', s, K, 'mask') for s in S])), boot(lambda s, ii: g('relayCK1_st', s, K, 'mask', ii)))
            out.append(f'relayCK1_st {NAME[K]} | gain vs Z PLAIN {gm["plain"]:+.2f} THR {gm["thr"]:+.2f} THRLAB {gm["thrlab"]:+.2f} MASK {gm["mask"]:+.2f} {mz[1]} | '
                       f'THR-PLAIN {tp[0]:+.2f} {tp[1]} ({tp[2]}/{len(S)}) | THR-THRLAB {tl[0]:+.2f} {tl[1]} ({tl[2]}/{len(S)})')
            V[(net, K)] = dict(tp=tp, tl=tl, mask=mz)
        for K in (0, 1):
            pm = np.mean([g(cage, s, K, 'plain') for s in S]); mz = (float(np.mean([g(cage, s, K, 'mask') for s in S])), boot(lambda s, ii: g(cage, s, K, 'mask', ii)))
            out.append(f'{cage} {NAME[K]} | PLAIN {pm:+.2f} MASK {mz[0]:+.2f} {mz[1]}')
            V[(net, 'cage', K)] = mz
    if not a.smoke and ('4x4', 0) in V:
        v = V[('4x4', 0)]
        out.append(f'JT1 THR > PLAIN at iid (4x4): {"SUPPORTED" if v["tp"][1][0] > 0 and v["tp"][2] >= 7 else "NOT SUPPORTED"}')
        out.append(f'JT2 THR > THRLAB at iid (4x4): {"SUPPORTED" if v["tl"][1][0] > 0 and v["tl"][2] >= 7 else "NOT SUPPORTED"}')
        jt3 = all(V[(n, 1)]['mask'][1][1] < 0 and V[(n, 'cage', 0)][1][1] < 0 for n in ('4x4', '3x3') if (n, 1) in V)
        out.append(f'JT3 MASK below Z (CK1 at K1, iid-trained at iid; both nets): {"SUPPORTED" if jt3 else "NOT SUPPORTED"}')
        if ('3x3', 0) in V:
            w = V[('3x3', 0)]
            out.append(f'JT4 3x3 signs (JT1 {w["tp"][2]}/5, JT2 {w["tl"][2]}/5): {"SUPPORTED" if w["tp"][2] >= 4 and w["tl"][2] >= 4 else "NOT SUPPORTED"}')
    txt = '\n'.join(out); print(txt); (ROOT / ('smoke_pipe' if a.smoke else '') / 'report.txt').write_text(txt + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
