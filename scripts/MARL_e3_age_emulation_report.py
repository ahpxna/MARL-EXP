#!/usr/bin/env python3
"""Report of PROTOCOL_E3_AGE_EMULATION_20261003.md (written 02:5x EDT 03/10, before any panel run).
EM1 EMU > PLAIN at iid (4x4 relayCK1; lower > 0, >= 7/10); EM2 EMU > LAB at iid (same); EM3 half of the hazard recovered;
EM4 |EMU - PLAIN| <= 0.3 in support (relayCK1 K=1, Cage iid; both nets); EM5 3x3 signs of EM1, EM2 in >= 4/5 seeds.  Amendment 1: EMU / LAB = per-slot floors (primary); EMUR / LABR = rank floors (reported).
Usage: MARL_e3_age_emulation_report.py [--smoke]"""
from __future__ import annotations
import argparse, json
from pathlib import Path
import numpy as np

ROOT = Path('research/marl_budget/e3_age_emulation_20261003')
NAME = {1: 'K=1', 2: 'K=2', 3: 'K=3', 0: 'iid'}


def load(P, tag, eps, key, val, ckpt):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE', tag
    assert f'{ckpt}/ckpt_best.pt' in str(m.get('args')), tag
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r.get(key) == val}
    assert sorted(rows) == sorted(eps), f'{tag} {val}: {len(rows)} episodes'
    return np.array([rows[e] for e in eps], float)


def gain(x, y, ii=None):
    return -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100


def main(a):
    out = []; verdict = {}
    for net, seeds, cage in (('4x4', range(10), 'relayCage_st'), ('3x3', range(5), 'relay6Cage_st')):
        P = ROOT / ('smoke_pipe' if a.smoke else '') / net
        panel = (9001, 9002) if a.smoke else tuple(range(5101, 5165))
        eps = [f'seed{s}_load{h}' for s in panel for h in (8, 16)]
        TS = sorted({e.split('_')[0] for e in eps}); IDX = {u: [i for i, e in enumerate(eps) if e.startswith(u + '_')] for u in TS}
        Z = {s: load(P, f'Z_s{s}', eps, 'rule', 'none', f'distill_none_s{s}') for s in seeds}
        R = {}
        for s in seeds:
            for arm, Ks in (('relayCK1_st', (1, 0, 2, 3)), (cage, (0,))):
                for K in Ks:
                    for md in ('plain', 'emu', 'lab', 'emur', 'labr'):
                        R[(arm, s, K, md)] = load(P, f'EM_{arm}_s{s}_K{K}', eps, 'mode', md, f'{arm}_s{s}')
        S = [s for s in seeds if Z[s] is not None and all(R[k] is not None for k in R if k[1] == s)]
        out.append(f'== {net}: complete seeds {S} of {list(seeds)}')
        if not S:
            continue

        def g(arm, s, K, md):
            return gain(R[(arm, s, K, md)], Z[s])

        def boot(f):
            rng = np.random.default_rng(0); bs = []
            for _ in range(2000):
                ss = rng.choice(S, len(S)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
                bs.append(np.mean([f(s, ii) for s in ss]))
            return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]

        def diff(arm, K, m1, m2):
            per = [g(arm, s, K, m1) - g(arm, s, K, m2) for s in S]
            ci = boot(lambda s, ii: gain(R[(arm, s, K, m1)], Z[s], ii) - gain(R[(arm, s, K, m2)], Z[s], ii))
            return float(np.mean(per)), ci, sum(x > 0 for x in per), per

        for arm, Ks in (('relayCK1_st', (1, 0, 2, 3)), (cage, (0,))):
            for K in Ks:
                gm = {md: np.mean([g(arm, s, K, md) for s in S]) for md in ('plain', 'emu', 'lab', 'emur', 'labr')}
                e_p = diff(arm, K, 'emu', 'plain'); e_l = diff(arm, K, 'emu', 'lab'); r_p = diff(arm, K, 'emur', 'plain'); r_l = diff(arm, K, 'emur', 'labr')
                out.append(f'{arm} {NAME[K]} | gain vs Z PLAIN {gm["plain"]:+.2f} EMU {gm["emu"]:+.2f} LAB {gm["lab"]:+.2f} | '
                           f'EMU-PLAIN {e_p[0]:+.2f} {e_p[1]} ({e_p[2]}/{len(S)}) | EMU-LAB {e_l[0]:+.2f} {e_l[1]} ({e_l[2]}/{len(S)}) || '
                           f'rank: EMUR {gm["emur"]:+.2f} LABR {gm["labr"]:+.2f} EMUR-PLAIN {r_p[0]:+.2f} {r_p[1]} EMUR-LABR {r_l[0]:+.2f} {r_l[1]}')
                verdict[(net, arm, K)] = dict(ep=e_p, el=e_l, gm=gm)
        hz = np.mean([g('relayCK1_st', s, 1, 'plain') - g('relayCK1_st', s, 0, 'plain') for s in S])
        out.append(f'{net} hazard PLAIN K=1 - iid {hz:+.2f}; recovered by EMU at iid {verdict[(net, "relayCK1_st", 0)]["ep"][0]:+.2f}')
        verdict[(net, 'hazard')] = hz
    if not a.smoke and ('4x4', 'relayCK1_st', 0) in verdict:
        v = verdict[('4x4', 'relayCK1_st', 0)]; n4 = 10
        out.append(f'EM1 EMU > PLAIN at iid (4x4): {"SUPPORTED" if v["ep"][1][0] > 0 and v["ep"][2] >= 7 else "NOT SUPPORTED"}')
        out.append(f'EM2 EMU > LAB at iid (4x4): {"SUPPORTED" if v["el"][1][0] > 0 and v["el"][2] >= 7 else "NOT SUPPORTED"}')
        out.append(f'EM3 half of the hazard: {"SUPPORTED" if v["ep"][0] >= 0.5 * verdict[("4x4", "hazard")] else "NOT SUPPORTED"}')
        em4 = all(abs(verdict[k]['ep'][0]) <= 0.3 for k in verdict if isinstance(k, tuple) and len(k) == 3 and
                  ((k[1] == 'relayCK1_st' and k[2] == 1) or (k[1] != 'relayCK1_st' and k[2] == 0)))
        out.append(f'EM4 near-identity in support: {"SUPPORTED" if em4 else "NOT SUPPORTED"}')
        if ('3x3', 'relayCK1_st', 0) in verdict:
            w = verdict[('3x3', 'relayCK1_st', 0)]
            out.append(f'EM5 3x3 signs (EM1 {w["ep"][2]}/5, EM2 {w["el"][2]}/5): '
                       f'{"SUPPORTED" if w["ep"][2] >= 4 and w["el"][2] >= 4 else "NOT SUPPORTED"}')
    txt = '\n'.join(out); print(txt)
    (ROOT / ('smoke_pipe' if a.smoke else '') / 'report.txt').write_text(txt + '\n')


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--smoke', action='store_true'); main(p.parse_args())
