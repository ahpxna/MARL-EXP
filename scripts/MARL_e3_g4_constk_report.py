#!/usr/bin/env python3
"""Report of PROTOCOL_E3_G4_CONSTK_20261001.md (written 01/10/2026 12:40:15 EDT, before any run) and its Addendum 2
(18:46:52 EDT, before any run: the K = 2 discriminating cell between the relative and absolute staleness readings).
G1 R_none vs Z at const K = 1 upper bound < 0; G2 gain(1) < gain(2) < gain(3) and dev B_stale(1) > B_stale(2) > B_stale(3);
G3 sign(mean dev net_Z(K)) = sign(mean gain(K)) for K = 1, 2, 3, iid; G4 R_clip vs R_none at K = 1 lower bound > 0.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np

M = Path('research/marl_budget'); P = M / 'e3_g4_constk_20261001'; A = M / 'e3_grid4x4_20260930/actors'
EPS = [f'seed{s}_load{h}' for s in range(3301, 3365) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
CAP = {1: 'const1', 2: 'const2', 3: 'const3', 0: 'iid'}


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


def boot(X, Y, S):
    rng = np.random.default_rng(0); bs = []
    for _ in range(4000):
        ss = rng.choice(S, len(S))
        bs.append(np.mean([gain(X[s], Y[s], np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])) for s in ss]))
    return [float(v) for v in np.percentile(bs, [2.5, 97.5])]


def burden(s, K, a99):
    z = np.load(P / f'VS_s{s}_K{K}/flags.npz'); h = z['age_hist'].sum(0); a = np.arange(len(h))
    return float((h * np.maximum(a - a99, 0)).sum() / len(z['max_age']))


def main():
    S = []
    for s in range(10):
        a95 = P / f'a95_s{s}.txt'
        if not a95.exists():
            continue
        clip_rule = f'clip{float(a95.read_text().strip()):g}'
        Z = load(f'Z_s{s}', 'none', f'distill_none_s{s}')
        R = {K: load(f'R_s{s}_K{K}_A-1', 'prefix', f'relayCage_st_s{s}') for K in CAP}
        C = load(f'R_s{s}_K1_clip', clip_rule, f'relayCage_st_s{s}')
        nf = all((P / f'NF_s{s}_{CAP[K]}/manifest.json').exists() for K in CAP) and all((P / f'VS_s{s}_K{K}/manifest.json').exists() for K in CAP)
        if Z is not None and C is not None and all(v is not None for v in R.values()) and nf:
            S.append((s, Z, R, C))
    if len(S) < 8:
        print(f'INCOMPLETE: {len(S)} complete seeds (need 8)'); return
    seeds = [x[0] for x in S]; Z = {x[0]: x[1] for x in S}; R = {x[0]: x[2] for x in S}; C = {x[0]: x[3] for x in S}
    out = dict(seeds=seeds); L = [f'complete seeds {seeds}']
    g = {K: [gain(R[s][K], Z[s]) for s in seeds] for K in CAP}; ci = {K: boot({s: R[s][K] for s in seeds}, Z, seeds) for K in CAP}
    netz = {}; B = {}
    for K in CAP:
        netz[K] = []
        for s in seeds:
            f = np.load(P / f'NF_s{s}_{CAP[K]}/flags.npz'); netz[K].append(float(f['protoS'].mean() - f['zok'].mean()))
    for s in seeds:
        z = np.load(P / f'VS_s{s}_K0/flags.npz'); a99 = float(np.percentile(z['max_age'][z['max_age'] >= 0], 99))
        B[s] = {K: burden(s, K, a99) for K in CAP}
    for K in (1, 2, 3, 0):
        L.append(f'{CAP[K]}: R_none vs Z {np.mean(g[K]):+.2f} % {ci[K]} | dev net_Z {np.mean(netz[K]):+.4f} | dev B_stale {np.mean([B[s][K] for s in seeds]):.2f}')
    ce = [gain(C[s], R[s][1]) for s in seeds]; cci = boot(C, {s: R[s][1] for s in seeds}, seeds)
    cz = [gain(C[s], Z[s]) for s in seeds]; czi = boot(C, Z, seeds)
    L.append(f'clip at K = 1: effect {np.mean(ce):+.2f} % {cci} | R_clip vs Z {np.mean(cz):+.2f} % {czi}')
    mg = {K: np.mean(g[K]) for K in CAP}; mb = {K: np.mean([B[s][K] for s in seeds]) for K in CAP}
    G1 = ci[1][1] < 0
    G2 = mg[1] < mg[2] < mg[3] and mb[1] > mb[2] > mb[3]
    G3 = all(np.sign(np.mean(netz[K])) == np.sign(mg[K]) for K in CAP)
    G4 = np.mean(ce) > 0 and cci[0] > 0
    L += [f'G1 sign reversal at K = 1 (upper bound < 0): {"SUPPORTED" if G1 else "NOT SUPPORTED"}',
          f'G2 dose (gain and burden monotone in K): {"SUPPORTED" if G2 else "NOT SUPPORTED"}',
          f'G3 decision-level sign = gain sign at K = 1, 2, 3, iid: {"SUPPORTED" if G3 else "NOT SUPPORTED"}',
          f'G4 interface repair (clip effect lower bound > 0): {"SUPPORTED" if G4 else "NOT SUPPORTED"}',
          f'reported: 4x4 K = 1 burden {mb[1]:.2f} vs 3x3 8.48; 4x4 K = 1 loss {mg[1]:+.2f} % vs 3x3 -1.6 %',
          'Addendum 2 discriminating cell K = 2: ' + ('R-abs (gain < 0, upper bound < 0)' if ci[2][1] < 0 else
                                                      'R-rel (gain > 0, lower bound > 0)' if ci[2][0] > 0 else 'undetermined')
          + f' [gain(2) {mg[2]:+.2f} % {ci[2]}]']
    L += [f'  s{s}: ' + ' '.join(f'{CAP[K]} {gain(R[s][K], Z[s]):+.2f}' for K in (1, 2, 3, 0)) + f' | clip {gain(C[s], R[s][1]):+.2f}' for s in seeds]
    out.update(gain=g, ci=ci, netz=netz, burden=B, clip_effect=ce, clip_ci=cci, clip_vs_Z=cz, clip_vs_Z_ci=czi, G1=bool(G1), G2=bool(G2), G3=bool(G3), G4=bool(G4))
    text = '\n'.join(L); print(text)
    (M / 'e3_g4_constk_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_g4_constk_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
