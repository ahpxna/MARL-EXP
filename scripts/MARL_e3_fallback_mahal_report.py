#!/usr/bin/env python3
"""Report of PROTOCOL_E3_FALLBACK_MAHAL_20261003.md (written 13:0x EDT 03/10, before any FB_M panel run).  Same gain, bootstrap,
hazard / benefit definitions as scripts/MARL_e3_fallback_report.py; Z from the stored #3 Z_s rows.
FM1 FB_Mq recovers >= 1/2 of the RELAY deficit at the 4x4 upgrade hazard; FM2 FB_M keeps < 0.75 RELAY in >= 1 own-channel benefit cell
(both nets) while FB_S keeps >= 0.75 everywhere; FM3 FB_S >= FB_Mq - 0.3 in every 4x4 cell; FM4 Spearman(FB_Mq rate, -gain RELAY) >= 0.6 (4x4)."""
import json
from pathlib import Path
import numpy as np
NAME = {1: 'K1', 2: 'K2', 3: 'K3', 0: 'iid'}; SYS = ['RELAY', 'FB_S', 'FB_M', 'FB_M95', 'FB_Mq']
NETS = {'4x4': dict(panel=range(4901, 4965), seeds=list(range(10)), arms=['relayCK1_st', 'relayCage_st']),
        '3x3': dict(panel=range(4801, 4865), seeds=list(range(5)), arms=['relayCK1_st', 'relay6Cage_st'])}
OWN = {'relay6Cage_st': [0], 'relayCage_st': [0], 'relayCK1_st': [1]}
L = []; V = {}
for net, c in NETS.items():
    F = Path('research/marl_budget/e3_fallback_20261002') / net; P = Path('research/marl_budget/e3_fallback_mahal_20261003') / net
    EPS = [f'seed{s}_load{h}' for s in c['panel'] for h in (8, 16)]; TS = [f'seed{s}' for s in c['panel']]
    IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}; seeds = c['seeds']

    def rows(d, system):
        m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
        r = {x['episode']: x for x in json.loads((d / 'rows.json').read_text()) if x['system'] == system}
        assert set(EPS) <= set(r), (d, system, len(r))
        return np.array([r[e]['queue_sum'] for e in EPS], float), (np.mean([r[e]['flags'] / r[e]['decisions'] for e in EPS]) if 'flags' in r[EPS[0]] else 0.0)
    try:
        Z = {s: rows(F / f'Z_s{s}', 'Z')[0] for s in seeds}
        ok = all((P / f'FBM_{arm}_s{s}_K{K}' / 'manifest.json').exists() for arm in c['arms'] for s in seeds for K in (1, 2, 3, 0))
    except (FileNotFoundError, AssertionError) as e:
        L.append(f'== {net}: incomplete ({e})'); continue
    if not ok:
        L.append(f'== {net}: incomplete'); continue
    gain = lambda x, y, ii=None: -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100
    def boot(X):
        rng = np.random.default_rng(0); bs = []
        for _ in range(2000):
            ss = rng.choice(seeds, len(seeds)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
            bs.append(np.mean([gain(X[s], Z[s], ii) for s in ss]))
        return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]
    G, CI, FR = {}, {}, {}
    for arm in c['arms']:
        for K in (1, 2, 3, 0):
            for sy in SYS:
                X = {}; fr = []
                for s in seeds:
                    q, f = rows(P / f'FBM_{arm}_s{s}_K{K}', sy); X[s] = q; fr.append(f)
                G[(arm, K, sy)] = float(np.mean([gain(X[s], Z[s]) for s in seeds])); CI[(arm, K, sy)] = boot(X); FR[(arm, K, sy)] = float(np.mean(fr))
    L.append(f'== {net}: gain vs Z in % [95 %] (fallback rate)')
    for arm in c['arms']:
        for K in (1, 2, 3, 0):
            L.append(f'{arm} {NAME[K]:>3} | ' + ' | '.join(f'{sy} {G[(arm, K, sy)]:+.2f} {CI[(arm, K, sy)]} ({FR[(arm, K, sy)]:.2f})' for sy in SYS))
    haz = [(arm, K) for arm in c['arms'] for K in (1, 2, 3, 0) if CI[(arm, K, 'RELAY')][1] < 0]
    ben = [(arm, K) for arm in c['arms'] for K in OWN[arm] if CI[(arm, K, 'RELAY')][0] > 0]
    upg = [(arm, K) for arm, K in haz if arm == 'relayCK1_st' and K != 1]
    frac = lambda sy, arm, K: (G[(arm, K, sy)] - G[(arm, K, 'RELAY')]) / (-G[(arm, K, 'RELAY')])
    keep = lambda sy, arm, K: G[(arm, K, sy)] / G[(arm, K, 'RELAY')]
    cells = [(arm, K) for arm in c['arms'] for K in (1, 2, 3, 0)]
    from scipy.stats import spearmanr       # AVERAGE ranks for ties (audit 03/10 14:1x; pre-result correction, protocol Amendment 1)
    sp = {sy: float(spearmanr([FR[(arm, K, sy)] for arm, K in cells], [-G[(arm, K, 'RELAY')] for arm, K in cells]).statistic) for sy in SYS[1:]}
    V[net] = dict(haz=haz, ben=ben, upg=upg, frac={sy: {f'{a}_{K}': frac(sy, a, K) for a, K in upg} for sy in SYS[1:]},
                  keep={sy: {f'{a}_{K}': keep(sy, a, K) for a, K in ben} for sy in SYS[1:]}, sp=sp,
                  fm3=all(G[(a, K, 'FB_S')] >= G[(a, K, 'FB_Mq')] - 0.3 for a, K in cells))
    L.append(f'{net}: hazard {haz}; benefit {ben}; upgrade {upg}; Spearman(rate, -gain RELAY) ' + ', '.join(f'{k} {v:+.2f}' for k, v in sp.items()))
    L.append(f'{net}: recovered fraction at upgrade cells ' + json.dumps({sy: {k: round(v, 2) for k, v in d.items()} for sy, d in V[net]['frac'].items()}))
    L.append(f'{net}: kept fraction at benefit cells ' + json.dumps({sy: {k: round(v, 2) for k, v in d.items()} for sy, d in V[net]['keep'].items()}))
if '4x4' in V:
    v = V['4x4']; sv = lambda b: 'SUPPORTED' if b else 'NOT SUPPORTED'
    L.append(f'FM1 FB_Mq recovers >= 1/2 at the 4x4 upgrade hazard: ' + (sv(all(x >= 0.5 for x in v['frac']['FB_Mq'].values())) if v['upg'] else 'not tested'))
    fm2 = any(x < 0.75 for n in V for x in V[n]['keep']['FB_M'].values()) and all(x >= 0.75 for n in V for x in V[n]['keep']['FB_S'].values())
    L.append(f'FM2 the chi2 gate is costly on own channels while FB_S is not (networks used: {sorted(V)}; protocol: both): {sv(fm2) if len(V) == 2 else "INCOMPLETE"}')
    L.append(f'FM3 FB_S >= FB_Mq - 0.3 in every 4x4 cell: {sv(v["fm3"])}')
    L.append(f'FM4 Spearman(FB_Mq rate, -gain RELAY) {v["sp"]["FB_Mq"]:+.2f} >= 0.6 (4x4): {sv(v["sp"]["FB_Mq"] >= 0.6)}')
txt = '\n'.join(L); print(txt); Path('research/marl_budget/e3_fallback_mahal_20261003/report.txt').write_text(txt + '\n')
