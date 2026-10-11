#!/usr/bin/env python3
"""Report of PROTOCOL_E3_SUPPORT_FALLBACK_20261002.md (written 02/10/2026 22:3x EDT, before any panel run).
Gain vs Z (%) = -(sum queue_sys / sum queue_Z - 1) * 100 per seed, mean over seeds; 95 % interval by the two-level bootstrap of
scripts/MARL_e3_mixq_report.py (seeds, then traffic seeds).  Hazard cell: RELAY upper bound < 0; benefit cell: lower bound > 0.
Usage: MARL_e3_fallback_report.py [--root DIR] [--nets 3x3 4x4] [--smoke]"""
import argparse, json
from pathlib import Path
import numpy as np

NAME = {1: 'K1', 2: 'K2', 3: 'K3', 0: 'iid'}
NETS = {'3x3': dict(panel=range(4801, 4865), seeds=list(range(5)), arms=['relay6Cage_st', 'relayCK1_st', 'relayMIX_st', 'relayMIX2_st'],
                    systems=['FB_S', 'FB_S1', 'FB_S10', 'FB_F', 'FB_R']),
        '4x4': dict(panel=range(4901, 4965), seeds=list(range(10)), arms=['relayCage_st', 'relayCK1_st'], systems=['FB_S', 'FB_F', 'FB_R']),
        'nyc': dict(panel=range(5001, 5065), seeds=list(range(5)), arms=['relayCage_st', 'relayCK1_st'], systems=['FB_S', 'FB_F', 'FB_R'])}
OWN = {'relay6Cage_st': [0], 'relayCage_st': [0], 'relayCK1_st': [1], 'relayMIX_st': [1, 2, 3, 0], 'relayMIX2_st': [1, 0]}
TRAIN_K = {'relay6Cage_st': 0, 'relayCage_st': 0, 'relayCK1_st': 1}          # for the upgrade-hazard definition (fresher than training)


def main(a):
    root = Path(a.root); L = []; verdict = {}
    for net in a.nets:
        c = NETS[net]; panel = list(c['panel'])[:a.n_panel] if a.n_panel else list(c['panel']); seeds = c['seeds'][:a.n_seeds] if a.n_seeds else c['seeds']
        EPS = [f'seed{s}_load{h}' for s in panel for h in (8, 16)]; TS = [f'seed{s}' for s in panel]
        IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}; P = root / net

        def rows(d, system):
            m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS', d
            r = {x['episode']: x for x in json.loads((d / 'rows.json').read_text()) if x['system'] == system}
            assert set(EPS) <= set(r), (d, system, len(r))
            return np.array([r[e]['queue_sum'] for e in EPS], float), np.array([r[e]['flags'] / r[e]['decisions'] for e in EPS]) if 'flags' in r[EPS[0]] else None

        Z = {s: rows(P / f'Z_s{s}', 'Z')[0] for s in seeds}
        gain = lambda x, y, ii=None: -(x.sum() / y.sum() - 1) * 100 if ii is None else -(x[ii].sum() / y[ii].sum() - 1) * 100

        def boot(X):
            rng = np.random.default_rng(0); bs = []
            for _ in range(2000 if not a.smoke else 200):
                ss = rng.choice(seeds, len(seeds)); ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
                bs.append(np.mean([gain(X[s], Z[s], ii) for s in ss]))
            return [round(float(v), 2) for v in np.percentile(bs, [2.5, 97.5])]

        G, CI, FR, FA = {}, {}, {}, {}
        for arm in c['arms']:
            for s in seeds:
                cal = json.loads((P / f'cal_{arm}_s{s}' / 'calib.json').read_text()); FA[(arm, s)] = cal['false_alarm']
            for K in (1, 2, 3, 0):
                for sysn in ['RELAY'] + c['systems']:
                    X = {}; F = []
                    for s in seeds:
                        q, f = rows(P / f'FB_{arm}_s{s}_K{K}', sysn); X[s] = q
                        if f is not None:
                            F.append(f.mean())
                    G[(arm, K, sysn)] = float(np.mean([gain(X[s], Z[s]) for s in seeds])); CI[(arm, K, sysn)] = boot(X); FR[(arm, K, sysn)] = float(np.mean(F)) if F else 0.0
        L.append(f'== {net}: gain vs Z in % [95 %] (fallback rate)  seeds {seeds[0]}-{seeds[-1]}, panel {panel[0]}-{panel[-1]}')
        for arm in c['arms']:
            fa = {k: float(np.mean([FA[(arm, s)][k] if k != 'S_loo' else FA[(arm, s)]['S_loo']['3'] for s in seeds])) for k in ('S_loo', 'F', 'R')}
            L.append(f'{arm}  calibration false alarm: S(n_min 3, leave-one-episode-out) {fa["S_loo"]:.3f}, F {fa["F"]:.3f}, R {fa["R"]:.3f}')
            for K in (1, 2, 3, 0):
                L.append(f'  {NAME[K]:>3} | ' + ' | '.join(f'{sysn} {G[(arm, K, sysn)]:+.2f} {CI[(arm, K, sysn)]} ({FR[(arm, K, sysn)]:.2f})' for sysn in ['RELAY'] + c['systems']))
        haz = [(arm, K) for arm in c['arms'] for K in (1, 2, 3, 0) if CI[(arm, K, 'RELAY')][1] < 0]
        ben = [(arm, K) for arm in c['arms'] for K in OWN[arm] if CI[(arm, K, 'RELAY')][0] > 0]
        upg = [(arm, K) for arm, K in haz if arm in TRAIN_K and TRAIN_K[arm] == 1 and K != 1]
        rec = lambda sysn, cells: sum(G[(arm, K, sysn)] - G[(arm, K, 'RELAY')] for arm, K in cells)
        fb1 = all(G[(arm, K, 'FB_S')] >= 0.5 * G[(arm, K, 'RELAY')] for arm, K in haz)
        fb2 = all(G[(arm, K, 'FB_S')] >= 0.75 * G[(arm, K, 'RELAY')] for arm, K in ben)
        frac = lambda sysn, arm, K: (G[(arm, K, sysn)] - G[(arm, K, 'RELAY')]) / (-G[(arm, K, 'RELAY')])
        fb3 = None if not upg else all(frac('FB_S', arm, K) >= 0.5 and frac('FB_F', arm, K) < 0.25 for arm, K in upg)
        fb4 = None if not haz else rec('FB_S', haz) >= rec('FB_R', haz)
        fb5 = all(G[(arm, K, 'FB_S')] >= min(G[(arm, K, 'RELAY')], 0) - 0.5 for arm in c['arms'] for K in (1, 2, 3, 0))
        cells = [(arm, K) for arm in c['arms'] for K in (1, 2, 3, 0)]
        fr_ = np.array([FR[(arm, K, 'FB_S')] for arm, K in cells]); lg_ = np.array([-G[(arm, K, 'RELAY')] for arm, K in cells])
        from scipy.stats import spearmanr     # AVERAGE ranks for ties (audit 03/10 14:1x; was argsort-of-argsort: FB6 3x3 +0.46 -> +0.50, 4x4 +0.83 -> +0.88, verdicts unchanged)
        sp6 = float(spearmanr(fr_, lg_).statistic) if len(cells) > 2 else float('nan')
        fb6 = sp6 >= 0.6                                  # Addendum 2 (23:0x): coverage ranks the relay's loss
        sv = lambda v: 'not tested' if v is None else ('SUPPORTED' if v else 'NOT SUPPORTED')
        L += [f'hazard cells {haz}; benefit cells (own channel) {ben}; upgrade hazard cells {upg}',
              f'FB1 repair (FB_S >= half of RELAY deficit in every hazard cell) -> {sv(fb1 if haz else None)}',
              f'FB2 little cost (FB_S >= 0.75 RELAY in own-channel benefit cells) -> {sv(fb2 if ben else None)}',
              f'FB3 support, not freshness (upgrade hazard: FB_S recovers >= 1/2, FB_F < 1/4) -> {sv(fb3)}' + (' ' + ', '.join(f'{arm} {NAME[K]}: S {frac("FB_S", arm, K):.2f} F {frac("FB_F", arm, K):.2f}' for arm, K in upg) if upg else ''),
              f'FB4 joint >= range (recovered over hazard cells: S {rec("FB_S", haz):+.2f}, R {rec("FB_R", haz):+.2f}) -> {sv(fb4)}',
              f'FB5 no new failure (FB_S >= min(RELAY, 0) - 0.5 everywhere) -> {sv(fb5)}',
              f'FB6 out-of-support share ranks the relay loss (Spearman(FB_S rate, -gain RELAY) {sp6:+.2f} >= 0.6 over {len(cells)} cells) -> {sv(fb6)}']
        verdict[net] = dict(FB1=fb1 if haz else None, FB2=fb2 if ben else None, FB3=fb3, FB4=fb4, FB5=fb5, FB6=fb6, FB6_spearman=sp6, hazard=haz, benefit=ben, upgrade=upg)
    txt = '\n'.join(L); print(txt)
    if not a.smoke:
        tag = '_'.join(a.nets); (root / f'report_{tag}.txt').write_text(txt + '\n'); (root / f'verdict_{tag}.json').write_text(json.dumps(verdict, indent=1, default=str))


if __name__ == '__main__':
    p = argparse.ArgumentParser(); p.add_argument('--root', default='research/marl_budget/e3_fallback_20261002')
    p.add_argument('--nets', nargs='+', default=['3x3', '4x4']); p.add_argument('--smoke', action='store_true')
    p.add_argument('--n-panel', type=int, default=0); p.add_argument('--n-seeds', type=int, default=0)
    main(p.parse_args())
