#!/usr/bin/env python3
"""Report of PROTOCOL_E3_HARM_PROSPECTIVE_20261001.md (written 01/10/2026 11:4x EDT, before the runs).
H1 Spearman(net_S(1), gain(1)) >= 0.5 and > Spearman(S_best(1), gain(1)); H2 the K = 1 loss replicates (two-level bootstrap
lower bound of the relay effect above 0); H3 mean over K of Spearman(net_S(K), gain(K)) >= 0.5.  Predictors are the protocol
table (re-read from the exploratory report JSON and checked equal).
"""
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

sys.path.insert(0, str(Path(__file__).resolve().parent))
import MARL_e3_demand_frontier_report as F

M = Path('research/marl_budget'); F.P = M / 'e3_harm_prospective_20261001'
F.EPS = [f'seed{s}_load{h}' for s in range(3001, 3065) for h in (8, 16)]
F.TS = sorted({e.split('_')[0] for e in F.EPS}); F.IDX = {u: [i for i, e in enumerate(F.EPS) if e.startswith(u + '_')] for u in F.TS}
SEEDS = range(10); KS = (1, 2, 3)
NET = {0: (0.0705, 0.1870, 0.2142), 1: (0.1768, 0.2601, 0.2975), 2: (0.0689, 0.2366, 0.2762), 3: (0.0454, 0.1405, 0.1661),
       4: (0.1287, 0.1939, 0.2276), 5: (0.0860, 0.1795, 0.1955), 6: (-0.0374, 0.1004, 0.1159), 7: (0.2302, 0.3072, 0.3269),
       8: (0.0080, 0.0187, 0.0363), 9: (0.1437, 0.1640, 0.1704)}
BEST = {0: (0.1811, 0.2292, 0.2650), 1: (0.1635, 0.2548, 0.3093), 2: (0.1709, 0.2393, 0.2826), 3: (0.1533, 0.1939, 0.2179),
        4: (0.1699, 0.2366, 0.2794), 5: (0.1704, 0.2260, 0.2628), 6: (0.1197, 0.1960, 0.2067), 7: (0.2158, 0.2682, 0.3355),
        8: (0.0582, 0.0673, 0.0748), 9: (0.1998, 0.2233, 0.2158)}


def check_table():
    d = json.loads((M / 'e3_protocol_demand_report_20261001.json').read_text())['per_cell']
    for s in SEEDS:
        for i, K in enumerate(KS):
            if abs(round(d[f's{s}_K{K}']['net_S'], 4) - NET[s][i]) > 1e-9 or abs(round(d[f's{s}_K{K}']['S_best'], 4) - BEST[s][i]) > 1e-9:
                raise SystemExit(f'PREDICTOR MISMATCH s{s} K{K}')


def main():
    check_table()
    Z = {s: F.load(f'Z_s{s}', f'distill_none_s{s}', 'none') for s in SEEDS}
    X = {(s, K): F.load(f'R_s{s}_const{K}', f'relay6Cage_st_s{s}', 'prefix') for s in SEEDS for K in KS}
    if any(v is None for v in Z.values()) or any(v is None for v in X.values()):
        print('INCOMPLETE'); return
    G = {s: [F.gain(X[(s, K)], Z[s]) for K in KS] for s in SEEDS}
    r = lambda pred, i: float(spearmanr([pred[s][i] for s in SEEDS], [G[s][i] for s in SEEDS]).correlation)
    rn = [r(NET, i) for i in range(3)]; rb = [r(BEST, i) for i in range(3)]
    H1 = rn[0] >= 0.5 and rn[0] > rb[0]; H3 = float(np.mean(rn)) >= 0.5
    rng = np.random.default_rng(0); bs = []
    for _ in range(4000):
        ss = rng.choice(list(SEEDS), 10)
        bs.append(np.mean([-F.gain(X[(s, 1)], Z[s], np.concatenate([F.IDX[F.TS[k]] for k in rng.choice(len(F.TS), len(F.TS))])) for s in ss]))
    lo, hi = np.percentile(bs, [2.5, 97.5]); m1 = float(np.mean([G[s][0] for s in SEEDS])); H2 = bool(lo > 0)
    Nv = {int(k): v for k, v in json.loads((M / 'e3_decision_depth_ten_report_20261001.json').read_text())['primary_cache']['N'].items()}
    mg = {int(k): v['margin'] for k, v in json.loads((M / 'e3_exact_demand_report_20261001.json').read_text())['predictors'].items()}
    comp = {K: dict(N=float(spearmanr([Nv[s] for s in SEEDS], [G[s][i] for s in SEEDS]).correlation),
                    margin=float(spearmanr([mg[s] for s in SEEDS], [G[s][i] for s in SEEDS]).correlation)) for i, K in enumerate(KS)}
    out = dict(gain=G, rho_net=rn, rho_best=rb, H1=bool(H1), H2=H2, H3=bool(H3), mean_gain_K1=m1, relay_effect_K1_ci=[float(lo), float(hi)],
               comparators=comp)
    L = ['mean gain by K: ' + ' '.join(f'K{K}:{np.mean([G[s][i] for s in SEEDS]):+.2f}' for i, K in enumerate(KS)),
         f'H1 rho(net_S(1), gain(1)) {rn[0]:+.3f} vs rho(S_best(1)) {rb[0]:+.3f} -> {"SUPPORTED" if H1 else "NOT SUPPORTED"}',
         f'H2 K = 1 loss: mean gain {m1:+.2f} %, relay effect 95 % [{lo:+.2f}, {hi:+.2f}] % -> {"SUPPORTED" if H2 else "NOT SUPPORTED"}',
         f'H3 mean rho(net_S(K), gain(K)) = {np.mean(rn):+.3f} ({" ".join(f"{x:+.3f}" for x in rn)}) -> {"SUPPORTED" if H3 else "NOT SUPPORTED"}',
         'comparators per K: ' + ' | '.join(f'K{K}: N {c["N"]:+.3f} margin {c["margin"]:+.3f}' for K, c in comp.items())]
    L += [f'  s{s}: ' + ' '.join(f'{g:+.2f}' for g in G[s]) for s in SEEDS]
    text = '\n'.join(L); print(text)
    (M / 'e3_harm_prospective_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_harm_prospective_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
