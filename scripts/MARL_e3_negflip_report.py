#!/usr/bin/env python3
"""Report of PROTOCOL_E3_NEGFLIP_VS_Z_20261001.md (EXPLORATORY; written 01/10/2026 11:58 EDT before the probe ran).
Per (seed, K): acc_S, acc_Z, acc_E, repair_Z = P(not zok, protoS), flip_Z = P(zok, not protoS), net_Z = acc_S - acc_Z,
net_S = acc_S - acc_E (identity re-checked against e3_protocol_demand for K = 1, 2, 3), view ages.  X1-X4 as stated.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); D = M / 'e3_negflip_20261001'; SEEDS = range(10); KS = (1, 2, 3, 0)


def bw(r, n=10):
    z = np.arctanh(np.clip(r, -0.999999, 0.999999)); se = np.sqrt((1 + r * r / 2) / (n - 3))
    return float(np.tanh(z - 1.96 * se)), float(np.tanh(z + 1.96 * se))


def main():
    F = {}
    for s in SEEDS:
        for K in KS:
            d = D / f's{s}_K{K}'
            if not (d / 'manifest.json').exists():
                print('INCOMPLETE', d.name); return
            m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS'
            F[(s, K)] = dict(np.load(d / 'flags.npz'))
    pdm = json.loads((M / 'e3_protocol_demand_report_20261001.json').read_text())['per_cell']
    Q = {}
    for (s, K), z in F.items():
        n, zk, ps = z['need'], z['zok'], z['protoS']
        q = dict(acc_S=ps.mean(), acc_Z=zk.mean(), acc_E=1 - n.mean(), repair_Z=(~zk & ps).mean(), flip_Z=(zk & ~ps).mean())
        q['net_Z'] = q['acc_S'] - q['acc_Z']; q['net_S'] = q['acc_S'] - q['acc_E']
        if K and abs(q['net_S'] - pdm[f's{s}_K{K}']['net_S']) > 1e-12:
            raise SystemExit(f'net_S differs from the protocol-demand probe s{s} K{K}')
        ok = z['mean_age'] >= 0; q['mean_age'] = float(z['mean_age'][ok].mean()); q['n_ent'] = float(z['n_ent'].mean())
        Q[(s, K)] = {k: float(v) for k, v in q.items()}
    G1 = {int(s): v for s, v in json.loads((M / 'e3_demand_frontier_report_20261001.json').read_text())['gain'].items()}
    G3 = {int(s): v for s, v in json.loads((M / 'e3_harm_prospective_report_20261001.json').read_text())['gain'].items()}
    L = ['K | acc_S | acc_Z | acc_E | repair_Z | flip_Z | net_Z | net_S | mean age (steps) | entries | gain 2801 | gain 3001']
    for K in KS:
        mu = {k: np.mean([Q[(s, K)][k] for s in SEEDS]) for k in Q[(0, K)]}
        g1 = f'{np.mean([G1[s][K - 1] for s in SEEDS]):+.2f}' if K else '  -  '; g3 = f'{np.mean([G3[s][K - 1] for s in SEEDS]):+.2f}' if K else '  -  '
        L.append(f'{K if K else "iid"} | {mu["acc_S"]:.3f} | {mu["acc_Z"]:.3f} | {mu["acc_E"]:.3f} | {mu["repair_Z"]:.3f} | {mu["flip_Z"]:.3f} | '
                 f'{mu["net_Z"]:+.3f} | {mu["net_S"]:+.3f} | {mu["mean_age"]:.2f} | {mu["n_ent"]:.2f} | {g1} | {g3}')
    nz = {K: np.mean([Q[(s, K)]['net_Z'] for s in SEEDS]) for K in KS}
    X1 = nz[1] < 0 < min(nz[2], nz[3])
    L.append(f'X1 mean net_Z(1) {nz[1]:+.4f} < 0 < net_Z(2) {nz[2]:+.4f}, net_Z(3) {nz[3]:+.4f}: {X1}'
             f' | seeds with net_Z(1) < 0: {sum(Q[(s, 1)]["net_Z"] < 0 for s in SEEDS)}/10')
    if not X1:
        L.append('X2 applies: the K = 1 loss is not visible as A_0.25 decision flips against Z')
    age_up = [Q[(s, 1)]['mean_age'] > Q[(s, 0)]['mean_age'] for s in SEEDS]
    old_f, old_n, new_f, new_n = 0, 0, 0, 0
    for s in SEEDS:
        zi = F[(s, 0)]; p95 = np.percentile(zi['max_age'][zi['max_age'] >= 0], 95)
        z = F[(s, 1)]; flip = z['zok'] & ~z['protoS']; old = z['max_age'] > p95
        old_f += flip[old].sum(); old_n += old.sum(); new_f += flip[~old].sum(); new_n += (~old).sum()
    rr = (old_f / max(old_n, 1)) / (new_f / max(new_n, 1)) if new_f else float('nan')
    X3 = all(age_up) and rr > 1.5
    L.append(f'X3 mean age K=1 > iid on {sum(age_up)}/10 seeds; flip_Z(1) rate on steps with an entry older than the iid p95: '
             f'{old_f / max(old_n, 1):.3f} ({old_n} steps) vs {new_f / max(new_n, 1):.3f} ({new_n}) -> ratio {rr:.2f}: {X3}')
    out = dict(per_cell={f's{s}_K{K}': v for (s, K), v in Q.items()}, X1=bool(X1), X3=bool(X3), flip_old_ratio=float(rr))
    L.append('X4 Spearman with realised gains (n = 10, Bonett-Wright 95 %):')
    for K in (1, 2, 3):
        for name, G in (('2801', G1), ('3001', G3)):
            g = [G[s][K - 1] for s in SEEDS]; parts = []
            for k in ('net_Z', 'flip_Z', 'repair_Z', 'acc_Z', 'acc_S', 'net_S'):
                sign = -1 if k in ('flip_Z', 'acc_Z') else 1
                r = float(spearmanr([sign * Q[(s, K)][k] for s in SEEDS], g).correlation); lo, hi = bw(r)
                parts.append(f'{"-" if sign < 0 else ""}{k} {r:+.3f} [{lo:+.2f},{hi:+.2f}]'); out[f'rho_K{K}_{name}_{k}'] = r
            L.append(f'  K{K} panel {name}: ' + ' | '.join(parts))
    text = '\n'.join(L); print(text)
    (M / 'e3_negflip_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_negflip_report_20261001.txt').write_text('EXPLORATORY (both target panels read before this probe)\n' + text + '\n')


if __name__ == '__main__':
    main()
