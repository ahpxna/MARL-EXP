#!/usr/bin/env python3
"""Report of PROTOCOL_E3_PROTOCOL_CONDITIONED_DEMAND_20261001.md (EXPLORATORY; written 01/10/2026 11:0x EDT).

Per (seed, K): N, S_best, S_protoT, S_protoS, harm_T, harm_S, net_X = S_protoX - harm_X, and the gaps N - S_best
(insufficiency under ideal delivery), S_best - S_protoT (delivery loss), S_protoT - S_protoS (usability).  Compared with the
realised gains of PROTOCOL_E3_DEMAND_FRONTIER_20261001 (read from its report JSON).  Expectations E1-E3 as stated.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); D = M / 'e3_protocol_demand_20261001'; SEEDS = range(10); KS = (1, 2, 3, 5, 7)


def main():
    G = {int(s): v for s, v in json.loads((M / 'e3_demand_frontier_report_20261001.json').read_text())['gain'].items()}
    Q = {}
    for s in SEEDS:
        for K in KS:
            d = D / f's{s}_K{K}'
            if not (d / 'manifest.json').exists():
                print('INCOMPLETE', d.name); return
            z = np.load(d / 'flags.npz'); n, b, pt, ps = z['need'], z['best'], z['protoT'], z['protoS']
            f = lambda x: float(np.mean(x))
            Q[(s, K)] = dict(N=f(n), S_best=f(n & b), S_protoT=f(n & pt), S_protoS=f(n & ps), harm_T=f(~n & ~pt), harm_S=f(~n & ~ps))
            Q[(s, K)]['net_T'] = Q[(s, K)]['S_protoT'] - Q[(s, K)]['harm_T']; Q[(s, K)]['net_S'] = Q[(s, K)]['S_protoS'] - Q[(s, K)]['harm_S']
    L = ['K | N | S_best | S_protoT | S_protoS | harm_T | harm_S | net_S | realised gain (protocol 1) | rho(net_S,gain) | rho(S_best,gain)']
    out = {}
    for K in KS:
        mean = {k: float(np.mean([Q[(s, K)][k] for s in SEEDS])) for k in Q[(0, K)]}
        g = [G[s][K - 1] for s in SEEDS]
        rn = float(spearmanr([Q[(s, K)]['net_S'] for s in SEEDS], g).correlation)
        rb = float(spearmanr([Q[(s, K)]['S_best'] for s in SEEDS], g).correlation)
        out[f'K{K}'] = dict(mean=mean, gain_mean=float(np.mean(g)), rho_netS=rn, rho_Sbest=rb)
        L.append(f'{K} | {mean["N"]:.3f} | {mean["S_best"]:.3f} | {mean["S_protoT"]:.3f} | {mean["S_protoS"]:.3f} | {mean["harm_T"]:.3f} | '
                 f'{mean["harm_S"]:.3f} | {mean["net_S"]:+.3f} | {np.mean(g):+.2f} % | {rn:+.3f} | {rb:+.3f}')
    netS = {K: out[f'K{K}']['mean']['net_S'] for K in KS}; harmS = {K: out[f'K{K}']['mean']['harm_S'] for K in KS}
    E1 = min(netS, key=netS.get) == 1 and max(harmS, key=harmS.get) == 1
    E2 = float(np.mean([out[f'K{K}']['rho_netS'] for K in KS])) > float(np.mean([out[f'K{K}']['rho_Sbest'] for K in KS]))
    loss = {K: out[f'K{K}']['mean']['S_best'] - out[f'K{K}']['mean']['S_protoT'] for K in KS}
    L.append(f'E1 (K = 1 has the lowest net_S and the largest harm_S): {E1}')
    L.append(f'E2 (mean over K of rho(net_S, gain) > that of rho(S_best, gain)): {E2}')
    L.append('E3 delivery loss S_best - S_protoT by K: ' + ' '.join(f'K{K}:{v:+.3f}' for K, v in loss.items()))
    out.update(E1=bool(E1), E2=bool(E2), delivery_loss=loss, per_cell={f's{s}_K{K}': v for (s, K), v in Q.items()})
    text = '\n'.join(L); print(text)
    (M / 'e3_protocol_demand_report_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_protocol_demand_report_20261001.txt').write_text('EXPLORATORY (written after protocol 1 results)\n' + text + '\n')


if __name__ == '__main__':
    main()
