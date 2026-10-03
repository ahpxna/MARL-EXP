#!/usr/bin/env python3
"""Report of PROTOCOL_E3_AGE_COUNTERFACTUAL_20261001.md (EXPLORATORY).  Y1-Y3 and the iid control as stated there."""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); D = M / 'e3_age_cf_20261001'; SEEDS = range(10)


def main():
    Q = {}
    for K in (1, 0):
        for s in SEEDS:
            d = D / f's{s}_K{K}'
            if not (d / 'manifest.json').exists():
                print('INCOMPLETE', d.name); return
            z = np.load(d / 'flags.npz')
            Q[(s, K)] = {k: float(z[k].mean()) for k in ('protoS', 'clip', 'drop', 'zok')} | {'old': float((z['n_old'] > 0).mean())}
    L = ['K | acc_S | acc_clip | acc_drop | acc_Z | share of steps with a copy older than A']
    mu = {}
    for K in (1, 0):
        mu[K] = {k: np.mean([Q[(s, K)][k] for s in SEEDS]) for k in Q[(0, K)]}
        L.append(f'{K if K else "iid"} | {mu[K]["protoS"]:.3f} | {mu[K]["clip"]:.3f} | {mu[K]["drop"]:.3f} | {mu[K]["zok"]:.3f} | {mu[K]["old"]:.3f}')
    m = mu[1]
    Y1 = m['clip'] - m['protoS'] >= 0.02 and m['clip'] >= m['zok']
    Y2 = m['drop'] >= m['zok'] and m['drop'] > m['protoS']
    Y3 = m['clip'] <= m['protoS']
    C = abs(mu[0]['clip'] - mu[0]['protoS']) <= 0.01 and abs(mu[0]['drop'] - mu[0]['protoS']) <= 0.01
    per = lambda k: sum(Q[(s, 1)][k] > Q[(s, 1)]['zok'] for s in SEEDS)
    L += [f'Y1 age-feature extrapolation (clip - S >= 0.02 and clip >= Z): {Y1}  [clip - S {m["clip"] - m["protoS"]:+.3f}; clip > Z on {per("clip")}/10]',
          f'Y2 drop >= Z and > S: {Y2}  [drop - Z {m["drop"] - m["zok"]:+.3f}; drop > Z on {per("drop")}/10]',
          f'Y3 clip <= S: {Y3}',
          f'control iid |clip - S| {abs(mu[0]["clip"] - mu[0]["protoS"]):.3f}, |drop - S| {abs(mu[0]["drop"] - mu[0]["protoS"]):.3f} (<= 0.01): {C}']
    G3 = {int(s): v for s, v in json.loads((M / 'e3_harm_prospective_report_20261001.json').read_text())['gain'].items()}
    for k in ('protoS', 'clip', 'drop'):
        r = spearmanr([Q[(s, 1)][k] - Q[(s, 1)]['zok'] for s in SEEDS], [G3[s][0] for s in SEEDS]).correlation
        L.append(f'  rho({k} - Z at K=1, gain(1) panel 3001) {r:+.3f}')
    text = '\n'.join(L); print(text)
    (M / 'e3_age_cf_report_20261001.json').write_text(json.dumps(dict(per_cell={f's{s}_K{K}': v for (s, K), v in Q.items()},
        Y1=bool(Y1), Y2=bool(Y2), Y3=bool(Y3), control=bool(C)), indent=1))
    (M / 'e3_age_cf_report_20261001.txt').write_text('EXPLORATORY\n' + text + '\n')


if __name__ == '__main__':
    main()
