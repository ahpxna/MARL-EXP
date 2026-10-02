#!/usr/bin/env python3
"""Comparators C1-C4 of PROTOCOL_E3_HARM_PROSPECTIVE_ADDENDUM1_20261001.md (written 11:51:58 EDT, before the target read).
No pass/fail rule.  Reported against the prospective panel 3001-3064 (K = 1, 2, 3) and, EXPLORATORY, the step-1 panel
2801-2864 (K = 1, 2, 3, 5, 7).  Spearman with Bonett-Wright 95 % intervals, n = 10 seeds.
C1 acc_S = P(relay student's action in A_0.25); C2 -harm_S; C3 acc_E = 1 - N_dev (teacher on the local-only view), all on the
relay student's own closed-loop states of the development panel seed901-904 x 8/16; C4 dev-panel closed-loop gain (relay
rows of e3_protocol_demand_20261001 vs e3_dev_Z_20261001).  Identity checked: net_S = acc_S - acc_E.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); SEEDS = range(10)
DEV = [f'seed{s}_load{h}' for s in (901, 902, 903, 904) for h in (8, 16)]


def bw(r, n=10):
    z = np.arctanh(np.clip(r, -0.999999, 0.999999)); se = np.sqrt((1 + r * r / 2) / (n - 3))
    return float(np.tanh(z - 1.96 * se)), float(np.tanh(z + 1.96 * se))


def rows(path, rule=None):
    return {r['episode']: r['queue_sum'] for r in json.loads(path.read_text()) if rule is None or r.get('rule') == rule}


def preds(K):
    d = json.loads((M / 'e3_protocol_demand_report_20261001.json').read_text())['per_cell']
    Nv = {int(k): v for k, v in json.loads((M / 'e3_decision_depth_ten_report_20261001.json').read_text())['primary_cache']['N'].items()}
    mg = {int(k): v['margin'] for k, v in json.loads((M / 'e3_exact_demand_report_20261001.json').read_text())['predictors'].items()}
    P = {k: {} for k in ('net_S', 'S_best', 'C1_accS', 'C2_-harmS', 'C3_accE', 'C4_devgain', 'N_VD10', 'margin')}
    for s in SEEDS:
        z = np.load(M / f'e3_protocol_demand_20261001/s{s}_K{K}/flags.npz'); n, ps = z['need'], z['protoS']
        c = d[f's{s}_K{K}']; accS, accE = float(ps.mean()), float(1 - n.mean())
        if abs((accS - accE) - c['net_S']) > 1e-12:
            raise SystemExit(f'IDENTITY FAIL s{s} K{K}')
        r = rows(M / f'e3_protocol_demand_20261001/s{s}_K{K}/rows.json'); zz = rows(M / f'e3_dev_Z_20261001/Z_s{s}/rows.json', 'none')
        if sorted(r) != sorted(DEV) or sorted(zz) != sorted(DEV):
            raise SystemExit(f'DEV EPISODES MISMATCH s{s} K{K}')
        P['net_S'][s] = c['net_S']; P['S_best'][s] = c['S_best']; P['C1_accS'][s] = accS; P['C2_-harmS'][s] = -c['harm_S']
        P['C3_accE'][s] = accE; P['C4_devgain'][s] = -(sum(r[e] for e in DEV) / sum(zz[e] for e in DEV) - 1) * 100
        P['N_VD10'][s] = Nv[s]; P['margin'][s] = mg[s]
    return P


def block(name, G, KS):
    L = [f'== {name} =='] ; out = {}
    for i, K in enumerate(KS):
        P = preds(K); g = [G[s][i] for s in SEEDS]; out[K] = {}
        parts = []
        for k, v in P.items():
            r = float(spearmanr([v[s] for s in SEEDS], g).correlation); lo, hi = bw(r); out[K][k] = dict(rho=r, ci=[lo, hi])
            parts.append(f'{k} {r:+.3f} [{lo:+.2f},{hi:+.2f}]')
        lev = dict(mean_gain=float(np.mean(g)), mean_net_S=float(np.mean(list(P['net_S'].values()))), mean_devgain=float(np.mean(list(P['C4_devgain'].values()))))
        out[K]['levels'] = lev
        L.append(f'K{K}: mean target gain {lev["mean_gain"]:+.2f} % | mean dev gain {lev["mean_devgain"]:+.2f} % | mean net_S {lev["mean_net_S"]:+.3f}')
        L += ['   ' + p for p in parts]
    return L, out


def main():
    L = []; out = {}
    pr = M / 'e3_harm_prospective_report_20261001.json'
    if pr.exists():
        G = {int(s): v for s, v in json.loads(pr.read_text())['gain'].items()}
        a, b = block('PROSPECTIVE panel 3001-3064 (comparators fixed in Addendum 1)', G, (1, 2, 3)); L += a; out['prospective'] = b
    else:
        L.append('prospective report not present')
    G1 = {int(s): v for s, v in json.loads((M / 'e3_demand_frontier_report_20261001.json').read_text())['gain'].items()}
    G1 = {s: [G1[s][K - 1] for K in (1, 2, 3, 5, 7)] for s in SEEDS}
    a, b = block('EXPLORATORY step-1 panel 2801-2864', G1, (1, 2, 3, 5, 7)); L += a; out['step1_exploratory'] = b
    text = '\n'.join(L); print(text)
    (M / 'e3_harm_prospective_comparators_20261001.json').write_text(json.dumps(out, indent=1))
    (M / 'e3_harm_prospective_comparators_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
