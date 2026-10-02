#!/usr/bin/env python3
"""Report of PROTOCOL_E3_DEMAND_FRONTIER_20261001.md (written 01/10/2026 10:4x EDT, BEFORE the runs).

Recomputes the predictors from the V-D10 depth files and REFUSES to report unless they equal the protocol table (4 dp);
reads the panel 2801-2864 runs; P1 (frontier shape vs the demand curve, against STEP and LINEAR nulls), P2
(Spearman(N_s, mean-over-K gain) >= 0.5), secondaries.  Self-checks: every manifest COMPLETE/PASS, 128 episodes
seed2801..seed2864 x load8/load16 per arm, the expected checkpoint in each manifest, rule 'prefix' (relay) / 'none' (Z).
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

M = Path('research/marl_budget'); P = M / 'e3_demand_frontier_20261001'; A = 'research/marl_budget/e3_delivery_actors_20260929'
VD = M / 'e3_decision_depth_ten_20261001'
EPS = [f'seed{s}_load{h}' for s in range(2801, 2865) for h in (8, 16)]
TS = sorted({e.split('_')[0] for e in EPS}); IDX = {u: [i for i, e in enumerate(EPS) if e.startswith(u + '_')] for u in TS}
KS = list(range(1, 8)); SEEDS = list(range(10))
TABLE = {0: [0.0807, 0.1321, 0.1607, 0.1855, 0.2155, 0.2543, 0.2879], 1: [0.1045, 0.1673, 0.2044, 0.2348, 0.2824, 0.3555, 0.4186],
         2: [0.1001, 0.1538, 0.1825, 0.2068, 0.2465, 0.3019, 0.3591], 3: [0.0695, 0.1052, 0.1295, 0.1542, 0.1840, 0.2197, 0.2484],
         4: [0.0857, 0.1275, 0.1537, 0.1782, 0.2205, 0.2681, 0.3086], 5: [0.0579, 0.1067, 0.1479, 0.1860, 0.2250, 0.2625, 0.2945],
         6: [0.0806, 0.1232, 0.1552, 0.1779, 0.2092, 0.2419, 0.2727], 7: [0.1270, 0.1817, 0.2107, 0.2285, 0.2691, 0.3299, 0.3826],
         8: [0.0318, 0.0517, 0.0665, 0.0789, 0.0904, 0.1014, 0.1122], 9: [0.0533, 0.0781, 0.0990, 0.1162, 0.1304, 0.1466, 0.1614]}
DSHAPE = [0.278, 0.431, 0.531, 0.614, 0.728, 0.872, 1.000]


def predictors():
    S, N = {}, {}
    for s in SEEDS:
        d = np.load(VD / f'cage_s{s}_agefirst_low/depth.npz')['depth'][:, 0, 1].astype(int)
        q = [float(np.mean(d > k)) for k in range(8)]
        S[s] = [q[0] - q[K] for K in KS]; N[s] = q[0]
        if max(abs(round(x, 4) - y) for x, y in zip(S[s], TABLE[s])) > 1e-9:
            raise SystemExit(f'PREDICTOR MISMATCH seed {s}: {S[s]} vs protocol {TABLE[s]}')
    sh = np.mean([S[s] for s in SEEDS], 0); sh = sh / sh[-1]
    if max(abs(round(x, 3) - y) for x, y in zip(sh, DSHAPE)) > 1e-9:
        raise SystemExit(f'SHAPE MISMATCH {sh}')
    return S, N


def load(tag, actor, rule):
    d = P / tag
    if not (d / 'manifest.json').exists():
        return None
    m = json.loads((d / 'manifest.json').read_text())
    assert m.get('status') == 'COMPLETE' and m.get('self_check') == 'PASS', tag
    assert f'{actor}={A}/{actor}/ckpt_best.pt' in str(m.get('args')), tag
    rows = {r['episode']: r['queue_sum'] for r in json.loads((d / 'rows.json').read_text()) if r['rule'] == rule}
    assert sorted(rows) == sorted(EPS), f'{tag}: {len(rows)} episodes'
    return np.array([rows[e] for e in EPS], float)


def gain(x, z, ii=None):
    return -(x.sum() / z.sum() - 1) * 100 if ii is None else -(x[ii].sum() / z[ii].sum() - 1) * 100


def mad(g, x):
    return float(np.mean(np.abs(np.asarray(g) - np.asarray(x))))


def main():
    S, N = predictors()
    Z = {s: load(f'Z_s{s}', f'distill_none_s{s}', 'none') for s in SEEDS}
    X = {(s, K): load(f'R_s{s}_const{K}', f'relay6Cage_st_s{s}', 'prefix') for s in SEEDS for K in KS}
    miss = [f'Z_s{s}' for s in SEEDS if Z[s] is None] + [f'R_s{s}_const{K}' for (s, K), v in X.items() if v is None]
    out = dict(missing=miss); L = []
    if miss:
        L.append(f'INCOMPLETE: {len(miss)} arms missing ({miss[:6]} ...). No verdict.')
    else:
        G = {s: [gain(X[(s, K)], Z[s]) for K in KS] for s in SEEDS}
        gbar = np.mean([G[s] for s in SEEDS], 0); gt = gbar / gbar.max()
        mD, mS, mL = mad(gt, DSHAPE), mad(gt, [1.0] * 7), mad(gt, [K / 7 for K in KS])
        P1 = bool(mD < mS and mD < mL)
        rng = np.random.default_rng(0); wins = 0; draws = 4000
        for _ in range(draws):
            ss = rng.choice(SEEDS, len(SEEDS)); gb = []
            for s in ss:
                ii = np.concatenate([IDX[TS[k]] for k in rng.choice(len(TS), len(TS))])
                gb.append([gain(X[(s, K)], Z[s], ii) for K in KS])
            g = np.mean(gb, 0); g = g / g.max() if g.max() > 0 else g
            wins += mad(g, DSHAPE) < min(mad(g, [1.0] * 7), mad(g, [K / 7 for K in KS]))
        Gbar = {s: float(np.mean(G[s])) for s in SEEDS}
        rho2 = float(spearmanr([N[s] for s in SEEDS], [Gbar[s] for s in SEEDS]).correlation); P2 = bool(rho2 >= 0.5)
        out.update(gain=G, gbar=gbar.tolist(), gtilde=gt.tolist(), MAD=dict(demand=mD, step=mS, linear=mL), P1=P1,
                   P1_bootstrap_share=wins / draws, rho_N_Gbar=rho2, P2=P2)
        L.append('mean gain by K: ' + ' '.join(f'K{K}:{g:+.2f}' for K, g in zip(KS, gbar)))
        L.append('normalised g~(K): ' + ' '.join(f'{x:.3f}' for x in gt) + ' | demand D~: ' + ' '.join(f'{x:.3f}' for x in DSHAPE))
        L.append(f'P1 MAD demand {mD:.3f} vs step {mS:.3f} vs linear {mL:.3f} -> {"SUPPORTED" if P1 else "NOT SUPPORTED"} '
                 f'(bootstrap share demand best {wins / draws:.3f})')
        L.append(f'P2 Spearman(N_s, mean-over-K gain) = {rho2:.3f} -> {"SUPPORTED" if P2 else "NOT SUPPORTED"} (>= 0.5)')
        kill = 'STOP the demand-curve line' if not (P1 or P2) else ('scalar law stands, curve dropped' if P2 and not P1 else
                                                                    ('curve: development evidence only' if P1 and not P2 else 'both hold'))
        out['kill_rule'] = kill; L.append(f'KILL RULE: {kill}')
        for K_i, K in enumerate(KS):
            rS = float(spearmanr([S[s][K_i] for s in SEEDS], [G[s][K_i] for s in SEEDS]).correlation)
            rN = float(spearmanr([N[s] for s in SEEDS], [G[s][K_i] for s in SEEDS]).correlation)
            out.setdefault('secondary', {})[f'K{K}'] = dict(rho_S=rS, rho_N=rN)
            L.append(f'  secondary K={K}: Spearman(S_s(K), gain) {rS:+.3f}, Spearman(N_s, gain) {rN:+.3f}')
        for s in SEEDS:
            L.append(f'  s{s}: ' + ' '.join(f'{g:+.2f}' for g in G[s]))
    text = '\n'.join(L); print(text)
    (M / 'e3_demand_frontier_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_demand_frontier_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
