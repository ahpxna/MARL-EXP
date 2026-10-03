#!/usr/bin/env python3
"""Report of PROTOCOL_E3_EXACT_DEMAND_1B_20261001.md (written 01/10/2026 10:5x EDT, before the v4 probes ran).

Predictors from the v4 probes (research/marl_budget/e3_decision_depth_v4_20261001/cage_s<s>/depth_v4.npz); the target is
PROTOCOL_E3_DEMAND_FRONTIER_20261001's, read through scripts/MARL_e3_demand_frontier_report.py's loader and checks.
"""
from __future__ import annotations
import json, sys
from pathlib import Path
import numpy as np
from scipy.stats import spearmanr

sys.path.insert(0, str(Path(__file__).resolve().parent))
import MARL_e3_demand_frontier_report as F

M = Path('research/marl_budget'); V4 = M / 'e3_decision_depth_v4_20261001'
SEEDS = F.SEEDS; KS = F.KS
D_S = dict(enumerate([0.081, 0.076, 0.069, 0.061, 0.080, 0.125, 0.102, 0.043, 0.031, 0.069]))


def predictors():
    out = {}
    for s in SEEDS:
        d = V4 / f'cage_s{s}'
        m = json.loads((d / 'manifest.json').read_text()); assert m['status'] == 'COMPLETE' and m['self_check'] == 'PASS'
        z = np.load(d / 'depth_v4.npz')
        Qe = [float(np.mean(z['dpre_empty'] > k)) for k in range(9)]; Qc = [float(np.mean(z['dpre_cache'] > k)) for k in range(9)]
        Qme = [float(np.mean(z['dmin_empty'] > k)) for k in range(9)]; Qmc = [float(np.mean(z['dmin_cache'] > k)) for k in range(9)]
        out[s] = dict(Qe=Qe, Qc=Qc, Gp=[Qe[0] - Qc[K] for K in KS], N=Qc[0], Qe0=Qe[0], Ae=sum(Qe[:8]), Ac=sum(Qc[:8]),
                      D=D_S[s], margin=float(np.mean(z['margin'])),
                      tax_empty=[Qe[k] - Qme[k] for k in range(9)], tax_cache=[Qc[k] - Qmc[k] for k in range(9)])
    return out


def main():
    try:
        Pd = predictors()
    except (FileNotFoundError, AssertionError) as e:
        print('INCOMPLETE predictors:', e); return
    Z = {s: F.load(f'Z_s{s}', f'distill_none_s{s}', 'none') for s in SEEDS}
    X = {(s, K): F.load(f'R_s{s}_const{K}', f'relay6Cage_st_s{s}', 'prefix') for s in SEEDS for K in KS}
    if any(v is None for v in Z.values()) or any(v is None for v in X.values()):
        print('INCOMPLETE target'); return
    G = {s: [F.gain(X[(s, K)], Z[s]) for K in KS] for s in SEEDS}; Gbar = {s: float(np.mean(G[s])) for s in SEEDS}
    gbar = np.mean([G[s] for s in SEEDS], 0); gt = gbar / gbar.max()
    rho = lambda pred: float(spearmanr([pred[s] for s in SEEDS], [Gbar[s] for s in SEEDS]).correlation)
    Gpbar = {s: float(np.mean(Pd[s]['Gp'])) for s in SEEDS}
    r1b = rho(Gpbar); rN = rho({s: Pd[s]['N'] for s in SEEDS})
    comps = {'N_s (cache Q(0))': rN, 'Q_empty(0)': rho({s: Pd[s]['Qe0'] for s in SEEDS}), 'area empty': rho({s: Pd[s]['Ae'] for s in SEEDS}),
             'area cache': rho({s: Pd[s]['Ac'] for s in SEEDS}), 'D_s': rho({s: Pd[s]['D'] for s in SEEDS}),
             'teacher margin': rho({s: Pd[s]['margin'] for s in SEEDS})}
    shape = np.mean([Pd[s]['Gp'] for s in SEEDS], 0); shape = shape / shape.max()
    mG, mS, mL = F.mad(gt, shape), F.mad(gt, [1.0] * 7), F.mad(gt, [K / 7 for K in KS])
    best_other = max(v for k, v in comps.items() if k != 'N_s (cache Q(0))')
    out = dict(rho_1b=r1b, P1b=bool(r1b >= 0.5), P1b_cmp=bool(r1b > rN), comparators=comps, best_other_comparator=best_other,
               spirit_fail=bool(best_other > r1b), shape=shape.tolist(), MAD=dict(Gprime=mG, step=mS, linear=mL),
               P1b_shape=bool(mG < mS and mG < mL), predictors={s: {k: v for k, v in Pd[s].items()} for s in SEEDS})
    L = [f'P1b Spearman(mean G\'_s, mean gain_s) = {r1b:.3f} -> {"SUPPORTED" if r1b >= 0.5 else "NOT SUPPORTED"}',
         f'P1b-cmp vs N_s ({rN:.3f}): {"SUPPORTED" if r1b > rN else "NOT SUPPORTED"}; comparators ' + ', '.join(f'{k} {v:+.3f}' for k, v in comps.items())
         + (' | a comparator other than N_s beats G\' (spirit failure)' if best_other > r1b else ''),
         f'P1b-shape MAD G\' {mG:.3f} vs step {mS:.3f} vs linear {mL:.3f} -> {"SUPPORTED" if out["P1b_shape"] else "NOT SUPPORTED"}; '
         f'shape {" ".join(f"{x:.3f}" for x in shape)}',
         'order tax (empty base) mean over seeds k=0..4: ' + ' '.join(f'{np.mean([Pd[s]["tax_empty"][k] for s in SEEDS]):.3f}' for k in range(5)),
         'order tax (cache base) mean over seeds k=0..4: ' + ' '.join(f'{np.mean([Pd[s]["tax_cache"][k] for s in SEEDS]):.3f}' for k in range(5))]
    # ADDENDUM 1 (written 11:00:34, before any target or predictor value was read): the sign of G'
    cells = [(s, Ki, Pd[s]['Gp'][Ki], G[s][Ki]) for s in SEEDS for Ki in range(len(KS))]
    neg = [c for c in cells if c[2] < 0]; pos = [c for c in cells if c[2] > 0]
    if not neg:
        out['P_sign'] = 'UNDETERMINED'; L.append('P-sign: UNDETERMINED (no cell with G\' < 0)')
    else:
        def delta(cs):
            n_ = [c for c in cs if c[2] < 0]; p_ = [c for c in cs if c[2] > 0]
            if not n_ or not p_:
                return np.nan
            return np.mean([c[3] < 0 for c in n_]) - np.mean([c[3] < 0 for c in p_])
        d0 = delta(cells); rng = np.random.default_rng(0); bs = []
        for _ in range(4000):
            ss = rng.choice(SEEDS, len(SEEDS)); bs.append(delta([c for s in ss for c in cells if c[0] == s]))
        lo = float(np.nanpercentile(bs, 2.5))
        out['P_sign'] = dict(delta=float(d0), lo=lo, supported=bool(d0 > 0 and lo > 0), n_neg=len(neg), n_pos=len(pos),
                             neg_per_K={K: sum(1 for c in neg if c[1] == Ki) for Ki, K in enumerate(KS)})
        L.append(f'P-sign: delta = P(gain<0 | G\'<0) - P(gain<0 | G\'>0) = {d0:+.3f}, 95 % lower {lo:+.3f} -> '
                 f'{"SUPPORTED" if out["P_sign"]["supported"] else "NOT SUPPORTED"}; cells with G\'<0 per K {out["P_sign"]["neg_per_K"]}')
    out['stale_harm_index'] = {s: Pd[s]['Qe'][0] - Pd[s]['Qc'][0] for s in SEEDS}
    L.append('stale-harm index Q_empty(0) - Q_cache(0) per seed: ' + ' '.join(f's{s}:{v:+.3f}' for s, v in out['stale_harm_index'].items()))
    text = '\n'.join(L); print(text)
    (M / 'e3_exact_demand_report_20261001.json').write_text(json.dumps(out, indent=1, default=float))
    (M / 'e3_exact_demand_report_20261001.txt').write_text(text + '\n')


if __name__ == '__main__':
    main()
