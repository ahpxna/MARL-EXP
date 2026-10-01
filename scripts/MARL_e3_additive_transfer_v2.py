#!/usr/bin/env python3
"""Additive probe v2 (independent recheck 18:50; v1 and its JSON are kept): a context-free additive evaluator used as
a SELECTOR, tuned on SELECT only, reported on DEV with decision metrics.

Model: y(S) ~ sum_i,j a_ij [j added at i] + b_ij [j dropped at i] (ridge; MARL_e3_additive_transfer.design/fit).
(The coefficients are not identified individually: adding c to every add-coefficient of a receiver and subtracting
c from its drop-coefficients leaves every prediction unchanged, since each receiver adds and drops equally many
senders.  Only predictions are interpreted.)
Tuning on SELECT: lambda in the grid and the edit threshold tau in {-inf, 0, per-state score quantiles 0.9/0.99, +inf},
maximising the mean selected gain (the same rule as the selector trainers).  Two eligible masks, reported separately:
cap84 (+84 B, the no-bid budget) and cap74 (+84 B minus the 10 B bid, the bid arms' own budget).
DEV report, per mask: selected gain, oracle regret (best eligible gain - selected), edit rate, harmful-edit rate
P(gain < 0 | edit), tie-half pair accuracy and predicted-tie fraction; bootstrap over TRAFFIC SEEDS.
DEV -> DEV is an in-sample reference only, never an upper bound.
"""
from __future__ import annotations
import argparse, glob, json, sys
from collections import defaultdict
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load, choose
from scripts.MARL_e3_additive_transfer import design, fit
from scripts.MARL_e3_ranking_diag_v2 import pair_acc, selftest


def boot(vals, keys, B=5000, seed=0):
    by = defaultdict(list)
    for v, k in zip(vals, keys):
        if not np.isnan(v):
            by[k].append(v)
    K = sorted(by); rng = np.random.default_rng(seed)
    out = [np.mean(np.concatenate([by[K[i]] for i in rng.integers(0, len(K), len(K))])) for _ in range(B)]
    return [round(float(x), 3) for x in np.quantile(out, [0.025, 0.975])]


def prep(S, cap):
    out = []
    for st in S:
        X, y, nr, _ = design(st)
        feas = np.array([c['bytes'] <= st['b0'] + cap for c in st['cands']]); feas[0] = True
        out.append((X, y, feas, str(st['traffic_seed'])))
    return out


def evaluate(P, w, tau):
    g, reg, ed, harm, acc, ties = [], [], [], [], [], []
    for X, y, feas, _ in P:
        an = X @ w                      # prefix row is all-zero, so an[0] = 0: anchored by construction
        j = choose(an.copy(), feas, np.ones_like(feas), tau); g.append(y[j]); reg.append(y[feas].max() - y[j]); ed.append(j != 0)
        if j != 0:
            harm.append(y[j] < 0)
        a_, t, n = pair_acc(an[feas], y[feas])
        acc.append(a_); ties.append(t)
    return dict(g=g, reg=reg, ed=ed, harm=harm, acc=acc, ties=ties)


def main(a):
    selftest(); D = Path(a.actor_dir)
    tr = load([x for x in sorted(glob.glob(str(D / 'labels_train_*'))) if Path(x).is_dir()])[0]
    se = load([D / 'labels_select'])[0]; dv = load([D / 'labels_dev'])[0]
    res = dict(actor_dir=str(D), n_train=len(tr), n_select=len(se), n_dev=len(dv), masks={})
    W = {lam: fit(tr, lam) for lam in a.lams}
    for mask, cap in (('cap84', 84), ('cap74', 74)):
        Pse, Pdv = prep(se, cap), prep(dv, cap); best = None
        for lam, w in W.items():
            sc = [X @ w for X, _, _, _ in Pse]
            grid = [-np.inf, 0.0] + sorted({float(x) for s in sc for x in np.quantile(s[1:], [0.9, 0.99])}) + [np.inf]
            for tau in grid:
                m = float(np.mean(evaluate(Pse, w, tau)['g']))
                if best is None or m > best[0] + 1e-12:
                    best = (m, lam, tau)
        sel_gain, lam, tau = best; E = evaluate(Pdv, W[lam], tau); seeds = [p[3] for p in Pdv]
        r = dict(lambda_selected=lam, tau_selected=('+inf' if tau > 0 else '-inf') if np.isinf(tau) else round(float(tau), 4), select_gain=round(sel_gain, 3),
                 dev_selected_gain=dict(mean=round(float(np.mean(E['g'])), 3), ci_traffic_seed=boot(E['g'], seeds)),
                 dev_oracle_regret=dict(mean=round(float(np.mean(E['reg'])), 3), ci_traffic_seed=boot(E['reg'], seeds)),
                 dev_oracle_best=round(float(np.mean([y[f].max() for _, y, f, _ in Pdv])), 3),
                 dev_edit_rate=round(float(np.mean(E['ed'])), 3), dev_harmful_edit_rate=round(float(np.mean(E['harm'])), 3) if E['harm'] else None,
                 dev_pair_acc=dict(mean=round(float(np.nanmean(E['acc'])), 4), ci_traffic_seed=boot(E['acc'], seeds)), dev_tie_fraction=round(float(np.nanmean(E['ties'])), 4))
        res['masks'][mask] = r
        print(f"{mask}: lambda {lam} tau {r['tau_selected']} (select gain {sel_gain:+.3f}) | DEV selected gain {r['dev_selected_gain']['mean']:+.3f} {r['dev_selected_gain']['ci_traffic_seed']} "
              f"regret {r['dev_oracle_regret']['mean']:.2f} (oracle {r['dev_oracle_best']:.2f}) edit {r['dev_edit_rate']:.2f} harm|edit {r['dev_harmful_edit_rate']} | "
              f"pair acc {r['dev_pair_acc']['mean']:.4f} {r['dev_pair_acc']['ci_traffic_seed']} ties {r['dev_tie_fraction']:.3f}", flush=True)
    Path(a.out).write_text(json.dumps(res, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--lams', type=float, nargs='+', default=[1.0, 10.0, 100.0, 1000.0])
    p.add_argument('--out', required=True)
    main(p.parse_args())
