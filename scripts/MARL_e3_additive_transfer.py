#!/usr/bin/env python3
"""Is the critic's sub-chance held-out ordering a property of the DATA? (read-only; labels only, no network.)

A context-free ADDITIVE model of the continuation gain,
    y(S) ~ sum over receivers i and senders j of  a_ij * [j added at i] + b_ij * [j dropped at i],
is fitted by ridge least squares on one set of states and scored on another by within-state pair order
accuracy (pairs of feasible candidates whose true gains differ), overall and for pairs of EQUAL edit size.
Transfers:
  train -> dev, train -> select      (the critic's own split);
  train half A -> train half B       (split by traffic seed; the same distribution, other episodes);
  dev -> dev (in-sample reference)   (an upper reference, not a result).
If the additive model is ALSO below 0.5 across episodes, per-sender effects reverse between episodes (a data
property the critic cannot beat by fitting); if it is above 0.5, the critic's inversion is a learning failure.
Also: the across-episode correlation of the fitted coefficients (half A vs half B).
"""
from __future__ import annotations
import argparse, glob, json, sys
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scripts.MARL_e3_selector_train import load


def design(st):
    m = st['m']; P = st['cands'][0]['sets']; X = np.zeros((len(st['cands']), 2 * m * m)); nr = np.zeros(len(st['cands']))
    for c, cand in enumerate(st['cands']):
        for i in range(m):
            add = set(cand['sets'][i]) - set(P[i]); drop = set(P[i]) - set(cand['sets'][i]); nr[c] += len(add)
            for j in add:
                X[c, i * m + j] = 1
            for j in drop:
                X[c, m * m + i * m + j] = 1
    y = np.array([c['cont'] for c in st['cands']]) - st['cands'][0]['cont']
    feas = np.array([c['bytes'] <= st['b0'] + 84 for c in st['cands']]); feas[0] = True
    return X, y, nr, feas


def fit(S, lam):
    X = np.concatenate([design(st)[0] for st in S]); y = np.concatenate([design(st)[1] for st in S])
    return np.linalg.solve(X.T @ X + lam * np.eye(X.shape[1]), X.T @ y)


def score(S, w):
    acc, acc_eq = [], []
    for st in S:
        X, y, nr, feas = design(st); p = X @ w; p, y, nr = p[feas], y[feas], nr[feas]
        dy = y[:, None] - y[None, :]; dp = p[:, None] - p[None, :]; dn = nr[:, None] - nr[None, :]; m = dy > 0
        if m.any():
            acc.append((dp[m] > 0).mean() + 0.5 * (dp[m] == 0).mean())
        me = m & (dn == 0)
        if me.any():
            acc_eq.append((dp[me] > 0).mean() + 0.5 * (dp[me] == 0).mean())
    return round(float(np.mean(acc)), 3), round(float(np.mean(acc_eq)), 3)


def main(a):
    D = Path(a.actor_dir)
    tr = load([x for x in sorted(glob.glob(str(D / 'labels_train_*'))) if Path(x).is_dir()])[0]
    se = load([D / 'labels_select'])[0]; dv = load([D / 'labels_dev'])[0]
    seeds = sorted({st['traffic_seed'] for st in tr}); half = set(seeds[: len(seeds) // 2])
    A = [st for st in tr if st['traffic_seed'] in half]; B = [st for st in tr if st['traffic_seed'] not in half]
    out = {}
    for lam in a.lams:
        w_tr, w_A, w_B, w_dv = fit(tr, lam), fit(A, lam), fit(B, lam), fit(dv, lam)
        r = {'train->dev': score(dv, w_tr), 'train->select': score(se, w_tr), 'trainA->trainB': score(B, w_A), 'trainB->trainA': score(A, w_B),
             'train->train (in-sample)': score(tr, w_tr), 'dev->dev (in-sample)': score(dv, w_dv),
             'coef corr halfA vs halfB': round(float(np.corrcoef(w_A, w_B)[0, 1]), 3), 'coef corr train vs dev': round(float(np.corrcoef(w_tr, w_dv)[0, 1]), 3)}
        out[f'lambda={lam}'] = r
        print(f'lambda {lam}: ' + ' | '.join(f'{k} {v}' for k, v in r.items()), flush=True)
    Path(a.out).write_text(json.dumps(dict(actor_dir=str(D), n_train=len(tr), n_A=len(A), n_B=len(B), results=out, note='(overall pair acc, equal-edit-size pair acc)'), indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--actor-dir', required=True); p.add_argument('--lams', type=float, nargs='+', default=[1.0, 10.0, 100.0]); p.add_argument('--out', required=True)
    main(p.parse_args())
