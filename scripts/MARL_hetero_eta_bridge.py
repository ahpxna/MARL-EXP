#!/usr/bin/env python3
"""Theory-traffic bridge: the edge-local constant eta of the TRUE traffic value (read-only on labels).

For a receiver i at one snapshot, every single-receiver one-swap S = P - (i,d) + (i,b) in the
stored candidate family has an oracle value difference D_db = f(S) - f(P).  ScoreLocal(f, w, eta)
(LeanMarlEstimatedRevisionV1 / LeanMarlBlockFrontierV1) implies |D_db - (w_b - w_d)| <= 2 eta for
some scores w.  The smallest such eta is half the Chebyshev (minimax) residual of the additive
model D_db ~ w_b - w_d, solved EXACTLY by a linear program per (snapshot, receiver).  It is a
LOWER bound on the eta of the whole value (only one-swaps from P are seen).
Also reported: whether the zero-price cut condition of T1 holds for that receiver (the best fitted
prefix score exceeds the best outsider score by >= 2 eta, i.e. keeping P_i is certified), and the
scale of eta against the value differences.  Evidence class: ORACLE-LABEL DIAGNOSTIC.
"""
from __future__ import annotations
import argparse, gzip, json, sys
from pathlib import Path
import numpy as np
from scipy.optimize import linprog

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from models.marl_hetero_selector import prefix_sets


def cheb(pairs, D, dn, bn):
    """min t s.t. |D_k - (w_b - w_d)| <= t; variables [w_d (dn), w_b (bn), t]; w_d[0] = 0 fixed."""
    n = dn + bn + 1; A, ub = [], []
    for (di, bi), dk in zip(pairs, D):
        row = np.zeros(n); row[dn + bi] = -1; row[di] = 1; row[-1] = -1; A.append(row); ub.append(-dk)
        row = np.zeros(n); row[dn + bi] = 1; row[di] = -1; row[-1] = -1; A.append(row); ub.append(dk)
    c = np.zeros(n); c[-1] = 1
    bounds = [(0, 0)] + [(None, None)] * (dn - 1) + [(None, None)] * bn + [(0, None)]
    r = linprog(c, A_ub=np.array(A), b_ub=np.array(ub), bounds=bounds, method='highs')
    if not r.success:
        raise RuntimeError(r.message)
    return r.x[-1], r.x[:dn], r.x[dn:dn + bn]


def main(a):
    out = []
    for lab in a.labels:
        for l in gzip.open(Path(lab) / 'labels.jsonl.gz', 'rt'):
            r = json.loads(l); m = r['m']
            for gi, g in enumerate(r['groups']):
                if a.live_only and gi > 0:
                    continue
                P = prefix_sets(r['order'], g['K']); Pm = [sum(1 << j for j in s) for s in P]
                ip = g['profiles'].index(Pm); vals = np.asarray(g['values'], float); D = vals - vals[ip]
                per = {}
                for c, prof in enumerate(g['profiles']):
                    ed = [i for i in range(m) if prof[i] != Pm[i]]
                    if len(ed) != 1:
                        continue
                    i = ed[0]; S = {j for j in range(16) if (prof[i] >> j) & 1}
                    add = S - P[i]; drop = P[i] - S
                    if len(add) != 1:
                        continue
                    per.setdefault(i, []).append((next(iter(drop)), next(iter(add)), D[c]))
                for i, L in per.items():
                    ds = sorted({x[0] for x in L}); bs = sorted({x[1] for x in L})
                    if len(L) < len(ds) + len(bs):             # not enough equations to test additivity
                        continue
                    pairs = [(ds.index(x[0]), bs.index(x[1])) for x in L]; Dv = [x[2] for x in L]
                    t, wd, wb = cheb(pairs, Dv, len(ds), len(bs))
                    eta = t / 2
                    margin = float(np.min(wd) - np.max(wb))    # best outsider vs weakest kept, fitted
                    out.append(dict(split=r['split'], t=r['t'], gi=gi, i=i, n=len(L), eta=eta,
                                    maxabsD=float(np.max(np.abs(Dv))), spread=float(np.ptp(Dv)),
                                    zero_price=bool(margin >= 2 * eta), best_swap=float(np.max(Dv))))
    eta = np.array([o['eta'] for o in out]); mx = np.array([o['maxabsD'] for o in out]); zp = np.array([o['zero_price'] for o in out])
    bs = np.array([o['best_swap'] for o in out])
    rep = dict(receivers=len(out), eta_quantiles=np.quantile(eta, [0, .25, .5, .75, .9, 1]).tolist(),
               frac_eta_zero=float((eta < 1e-9).mean()), eta_over_maxabsD_median=float(np.median(eta / np.maximum(mx, 1e-9))),
               frac_zero_price_certified=float(zp.mean()),
               frac_best_swap_positive=float((bs > 1e-9).mean()),
               frac_best_swap_positive_given_zero_price=float((bs[zp] > 1e-9).mean()) if zp.any() else None)
    Path(a.out).write_text(json.dumps(dict(report=rep, rows=out)))
    print(json.dumps(rep, indent=1))


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--labels', nargs='+', required=True); p.add_argument('--out', required=True)
    p.add_argument('--live-only', action='store_true')
    main(p.parse_args())
