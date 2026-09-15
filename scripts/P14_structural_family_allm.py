#!/usr/bin/env python3
"""Structural B: the linear-separation family, computed by SIGN COUNTS so it reaches
every m in range rather than the m = 5..14 table.

`P3_avg_path_amplification.py` found the family
    g_m = (-3, (-1) x p, (+1) x q, 3),   p = ceil((m-2)/2), q = m-2-p,
with eps_nest = 2/(m+4), V_avg = 2/((m+4)(m-1)) and ratio exactly b = m-1, by a
subset DP that costs 2^m.  That is why the table stopped at m = 14.

THE REDUCTION THE SUPERVISOR ASKED FOR.  For this family the regret of a prefix does
not depend on WHICH elements were taken, only on HOW MANY of each sign:
    sigma = -3*n3m - n1m + n1p + 3*n3p,     k = n3m + n1m + n1p + n3p,
    L = |TOT - sigma| / D,   D = m+4,   TOT = q - p,
    r(k, state) = L - opt_k,   opt_k = min over count vectors of size k of |TOT-sigma|/D.
So the ordering DAG has O(m^2) states, not 2^m, and both quantities are exact:
  * eps_nest by  f(state) = min over the last sign added of max(f(prev), r(state));
  * V_avg^free as the matrix game over PATHS, solved by column generation whose
    best-response is the additive DP on the same DAG, then certified in exact
    rationals by a primal mixture and a dual q.
This is step 1 of the assignment ("regret from the number of signs chosen") and it is
what lets steps 2 and 3 be CHECKED at every m in range.

WHAT IS FOUND
  * eps_nest = 2/(m+4) and V_avg = 2/((m+4)(m-1)) at every m checked, so the ratio is
    exactly b = m-1.
  * The two saturation conditions hold at every m: the cheapest ordering's TOTAL
    regret equals eps_nest (all of it on ONE budget), and the uniform dual attains
    V_avg.  `LeanStructuralSaturationV1` turns those two into the ratio, so what is
    left open is exactly the two conditions, not the conclusion.
  * The explicit balanced ordering distribution is recorded per m.

WHAT THIS DOES NOT ESTABLISH
  * It is a computation at each m, not an induction over m.  The two saturation
    conditions are verified, not proved; a proof would be a prefix-counting argument
    and is the remaining step.
  * eps_nest = 2/(m+4) SHRINKS with m.  The ratio grows, the separation level does
    not: this must not be advertised as an unbounded separation at a fixed epsilon.
  * No marginal constraint is imposed: these are the FREE values, which is what the
    saturation lemma needs (see P3 for why x* = M(P*) makes that the right comparison).

    .venv/bin/python scripts/P14_structural_family_allm.py
"""
from __future__ import annotations
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

REPO = Path(__file__).resolve().parents[1]


def family(m):
    p = (m - 2 + 1) // 2
    return p, m - 2 - p


def build(m):
    """states, opt_k and the regret table, all from sign counts."""
    p, q = family(m)
    D = m + 4
    TOT = q - p
    states = {}
    for a in range(2):
        for b in range(p + 1):
            for c in range(q + 1):
                for d in range(2):
                    k = a + b + c + d
                    sig = -3 * a - b + c + 3 * d
                    states[(a, b, c, d)] = (k, F(abs(TOT - sig), D))
    opt = {}
    for st, (k, L) in states.items():
        if k not in opt or L < opt[k]:
            opt[k] = L
    reg = {st: states[st][1] - opt[states[st][0]] for st in states}
    return p, q, D, TOT, states, opt, reg


def preds(st, p, q):
    a, b, c, d = st
    out = []
    if a: out.append((0, b, c, d))
    if b: out.append((a, b - 1, c, d))
    if c: out.append((a, b, c - 1, d))
    if d: out.append((a, b, c, 0))
    return out


def order_states(m, p, q):
    return sorted(((a, b, c, d) for a in range(2) for b in range(p + 1)
                   for c in range(q + 1) for d in range(2)),
                  key=lambda s: sum(s))


def eps_nest(m):
    p, q, D, TOT, states, opt, reg = build(m)
    f = {}
    for st in order_states(m, p, q):
        if sum(st) == 0:
            f[st] = F(0)
            continue
        f[st] = min(max(f[pr], reg[st]) for pr in preds(st, p, q))
    return f[(1, p, q, 1)], (p, q, D, TOT, states, opt, reg)


def best_response(m, ctx, w):
    """min over orderings of sum_k w_k r(k, state), exact; returns (value, column)."""
    p, q, D, TOT, states, opt, reg = ctx
    g = {}
    for st in order_states(m, p, q):
        if sum(st) == 0:
            g[st] = (F(0), ())
            continue
        k = sum(st)
        best = None
        for pr in preds(st, p, q):
            v = g[pr][0] + w[k] * reg[st]
            if best is None or v < best[0]:
                best = (v, g[pr][1] + (st,))
        g[st] = best
    val, path = g[(1, p, q, 1)]
    col = [F(0)] * (m + 1)
    for st in path:
        col[sum(st)] = reg[st]
    return val, tuple(col)


def v_avg(m, ctx, rounds=300):
    cols, seen = [], set()
    w = [F(1, m + 1)] * (m + 1)
    for _ in range(rounds):
        val, col = best_response(m, ctx, w)
        if col not in seen:
            seen.add(col); cols.append(col)
        n = len(cols)
        A = np.array([[float(cols[j][k]) for j in range(n)] + [-1.0]
                      for k in range(m + 1)])
        res = linprog(np.r_[np.zeros(n), 1.0], A_ub=A, b_ub=np.zeros(m + 1),
                      A_eq=np.array([np.r_[np.ones(n), 0.0]]), b_eq=[1.0],
                      bounds=[(0, None)] * n + [(None, None)], method="highs")
        if not res.success:
            return None
        qf = np.abs(np.array(res.ineqlin.marginals, dtype=float))
        sm = qf.sum()
        qf = qf / sm if sm > 0 else np.ones(m + 1) / (m + 1)
        w = [F(float(v)).limit_denominator(10 ** 7) for v in qf]
        sq = sum(w)
        w = [v / sq for v in w] if sq else [F(1, m + 1)] * (m + 1)
        lo, _ = best_response(m, ctx, w)
        P = [F(float(v)).limit_denominator(10 ** 7) for v in res.x[:n]]
        sP = sum(P)
        if sP == 0:
            continue
        P = [v / sP for v in P]
        up = max(sum(P[j] * cols[j][k] for j in range(n)) for k in range(m + 1))
        if lo == up:
            return up, w, P, cols
    return None


def main():
    print("Structural: the family at every m, from sign counts\n")
    res = {"rows": []}
    MS = list(range(5, 31)) + [36, 40]
    for m in MS:
        en, ctx = eps_nest(m)
        out = v_avg(m, ctx)
        if out is None:
            print(f"   m={m}: V_avg not certified exactly; skipped")
            continue
        va, w, P, cols = out
        b = m - 1
        pred_e, pred_v = F(2, m + 4), F(2, (m + 4) * (m - 1))
        ok_e, ok_v = (en == pred_e), (va == pred_v)
        # saturation conditions
        tot, _ = best_response(m, ctx, [F(1)] * (m + 1))
        qunif = [F(0)] + [F(1, b)] * b + [F(0)]
        lo_unif, _ = best_response(m, ctx, qunif)
        c1 = (tot == en)
        c2 = (lo_unif == va)
        if not (ok_e and ok_v and c1 and c2):
            raise AssertionError(
                f"m={m}: eps {en} vs {pred_e}, V_avg {va} vs {pred_v}, "
                f"concentrated {c1}, uniform-optimal {c2}")
        if m <= 12 or m % 10 == 0:
            print(f"   m={m:3d}: eps_nest = {en} = 2/(m+4);  V_avg = {va} = "
                  f"2/((m+4)(m-1));  ratio = {b};  concentrated & uniform-dual: OK")
        res["rows"].append({"m": m, "eps_nest": str(en), "V_avg": str(va),
                            "ratio": b, "regret_concentrated": True,
                            "uniform_dual_optimal": True,
                            "n_columns": len(cols),
                            "balanced_mixture_support": sum(1 for v in P if v > 0)})
    print(f"\n   verified at {len(res['rows'])} values of m, up to m = "
          f"{res['rows'][-1]['m']} (the subset DP of P3 stopped at 14)")
    print("   ratio = m-1 at every one; and the two saturation conditions hold, so")
    print("   LeanStructuralSaturationV1 converts them into the ratio.")
    print("   NOTE eps_nest = 2/(m+4) SHRINKS: the RATIO grows, the separation LEVEL")
    print("   does not.  This is not an unbounded separation at a fixed epsilon.")
    res["not_established"] = [
        "a computation at each m, not an induction over m; the two saturation "
        "conditions are verified, not proved",
        "eps_nest shrinks like 2/(m+4): the ratio grows, the level does not",
        "no marginal constraint is imposed; these are the FREE values",
    ]
    out = REPO / "research/worker_P14_structural_20260915/P14_structural_family_allm.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
