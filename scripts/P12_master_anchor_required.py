#!/usr/bin/env python3
"""MASTER: "at price 1/10 the anchor is MANDATORY", by two SEPARATED certificates.

WHY THIS FILE REPLACES P8's THRESHOLD CLAIM.  `P8_master_active_set.py` located a
threshold by bisecting `V(c0) > V0 + tol`.  That is not a proof of a threshold, and
its dual extraction was wrong: it kept only the cuts whose shift equalled the
alternative's own profiling shift, which threw away most of the LP's multipliers and
produced an "upper bound" of 0.0286687 against a primal of 0.0137731 -- a factor of
two, not a certificate.  Nothing downstream of that number was certified.

WHAT IS CERTIFIED HERE INSTEAD, and it is enough.  With
    E_u(x, x0; t) = (1/2) sum_e (x_e/v_e)(d_{u,e} - t)^2 + x0 t^2/(2 v0),
    I_u = inf_t E_u = D_u - M_u^2/(2K),   J = min_u I_u,
    budget: sum_e kappa_e x_e + c0 x0 = 1,
the two certificates are
    (UPPER)  any lambda >= 0 on PAIRS (u_j, t_j) with sum lambda = 1 gives, for every
             anchor-free allocation,
                 J(x, 0) <= sum_j lam_j E_{u_j}(x, 0; t_j) = sum_e x_e H_e
                         <= U0 * sum_e kappa_e x_e = U0,
             H_e = sum_j lam_j (d_{u_j,e} - t_j)^2/(2 v_e),  U0 = max_e H_e/kappa_e.
             No claim that any cut is active, no complementary slackness, no
             optimality of lambda.  The bound holds whatever produced lambda.
    (LOWER)  one explicit rational allocation with x0 > 0 attains L1 = min_u I_u.
If L1 > U0 then no anchor-free design can reach L1, so EVERY design attaining at
least L1 -- in particular every optimizer -- has x0 > 0.

Everything below runs in exact `Fraction` arithmetic.  The LP is used only to
PROPOSE lambda and the allocation; both are then rationalised, renormalised against
the exact budget, and re-verified.  No float enters a certificate.

WHAT THIS DOES NOT ESTABLISH
  * Not a threshold.  It shows the anchor is mandatory at c0 = 1/10 on this instance;
    the exact critical price is a different question and is not answered.
  * The alternative set is the finite one P8 uses (each rival tying the leader).  It
    is not the full alternative set of an unconstrained argmax problem.
  * U0 is whatever the proposed lambda gives; a better lambda would give a smaller
    U0.  The certificate does not depend on lambda being optimal, only on L1 > U0.

    .venv/bin/python scripts/P12_master_anchor_required.py
"""
from __future__ import annotations

from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

REPO = Path(__file__).resolve().parents[1]


class Game:
    def __init__(self, theta, alts, v, kappa, v0, c0):
        self.theta = [F(t) for t in theta]
        self.d = [[F(a) for a in row] for row in alts]
        self.v = [F(t) for t in v]
        self.kappa = [F(t) for t in kappa]
        self.v0, self.c0 = F(v0), F(c0)
        self.n, self.nu = len(v), len(alts)

    def energy(self, x, x0, u, t):
        return (sum(x[e] * (self.d[u][e] - t) ** 2 / (2 * self.v[e])
                    for e in range(self.n)) + x0 * t * t / (2 * self.v0))

    def DMK(self, x, x0):
        K = sum(x[e] / self.v[e] for e in range(self.n)) + x0 / self.v0
        D = [sum(x[e] * self.d[u][e] ** 2 / (2 * self.v[e]) for e in range(self.n))
             for u in range(self.nu)]
        M = [sum(x[e] * self.d[u][e] / self.v[e] for e in range(self.n))
             for u in range(self.nu)]
        return D, M, K

    def info(self, x, x0):
        D, M, K = self.DMK(x, x0)
        return [D[u] - M[u] ** 2 / (2 * K) for u in range(self.nu)], [
            M[u] / K for u in range(self.nu)], K

    def budget(self, x, x0):
        return sum(self.kappa[e] * x[e] for e in range(self.n)) + self.c0 * x0


def solve_lp(g: Game, allow_anchor: bool, rounds=80):
    """cutting planes; returns (x, x0, cuts, multipliers) -- a PROPOSAL only."""
    n, nu = g.n, g.nu
    cuts = [(u, F(0)) for u in range(nu)]
    x = [F(1, n)] * n
    x0 = F(0)
    lastres = None
    for _ in range(rounds):
        rows = []
        for (u, t) in cuts:
            row = [-float((g.d[u][e] - t) ** 2 / (2 * g.v[e])) for e in range(n)]
            row.append(-float(t * t / (2 * g.v0)) if allow_anchor else 0.0)
            row.append(1.0)
            rows.append(row)
        ce = [float(v) for v in g.kappa] + [float(g.c0)]
        bnds = [(0, None)] * n + ([(0, None)] if allow_anchor else [(0, 0)])
        res = linprog(np.r_[np.zeros(n + 1), -1.0], A_ub=np.array(rows),
                      b_ub=np.zeros(len(cuts)),
                      A_eq=np.array([np.r_[ce, 0.0]]), b_eq=[1.0],
                      bounds=bnds + [(None, None)], method="highs")
        if not res.success:
            return None
        lastres = res
        x = [F(float(v)).limit_denominator(10 ** 9) for v in res.x[:n]]
        x0 = F(float(res.x[n])).limit_denominator(10 ** 9)
        b = g.budget(x, x0)
        if b == 0:
            return None
        x = [v / b for v in x]; x0 = x0 / b
        I, ts, K = g.info(x, x0)
        new = False
        for u in range(nu):
            if (u, ts[u]) not in cuts:
                cuts.append((u, ts[u])); new = True
        if not new:
            break
    return x, x0, cuts, lastres


def upper_certificate(g: Game, lam, cuts):
    """U0 = max_e H_e/kappa_e, exact.  Valid for EVERY anchor-free allocation."""
    He = [sum(lam[j] * (g.d[cuts[j][0]][e] - cuts[j][1]) ** 2 / (2 * g.v[e])
              for j in range(len(cuts))) for e in range(g.n)]
    return max(He[e] / g.kappa[e] for e in range(g.n)), He


def main():
    print("MASTER: the anchor is MANDATORY at c0 = 1/10, by two separated "
          "certificates\n")
    theta = [F(1), F(3, 5), F(11, 20), F(1, 2)]
    alts, labels = [], []
    for j in range(1, 4):
        dj = [F(0)] * 4
        gap = theta[0] - theta[j]
        dj[0] = gap / 2
        dj[j] = -gap / 2
        alts.append(dj)
        labels.append(f"leader ties rival {j+1} (gap {gap})")
    c0 = F(1, 10)
    g = Game(theta, alts, [F(1)] * 4, [F(1)] * 4, F(1), c0)
    res = {"theta": [str(t) for t in theta], "c0": str(c0),
           "alternatives": [[str(a) for a in r] for r in alts], "labels": labels}

    print("PART 1 -- the UPPER certificate for every anchor-free design")
    out = solve_lp(g, allow_anchor=False)
    x_free, _x0, cuts, lp = out
    mult = np.abs(np.array(lp.ineqlin.marginals, dtype=float))
    tot = mult.sum()
    if tot <= 0:
        raise AssertionError("the LP returned no usable multipliers")
    # KEEP EVERY CUT THE LP USED, each with its OWN shift.  Dropping the cuts whose
    # shift is not the alternative's profiling shift is exactly the bug in P8.
    lam = [F(float(v / tot)).limit_denominator(10 ** 9) for v in mult]
    sl = sum(lam)
    lam = [v / sl for v in lam]
    U0, He = upper_certificate(g, lam, cuts)
    Ifree, _t, _K = g.info(x_free, F(0))
    Vfree = min(Ifree)
    nnz = sum(1 for v in lam if v > 0)
    print(f"   lambda on {nnz} of {len(cuts)} cut pairs (u, t), sum = {sum(lam)}")
    print(f"   H_e/kappa_e = " + ", ".join(f"{float(He[e]/g.kappa[e]):.9f}"
                                           for e in range(g.n)))
    print(f"   U0 = {float(U0):.12f}   (an anchor-free PRIMAL reaches "
          f"{float(Vfree):.12f}, so U0 is tight to "
          f"{float((U0-Vfree)/Vfree):.2e})")
    # soundness spot-check: the bound must hold for allocations OTHER than the LP's
    ctrl = 0
    for cand in ([F(1, 4)] * 4, [F(1, 2), F(1, 6), F(1, 6), F(1, 6)],
                 [F(7, 10), F(1, 10), F(1, 10), F(1, 10)],
                 [F(1, 10), F(3, 10), F(3, 10), F(3, 10)]):
        b = g.budget(cand, F(0))
        cand = [v / b for v in cand]
        Ic, _tc, _Kc = g.info(cand, F(0))
        if min(Ic) > U0:
            raise AssertionError(f"UPPER certificate violated at {cand}")
        ctrl += 1
    print(f"   checked against {ctrl} other anchor-free allocations (including the "
          f"uniform 1/4 one): none exceeds U0")
    res["upper"] = {"U0": str(U0), "H_over_kappa": [str(He[e] / g.kappa[e])
                                                    for e in range(g.n)],
                    "lambda": [str(v) for v in lam],
                    "cuts": [[c[0], str(c[1])] for c in cuts],
                    "anchor_free_primal": str(Vfree),
                    "controls_checked": ctrl}

    print("\nPART 2 -- the LOWER certificate: ONE explicit design that buys the anchor")
    out2 = solve_lp(g, allow_anchor=True)
    x1, x01, _c2, _lp2 = out2
    # rationalise coarsely, then renormalise EXACTLY against the budget
    x1 = [F(v).limit_denominator(10 ** 4) for v in x1]
    x01 = F(x01).limit_denominator(10 ** 4)
    b = g.budget(x1, x01)
    x1 = [v / b for v in x1]; x01 = x01 / b
    if g.budget(x1, x01) != 1:
        raise AssertionError("the lower design is not budget-feasible")
    I1, t1, K1 = g.info(x1, x01)
    L1 = min(I1)
    print(f"   x = {[str(v) for v in x1]}")
    print(f"   x0 = {x01} = {float(x01):.9f} > 0,  budget = {g.budget(x1, x01)}")
    print(f"   I_u = " + ", ".join(f"{float(v):.12f}" for v in I1))
    print(f"   L1 = {float(L1):.12f}")
    res["lower"] = {"x": [str(v) for v in x1], "x0": str(x01),
                    "I": [str(v) for v in I1], "L1": str(L1),
                    "K": str(K1), "shifts": [str(v) for v in t1]}

    print("\nPART 3 -- the conclusion, in exact rationals")
    gap = L1 - U0
    print(f"   L1 - U0 = {gap} = {float(gap):.12e}")
    if gap <= 0:
        raise AssertionError("the two certificates do not separate")
    print("   L1 > U0, and U0 caps EVERY anchor-free design, so no design with")
    print("   x0 = 0 reaches L1.  Hence every design of value at least L1 -- in")
    print(f"   particular every optimizer at c0 = {c0} -- must have x0 > 0.")
    print("   THE ANCHOR IS MANDATORY AT THIS PRICE.  Nothing here is a threshold.")
    res["conclusion"] = {"L1_minus_U0": str(gap), "float": float(gap),
                         "anchor_mandatory": True,
                         "is_a_threshold": False}
    res["not_established"] = [
        "not a threshold: the exact critical price is not computed",
        "the alternative set is the finite one P8 uses, not the full alternative set "
        "of an unconstrained argmax problem",
        "U0 is whatever the proposed lambda gives; the certificate needs only "
        "L1 > U0, not optimality of lambda",
    ]
    outp = REPO / "research/worker_P12_master_20260915/P12_master_anchor_required.json"
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {outp}")


if __name__ == "__main__":
    main()
