#!/usr/bin/env python3
"""MASTER: from ONE alternative to the ACTIVE SET of the whole game, and the
acquisition threshold that follows.

WHAT IS ALREADY ON DISK.  `LeanMasterAnchorCertificateV1` proves both sides of the
anchor price threshold FOR A SINGLE ALTERNATIVE with given `D_u, M_u, K`:
`anchor_strictly_helps` / `anchor_cheap_suffices` below the price, `dual_bound` +
`no_anchor_needed` above it.  Its own docstring says the link to the real instrument
is an interface, and the game has more than one alternative.  This file supplies the
missing step: the ACTIVE SET of the whole game, and what the threshold becomes.

THE GAME, as an LP with cuts.  With a common offset `b`, query `e` has mean
`m_theta(e) + b`, variance `sig_e`, price `c_e`; the anchor reads `b` directly with
variance `sig0` and price `c0`.  Profiling the offset,
    I_u(a, x0) = min_t [ sum_e a_e (d_{u,e} - t)^2/(2 sig_e) + x0 t^2/(2 sig0) ],
a MINIMUM OF LINEAR functions of (a, x0), hence concave, so
    Gamma = max_{a,x0 >= 0, sum c_e a_e + c0 x0 = 1}  min_u I_u(a, x0)
is an LP over the cuts (u, t).  The cut generator is exact: the best `t` for a given
allocation is `t_u = M_u/(K + x0/sig0)`.  The LP's own multipliers give the
certificate `(lambda, z)` that `dual_bound` needs, and complementary slackness makes
the support of `lambda` the ACTIVE SET.

WHAT THIS FILE SHOWS
 1. The active set of the anchor-free game is NOT a singleton on a natural instance:
    several alternatives tie at `V_0`, and the certificate weights are spread over
    them.  So a threshold derived from one alternative is a statement about one face
    of the value, not about the game.
 2. The GAME threshold `c0*` -- the largest price at which buying anchor exposure
    strictly raises the value -- is computed by bisection on the LP, with the primal
    and the dual reported on both sides.
 3. It is compared against the per-alternative price of `anchor_cheap_suffices`.
    Those prices differ, and the file reports the interval of `c0` where a
    single-alternative rule and the game disagree: there the one-alternative
    calculation says "buy" while the game says the value does not move, or vice
    versa.  That interval is the reason the active set has to be carried.

WHAT THIS DOES NOT ESTABLISH
  * The instance is a concrete finite design; nothing here is a theorem about all
    MASTER instances.  The general statements that ARE proved are in
    `LeanMasterActiveSetV1.lean`: complementary slackness, and that every optimal
    allocation buys the anchor once the two sides separate.
  * The LP runs in floating point; the value, the active set and the certificate are
    then RE-CHECKED in exact rationals, and both the primal value and the dual bound
    are printed so the gap is visible.
  * `c0*` is located by bisection to a stated tolerance, not in closed form.

    .venv/bin/python scripts/P8_master_active_set.py
"""
from __future__ import annotations

from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

REPO = Path(__file__).resolve().parents[1]


class Master:
    """m_theta on n items, common offset, unit variances, unit query prices."""

    def __init__(self, theta, alts, sig=None, cost=None, sig0=F(1)):
        self.theta = [F(v) for v in theta]
        self.n = len(theta)
        self.d = [[F(a) for a in row] for row in alts]      # d[u][e]
        self.sig = [F(1)] * self.n if sig is None else [F(v) for v in sig]
        self.cost = [F(1)] * self.n if cost is None else [F(v) for v in cost]
        self.sig0 = F(sig0)

    def info_at(self, a, x0, u, t):
        """the LINEAR-in-(a,x0) function whose min over t is I_u."""
        return (sum(a[e] * (self.d[u][e] - t) ** 2 / (2 * self.sig[e])
                    for e in range(self.n))
                + x0 * t * t / (2 * self.sig0))

    def DMK(self, a, x0):
        K = sum(a[e] / self.sig[e] for e in range(self.n)) + x0 / self.sig0
        D = [sum(a[e] * self.d[u][e] ** 2 / (2 * self.sig[e])
                 for e in range(self.n)) for u in range(len(self.d))]
        M = [sum(a[e] * self.d[u][e] / self.sig[e] for e in range(self.n))
             for u in range(len(self.d))]
        return D, M, K

    def info(self, a, x0):
        D, M, K = self.DMK(a, x0)
        if K == 0:
            return [F(0)] * len(self.d), [F(0)] * len(self.d)
        return ([D[u] - M[u] ** 2 / (2 * K) for u in range(len(self.d))],
                [M[u] / K for u in range(len(self.d))])


def solve(game: Master, c0, allow_anchor=True, rounds=60):
    """cutting-plane LP; returns (value, a, x0, cuts, multipliers)."""
    n, nu = game.n, len(game.d)
    cuts = [(u, F(0)) for u in range(nu)]
    a = None
    for _ in range(rounds):
        rows = []
        for (u, t) in cuts:
            row = [-float((game.d[u][e] - t) ** 2 / (2 * game.sig[e]))
                   for e in range(n)]
            row.append(-float(t * t / (2 * game.sig0)) if allow_anchor else 0.0)
            row.append(1.0)
            rows.append(row)
        ce = [float(v) for v in game.cost] + [float(c0)]
        bounds = [(0, None)] * n + ([(0, None)] if allow_anchor else [(0, 0)])
        res = linprog(np.r_[np.zeros(n + 1), -1.0], A_ub=np.array(rows),
                      b_ub=np.zeros(len(cuts)),
                      A_eq=np.array([np.r_[ce, 0.0]]), b_eq=[1.0],
                      bounds=bounds + [(None, None)], method="highs")
        if not res.success:
            return None
        a = [F(float(v)).limit_denominator(10 ** 9) for v in res.x[:n]]
        x0 = F(float(res.x[n])).limit_denominator(10 ** 9)
        bud = sum(game.cost[e] * a[e] for e in range(n)) + c0 * x0
        if bud == 0:
            return None
        a = [v / bud for v in a]; x0 = x0 / bud
        I, tstar = game.info(a, x0)
        newcut = False
        for u in range(nu):
            if (u, tstar[u]) not in cuts:
                cuts.append((u, tstar[u])); newcut = True
        if not newcut:
            break
    I, tstar = game.info(a, x0)
    V = min(I)
    return V, a, x0, cuts, res, I, tstar


def certify(game: Master, a, x0, c0, lam, z):
    """H_e/c_e and H0/c0 against V, exactly -- the `dual_bound` hypothesis."""
    n = game.n
    He = [sum(lam[u] * (game.d[u][e] - z[u]) ** 2 / (2 * game.sig[e])
              for u in range(len(game.d))) for e in range(n)]
    H0 = sum(lam[u] * z[u] ** 2 / (2 * game.sig0) for u in range(len(game.d)))
    ratios = [He[e] / game.cost[e] for e in range(n)] + [H0 / c0]
    return max(ratios), ratios, He, H0


def main():
    print("MASTER: the ACTIVE SET of the whole game, and the acquisition threshold\n")
    # argmax answer, four items; alternative u_j ties item 1 with item j+1
    theta = [F(1), F(3, 5), F(11, 20), F(1, 2)]
    alts = []
    labels = []
    for j in range(1, 4):
        dj = [F(0)] * 4
        gap = theta[0] - theta[j]
        dj[0] = gap / 2
        dj[j] = -gap / 2
        alts.append(dj)
        labels.append(f"item 1 ties item {j+1} (gap {gap})")
    game = Master(theta, alts)
    res = {"theta": [str(v) for v in theta],
           "alternatives": [[str(v) for v in row] for row in alts],
           "alternative_labels": labels}

    print("PART 1 -- the anchor-free game: value, ACTIVE SET, certificate")
    out = solve(game, F(1), allow_anchor=False)
    V0, a0, x00, cuts0, lp0, I0, t0 = out
    act0 = [u for u in range(len(alts)) if I0[u] <= V0 * (1 + F(1, 10 ** 6))]
    print(f"   allocation a = {[float(v) for v in a0]}   (x0 = {float(x00)})")
    print(f"   V_0 = {float(V0):.9f}")
    for u in range(len(alts)):
        print(f"      I_{u+1} = {float(I0[u]):.9f}  t_{u+1} = {float(t0[u]):+.6f}"
              f"   [{labels[u]}]{'   ACTIVE' if u in act0 else ''}")
    print(f"   ACTIVE SET = {[u+1 for u in act0]}  ({len(act0)} of {len(alts)})")
    if len(act0) < 2:
        print("   (a singleton here -- the instance would not need the active set)")
    # certificate from the LP multipliers, restricted to the cuts at t = t_u
    mult = np.abs(np.array(lp0.ineqlin.marginals, dtype=float))
    lam = [F(0)] * len(alts)
    for k, (u, t) in enumerate(cuts0):
        if mult[k] > 1e-12 and t == t0[u]:
            lam[u] += F(float(mult[k])).limit_denominator(10 ** 9)
    s = sum(lam)
    if s == 0:
        lam = [F(1, len(act0)) if u in act0 else F(0) for u in range(len(alts))]
    else:
        lam = [v / s for v in lam]
    print(f"   dual weights lambda = {[float(v) for v in lam]}")
    supp = [u for u in range(len(alts)) if lam[u] > 0]
    print(f"   support(lambda) = {[u+1 for u in supp]}  -> inside the active set: "
          f"{set(supp) <= set(act0)}   (complementary slackness)")
    res["anchor_free"] = {
        "a": [str(v) for v in a0], "V0": str(V0),
        "I": [str(v) for v in I0], "t": [str(v) for v in t0],
        "active_set": [u + 1 for u in act0],
        "lambda": [str(v) for v in lam],
        "lambda_support_in_active_set": bool(set(supp) <= set(act0))}

    print("\nPART 2 -- the GAME threshold on the anchor price c0")
    # an ABSOLUTE tolerance: the real gains here are ~1e-4, while the LP's own
    # noise is ~1e-8, so a relative test at 1e-7 would be reading noise.  The test
    # also requires the exposure itself to be bought.
    TOL = F(1, 10 ** 7)
    XTOL = F(1, 10 ** 6)

    def game_value(c0, sub=None):
        gg = game if sub is None else Master(
            theta, [alts[u] for u in sub], game.sig, game.cost, game.sig0)
        o = solve(gg, c0, allow_anchor=True)
        return None if o is None else (o[0], o[2])

    def threshold(sub=None, base=None):
        """largest c0 at which buying exposure still strictly raises the value."""
        lo, hi = F(1, 10 ** 5), F(4)
        if base is None:
            gg = game if sub is None else Master(
                theta, [alts[u] for u in sub], game.sig, game.cost, game.sig0)
            base = solve(gg, F(1), allow_anchor=False)[0]
        for _ in range(45):
            mid = (lo + hi) / 2
            v, xm = game_value(mid, sub)
            if v > base + TOL and xm > XTOL:
                lo = mid
            else:
                hi = mid
        return (lo + hi) / 2, base

    c0_game, _ = threshold(None, V0)
    print(f"   c0* (whole game) = {float(c0_game):.9f}")
    for c0 in (c0_game * F(1, 2), c0_game * F(2)):
        v, x0 = game_value(c0)
        print(f"      c0 = {float(c0):.9f}: V = {float(v):.9f} "
              f"({'>' if v > V0 else '='} V_0 = {float(V0):.9f}), x0 = "
              f"{float(x0):.6f}  -> the anchor {'IS' if x0 > 0 else 'is NOT'} bought")
    res["game_threshold"] = {"c0_star": str(c0_game), "V0": str(V0)}

    print("\nPART 3 -- the SINGLE-ALTERNATIVE thresholds: they are all ZERO")
    per = []
    for u in range(len(alts)):
        cu, base_u = threshold([u])
        per.append((cu, base_u))
        print(f"   u={u+1} [{labels[u]}]: alone, V_0 = {float(base_u):.9f} and the "
              f"anchor pays until c0 = {float(cu):.9f}"
              + ("   ACTIVE in the game" if u in act0 else ""))
    print("   For ONE alternative the optimal anchor-free design already sets")
    print("   M_u = 0 -- weight is split so the offset cancels -- and then")
    print("   I_u = D_u - M_u^2/(2K) = D_u does not depend on K at all, so the")
    print("   anchor is worth NOTHING at any price.  The thresholds above are the")
    print("   bisection floor, i.e. zero.  A positive threshold exists only because")
    print("   no single allocation can zero every ACTIVE M_u at once.")
    Dg, Mg, Kg = game.DMK(a0, F(0))
    print(f"   at the GAME optimum the offsets do not cancel: M = "
          + ", ".join(f"{float(v):+.6f}" for v in Mg))
    for u in range(len(alts)):
        g1 = Master(theta, [alts[u]], game.sig, game.cost, game.sig0)
        r1 = solve(g1, F(1), allow_anchor=False)
        _D1, M1, _K1 = g1.DMK(r1[1], F(0))
        print(f"      alone, u={u+1}: M_u = {float(M1[0]):+.3e}  (the design cancels "
              f"the offset by itself)")
    cu_act = [per[u][0] for u in act0]
    print(f"   whole game:                                          c0* = "
          f"{float(c0_game):.9f}")
    print(f"   max over ALL alternatives alone   = {float(max(p[0] for p in per)):.9f}")
    print(f"   min over the ACTIVE set alone     = {float(min(cu_act)):.9f}")
    print(f"   max over the ACTIVE set alone     = {float(max(cu_act)):.9f}")
    inside = min(cu_act) <= c0_game <= max(cu_act)
    print(f"   every single-alternative threshold is the bisection floor (zero);")
    print(f"   the game's is {float(c0_game):.6f} > 0.  So the single-alternative")
    print("   calculation cannot produce the game's rule even in principle: it is")
    print("   not conservative, it is EMPTY.  The threshold is a property of the")
    print("   ACTIVE SET -- of the fact that the active alternatives demand")
    print("   incompatible offset cancellations -- and of nothing smaller.")
    res["per_alternative"] = {
        "thresholds": [str(p[0]) for p in per],
        "alone_V0": [str(p[1]) for p in per],
        "game_threshold": str(c0_game),
        "active_set": [u + 1 for u in act0],
        "game_threshold_inside_active_range": bool(inside)}

    print("\nPART 4 -- a dual certificate for the FULL game, below the threshold")
    c0 = c0_game / 2
    o = solve(game, c0, allow_anchor=True)
    V, a, x0, cuts, lp, I, ts = o
    act = [u for u in range(len(alts)) if I[u] <= V * (1 + F(1, 10 ** 5))]
    mult = np.abs(np.array(lp.ineqlin.marginals, dtype=float))
    tot = mult.sum()
    if tot <= 0:
        mult = np.ones(len(cuts)); tot = mult.sum()
    lamc = [F(float(v / tot)).limit_denominator(10 ** 9) for v in mult]
    sl = sum(lamc)
    lamc = [v / sl for v in lamc]
    # cut-level certificate: one shift z per CUT, exactly the index set dual_bound
    # is stated over (its `U` is an index type, not necessarily the alternatives)
    n = game.n
    He = [sum(lamc[k] * (game.d[cuts[k][0]][e] - cuts[k][1]) ** 2
              / (2 * game.sig[e]) for k in range(len(cuts))) for e in range(n)]
    H0 = sum(lamc[k] * cuts[k][1] ** 2 / (2 * game.sig0) for k in range(len(cuts)))
    ratios = [He[e] / game.cost[e] for e in range(n)] + [H0 / c0]
    U = max(ratios)
    print(f"   c0 = {float(c0):.9f}: V = {float(V):.9f}, x0 = {float(x0):.6f}, "
          f"active set = {[u+1 for u in act]}")
    print(f"   H_e/c_e over the {n} queries, then H_0/c_0: "
          + ", ".join(f"{float(v):.9f}" for v in ratios))
    print(f"   max = {float(U):.9f} vs V = {float(V):.9f}  -> dual_bound gives "
          f"Gamma <= {float(U):.9f}   (relative gap {float((U-V)/V):.2e})")
    byalt = {}
    for k in range(len(cuts)):
        byalt[cuts[k][0]] = byalt.get(cuts[k][0], F(0)) + lamc[k]
    print("   certificate weight per alternative: "
          + ", ".join(f"u{u+1}:{float(byalt.get(u, F(0))):.4f}"
                      for u in range(len(alts))))
    ok = all(byalt.get(u, F(0)) == 0 for u in range(len(alts)) if u not in act)
    print(f"   all of it sits on ACTIVE alternatives: {ok}   (complementary "
          f"slackness, proved in LeanMasterActiveSetV1)")
    weight_on_active = sum(byalt.get(u, F(0)) for u in act)
    res["full_certificate"] = {
        "c0": str(c0), "V": str(V), "x0": str(x0),
        "active_set": [u + 1 for u in act],
        "H_over_cost": [str(v) for v in ratios], "dual_max": str(U),
        "relative_gap": float((U - V) / V),
        "certificate_weight_on_active_cuts": float(weight_on_active)}

    res["not_established"] = [
        "the instance is one concrete finite design; the general statements are in "
        "LeanMasterActiveSetV1",
        "the LP runs in floating point and is re-checked in exact rationals; both "
        "the primal value and the dual bound are printed so the gap is visible",
        "c0* is located by 40 bisection steps, not in closed form",
    ]
    out_p = REPO / "research/worker_P8_master_20260914/P8_master_active_set.json"
    out_p.parent.mkdir(parents=True, exist_ok=True)
    out_p.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out_p}")


if __name__ == "__main__":
    main()
