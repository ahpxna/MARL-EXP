#!/usr/bin/env python3
"""D6 package 2: the optimum over the WHOLE design space, including the class that
broke the scalar/pair certificate.

WHY THIS EXISTS.  `P1_d6_phase_law.py` PART 3-7 found that the scalar+pair
certificate is not universal: the binding dual orbit is always (s,t,b) = (2,0,0) --
a width-2 query on TWO coordinates of A -- its slack decays like 1/q, and it changes
SIGN at a boundary T_c(mu) that sits strictly BELOW t_end.  The instruction for that
case was explicit: keep the violating class as the result, ADD it to the design, and
solve the new equal-payoff problem -- do not retune the nuisance or the dual per
query to make the old certificate pass.  That is what this file does, and it does it
over EVERY legal class at once rather than over a guessed ansatz.

THE INFORMATION OF EVERY CLASS, DERIVED NOT ASSERTED.  An alternative at exchange
distance d removes d coordinates from A and adds d from B.  For a query class
(s,t,b) let  l = |S n A n (A\\C)| ~ Hypergeom(q+1, d, s)  and
m = |S n B n C| ~ Hypergeom(q, d, t), independent, and u = l - m.  Then from the
corpus's own `mean_query`,
    mean difference = ((t-b) + u) x  -  g u,        x = nu - mu,
so the per-sample information of the class against (d, x) is
    I_{s,t,b}(d,x) = [ x^2 ((t-b)^2 + 2(t-b)E u + E u^2)
                       - 2 g x ((t-b) E u + E u^2) + g^2 E u^2 ] / 2,
and the three width-1 scalar families have their own means:
    I_A = (d/(q+1)) (mu+x)^2/2,
    I_B = [ (d/q) mu^2 + ((q-d)/q) x^2 ] / 2,
    I_j = x^2/2.
Every one of these is CHECKED against brute-force enumeration over actual coordinate
subsets and actual alternative labels at q = 3, 4, and against `B1.general_poly` for
the scalar+B-pair design, before anything is optimised.  At d = 1 they also reproduce
D8's closed-form dual payoffs exactly, including the `(t-b)` that distinguishes a
query containing the special coordinate j.

THE PROGRAMME.  With budget shares w_e and charge cost_e = r^z (r = s+t+b, and 1 for
a scalar), the number of samples is w_e/cost_e, so
    Gamma_full = max_{w in Delta} min_{d in [1,q], x in [-mu, 1-mu]}
                 sum_e (w_e / cost_e) I_e(d, x).
It is solved by CUTTING PLANES over the alternatives: the LP is solved in floats, the
best response (exact minimisation of a clipped quadratic in x, over every d) is
computed in rationals, and the cut is added until no alternative is violated.  The
answer is then certified: the rational design gives a LOWER bound (charges taken at
their certified UPPER end, which can only reduce the sample count), and the rational
alternative mixture gives an UPPER bound max_e H_e(lambda)/cost_e over EVERY class
(charges at their certified LOWER end).  A cell is reported only when both are
computed; the gap between them is printed, never hidden.

WHAT IS FOUND
  * Below T_c the optimal support is exactly {scalar B, B-pair} -- the old ansatz is
    recovered, not assumed.
  * Above T_c the support gains the A-pair (2,0,0): a THIRD measurement type appears,
    and the two-class value is strictly below Gamma_full.
So the phase transition of the full game is a change in the OPTIMAL SUPPORT, and the
scalar/pair result is the low-t phase of a two-phase law.

WHAT THIS DOES NOT ESTABLISH
  * Gamma_full is computed per cell by a solver and certified by a rational
    primal/dual pair; it is not a closed form and nothing here is a Lean proof.
  * Charges r^z for r >= 3 go through the z* bracket widened onto a lattice, so the
    bounds involving wide queries are conservative.
  * The alternative set is (d, x) with d an exchange distance and x the nuisance;
    alternatives outside that family are not considered, exactly as in the rest of
    the D6 chain.

    .venv/bin/python scripts/P7_d6_full_design.py
"""
from __future__ import annotations

from fractions import Fraction as F
import importlib.util, itertools, json, math, sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO / "scripts"))
from certified_pow import enclose_root, enclose_charge, enclose_zstar

spec = importlib.util.spec_from_file_location(
    "b1", REPO / "scripts/B1_d6_width_transition_local.py")
b1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b1)

ZDEN = 480


def coarsen(z: F, up: bool) -> F:
    n = z * ZDEN
    return F(math.ceil(n) if up else math.floor(n), ZDEN)


def charge2(g, mu, h, digits=40):
    """certified bracket for 2**(z*-h) using 2**(z*) = 2 (g/mu)**2 EXACTLY."""
    p_, n_ = h.numerator, h.denominator
    lo, hi = enclose_root(F(2), -p_, n_, digits)
    base = 2 * (g / mu) ** 2
    return base * lo, base * hi


# ------------------------------------------------------------- hypergeom ----
def hyp_moments(N, K, n):
    """E[X], E[X^2] for X ~ Hypergeometric(N, K, n), exact."""
    if n == 0 or N == 0:
        return F(0), F(0)
    m = F(n * K, N)
    if N == 1:
        return m, m * m
    var = F(n) * F(K, N) * (1 - F(K, N)) * F(N - n, N - 1)
    return m, var + m * m


def u_moments(q, d, s, t):
    """u = l - m with l ~ Hyp(q+1, d, s) and m ~ Hyp(q, d, t), independent."""
    e1, e1sq = hyp_moments(q + 1, d, s)
    e2, e2sq = hyp_moments(q, d, t)
    v1, v2 = e1sq - e1 * e1, e2sq - e2 * e2
    eu = e1 - e2
    return eu, v1 + v2 + eu * eu


def query_info(q, mu, s, t, b, d, x):
    """per-sample information of class (s,t,b) against (d, x)."""
    g = 1 - mu
    eu, eu2 = u_moments(q, d, s, t)
    m = t - b
    return (x * x * (m * m + 2 * m * eu + eu2)
            - 2 * g * x * (m * eu + eu2) + g * g * eu2) / 2


def scalar_info(q, mu, kind, d, x):
    if kind == "A":
        return F(d, q + 1) * (mu + x) ** 2 / 2
    if kind == "B":
        return (F(d, q) * mu * mu + F(q - d, q) * x * x) / 2
    if kind == "j":
        return x * x / 2
    raise ValueError(kind)


def all_classes(q):
    """every legal measurement class: three width-1 scalar families and every query
    orbit, exactly the enumeration D8's dual uses."""
    out = [(("scalar", "A"), 1), (("scalar", "B"), 1), (("scalar", "j"), 1)]
    for s in range(q + 2):
        for t in range(q + 1):
            if not (1 <= s + t <= q):
                continue
            for bsw in (0, 1):
                if bsw == 0 and s + t < 2:
                    continue
                out.append((("query", s, t, bsw), s + t + bsw))
    return out


def info_of(q, mu, lab, d, x):
    if lab[0] == "scalar":
        return scalar_info(q, mu, lab[1], d, x)
    return query_info(q, mu, lab[1], lab[2], lab[3], d, x)


# ------------------------------------------------------------ self-checks ---
def brute_check():
    """Every closed form above, against enumeration over ACTUAL subsets and ACTUAL
    alternative labels, using the corpus's own mean functions."""
    print("PART 0 -- the per-class information, against brute-force enumeration")
    nchk = 0
    for q in (3, 4):
        coords, j, A, B = b1.universe(q)
        As, Bs = sorted(A), sorted(B)
        mu = F(1, 4)
        for d in range(1, q + 1):
            alts = []
            for R in itertools.combinations(As, d):
                for S in itertools.combinations(Bs, d):
                    alts.append(frozenset(set(A) - set(R)) | frozenset(S))
            for lab, _cost in all_classes(q):
                if lab[0] == "scalar":
                    kind = lab[1]
                    pts = As if kind == "A" else (Bs if kind == "B" else [j])
                    tot0 = tot1 = F(0)
                    for C in alts:
                        for i in pts:
                            for nu, acc in ((mu, 0), (mu + 1, 1)):
                                dd = (b1.mean_scalar(A, j, mu, i)
                                      - b1.mean_scalar(C, j, nu, i))
                                if acc == 0:
                                    tot0 += dd * dd / 2
                                else:
                                    tot1 += dd * dd / 2
                    n = len(alts) * len(pts)
                    got0, got1 = tot0 / n, tot1 / n
                    want0 = scalar_info(q, mu, kind, d, F(0))
                    want1 = scalar_info(q, mu, kind, d, F(1))
                    if got0 != want0 or got1 != want1:
                        raise AssertionError(
                            f"scalar {kind} q={q} d={d}: {got0},{got1} vs "
                            f"{want0},{want1}")
                    nchk += 2
                else:
                    _, s, t, bsw = lab
                    if s > len(As) or t > len(Bs):
                        continue
                    G = tuple(As[:s]) + tuple(Bs[:t])
                    h = bool(bsw)
                    tot0 = tot1 = F(0)
                    for C in alts:
                        for nu, acc in ((mu, 0), (mu + 1, 1)):
                            dd = (b1.mean_query(A, j, mu, G, h)
                                  - b1.mean_query(C, j, nu, G, h))
                            if acc == 0:
                                tot0 += dd * dd / 2
                            else:
                                tot1 += dd * dd / 2
                    got0, got1 = tot0 / len(alts), tot1 / len(alts)
                    want0 = query_info(q, mu, s, t, bsw, d, F(0))
                    want1 = query_info(q, mu, s, t, bsw, d, F(1))
                    if got0 != want0 or got1 != want1:
                        raise AssertionError(
                            f"query {lab} q={q} d={d}: {got0},{got1} vs "
                            f"{want0},{want1}")
                    nchk += 2
    print(f"   {nchk} exact agreements over q = 3, 4, every class, every d, at two "
          f"values of the nuisance (so the whole affine dependence is pinned)")

    # and the two-class design reproduces B1.general_poly
    n2 = 0
    for q in (3, 4, 5, 6):
        for mu in (F(1, 4), F(2, 5)):
            for eta in (F(1, 5), F(13, 20), F(1)):
                for cz in (F(3), F(37, 2)):
                    for d in range(1, q + 1):
                        for x in (F(0), F(1, 7), F(-1, 5)):
                            got = ((1 - eta) * scalar_info(q, mu, "B", d, x)
                                   + eta / cz * query_info(q, mu, 0, 2, 0, d, x))
                            want = b1.general_poly(q, mu, eta, cz, d, x)
                            if got != want:
                                raise AssertionError(
                                    f"two-class mismatch q={q} d={d} eta={eta}: "
                                    f"{got} vs {want}")
                            n2 += 1
    print(f"   the scalar-B + B-pair mixture reproduces B1.general_poly on {n2} "
          f"exact evaluations")
    return {"brute_force_agreements": nchk, "general_poly_agreements": n2}


# --------------------------------------------------------- the programme ----
def best_response(q, mu, weights, classes):
    """exact min over d in [1,q] and x in [-mu, 1-mu] of sum_e n_e I_e(d,x)."""
    lo, hi = -mu, 1 - mu
    best = None
    for d in range(1, q + 1):
        a = b = c = F(0)
        for (lab, _cost), n in zip(classes, weights):
            if n == 0:
                continue
            i0 = info_of(q, mu, lab, d, F(0))
            i1 = info_of(q, mu, lab, d, F(1))
            im = info_of(q, mu, lab, d, F(-1))
            # I is a quadratic in x: c + bx + ax^2
            c += n * i0
            a += n * (i1 + im - 2 * i0) / 2
            b += n * (i1 - im) / 2
        cands = [lo, hi]
        if a > 0:
            xs = -b / (2 * a)
            if lo <= xs <= hi:
                cands.append(xs)
        for x in cands:
            v = c + b * x + a * x * x
            if best is None or v < best[0]:
                best = (v, d, x)
    return best


def solve_full(q, mu, costs, classes, rounds=60):
    """cutting planes: LP in floats, exact best response, exact certification."""
    n = len(classes)
    cuts = [(1, F(0)), (1, mu), (q, F(0))]
    inv = [F(1) / c for c in costs]
    w = None
    for _ in range(rounds):
        A_ub = []
        for (d, x) in cuts:
            A_ub.append([-float(inv[i] * info_of(q, mu, classes[i][0], d, x))
                         for i in range(n)] + [1.0])
        res = linprog(np.r_[np.zeros(n), -1.0], A_ub=np.array(A_ub),
                      b_ub=np.zeros(len(cuts)),
                      A_eq=np.array([np.r_[np.ones(n), 0.0]]), b_eq=[1.0],
                      bounds=[(0, None)] * n + [(None, None)], method="highs")
        if not res.success:
            return None
        w = res.x[:n]
        wq = [F(float(v)).limit_denominator(10 ** 8) for v in w]
        sw = sum(wq)
        wq = [v / sw for v in wq]
        nq = [wq[i] * inv[i] for i in range(n)]
        br = best_response(q, mu, nq, classes)
        if (br[1], br[2]) in cuts:
            break
        cuts.append((br[1], br[2]))
    wq = [F(float(v)).limit_denominator(10 ** 8) for v in w]
    sw = sum(wq)
    wq = [v / sw for v in wq]
    nq = [wq[i] * inv[i] for i in range(n)]
    L, dstar, xstar = best_response(q, mu, nq, classes)
    return wq, L, cuts, (dstar, xstar), res


def dual_upper(q, mu, lam, classes, costs_lo):
    """max over EVERY class of H_e(lambda)/cost_e, with charges at their certified
    LOWER end so the bound can only be raised."""
    best = None
    for i, (lab, _c) in enumerate(classes):
        H = sum(p * info_of(q, mu, lab, d, x) for (d, x), p in lam)
        v = H / costs_lo[i]
        if best is None or v > best[0]:
            best = (v, lab)
    return best


def main():
    print("D6: the optimum over the WHOLE design space, with the class that broke")
    print("the scalar/pair certificate put back into the design\n")
    res = {"self_check": brute_check(), "cells": []}

    print("\nPART 1 -- Gamma_full, its support, and the two-class value beside it")
    for mu in (F(1, 4), F(2, 5)):
        g = 1 - mu
        for q in (8, 16):
            for t in (F(1, 2), F(1), F(3, 2), F(2), F(3)):
                h = t / q
                zs_lo, zs_hi = enclose_zstar(g, mu)
                zlo, zhi = coarsen(zs_lo - h, False), coarsen(zs_hi - h, True)
                cl, ch = charge2(g, mu, h)
                classes = all_classes(q)
                costs_hi, costs_lo = [], []
                for lab, r in classes:
                    if r == 1:
                        costs_hi.append(F(1)); costs_lo.append(F(1))
                    elif r == 2:
                        costs_hi.append(ch); costs_lo.append(cl)
                    else:
                        a, bb = enclose_charge(r, zlo, zhi, 12)
                        costs_hi.append(bb); costs_lo.append(a)
                sol = solve_full(q, mu, costs_hi, classes)
                if sol is None:
                    print(f"   mu={mu} q={q} t={t}: LP failed; skipped")
                    continue
                wq, L, cuts, (ds, xs), lp = sol
                sup = sorted((classes[i][0], wq[i]) for i in range(len(classes))
                             if wq[i] > F(1, 10 ** 5))
                # dual: the LP's multipliers on the cuts, rationalised
                mult = np.abs(np.array(lp.ineqlin.marginals, dtype=float))
                if mult.sum() <= 0:
                    mult = np.ones(len(cuts))
                mult = mult / mult.sum()
                lam = [(cuts[k], F(float(mult[k])).limit_denominator(10 ** 8))
                       for k in range(len(cuts)) if mult[k] > 1e-12]
                sl = sum(p for _c, p in lam)
                lam = [(c, p / sl) for c, p in lam]
                U, arg = dual_upper(q, mu, lam, classes, costs_lo)
                gap = float((U - L) / L) if L > 0 else float("nan")
                # the OLD two-class family, same charges, for comparison
                two = [i for i, (lab, _r) in enumerate(classes)
                       if lab in (("scalar", "B"), ("query", 0, 2, 0))]
                cls2 = [classes[i] for i in two]
                sol2 = solve_full(q, mu, [costs_hi[i] for i in two], cls2)
                L2 = sol2[1] if sol2 else None
                uses_third = any(lab == ("query", 2, 0, 0) for lab, _w in sup)
                print(f"   mu={mu} q={q:3d} t={t}: Gamma_full >= {float(L):.6e}  "
                      f"dual <= {float(U):.6e}  gap {gap:.2e}")
                print(f"      support: "
                      + ", ".join(f"{lab}:{float(v):.4f}" for lab, v in sup)
                      + ("   <- THIRD CLASS ACTIVE" if uses_third else ""))
                if L2 is not None:
                    print(f"      two-class (scalar B + B-pair) value "
                          f"{float(L2):.6e}   full/two = {float(L/L2):.9f}")
                res["cells"].append({
                    "mu": str(mu), "q": q, "t": str(t),
                    "Gamma_full_lower": str(L), "dual_upper": str(U),
                    "relative_gap": gap,
                    "support": [[list(map(str, lab)), str(v)] for lab, v in sup],
                    "third_class_active": bool(uses_third),
                    "two_class_value": None if L2 is None else str(L2),
                    "full_over_two": None if not L2 else float(L / L2),
                    "dual_argmax": list(map(str, arg)),
                    "binding_alternatives": [[d, str(x), str(p)] for (d, x), p in lam],
                })
    res["not_established"] = [
        "Gamma_full is computed per cell by a cutting-plane solver and certified by a "
        "rational primal/dual pair; it is not a closed form and not a Lean proof",
        "charges r^z for r >= 3 use the z* bracket widened onto the 1/480 lattice, so "
        "bounds involving wide queries are conservative",
        "the alternative family is (d, x) -- exchange distance and nuisance -- as in "
        "the rest of the D6 chain; nothing outside it is considered",
    ]
    out = REPO / "research/worker_P7_d6_fulldesign_20260914/P7_d6_full_design.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
