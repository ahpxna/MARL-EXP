#!/usr/bin/env python3
"""Gói A - Functional: the EXACT finite optimum on a closed region.

Same family as scripts/N7_functional_extrema_crossover.py:
    incumbent theta_I = (-1/2, +1/2), outsider theta_O = (-rho/2, +rho/2, 0^n),
    Gaussian variance 1, unit cost per cell, allocation w on the 4+n cells,
    alternative set = {range(lambda_O) >= range(lambda_I)}.

NOTATION
    x = sqrt n,  H = x + 2 + sqrt 2,  a = (1 - rho/2)^2,  Delta = 1 - rho,
    p = mass on the two incumbent endpoints,
    q = mass on the two outsider endpoints,
    u = mass on the n middle cells,          p + q + u = 1.

WHAT THIS SCRIPT CHECKS (every check raises on mismatch; nothing prints-and-exits-0)

  A. THREE-COST IDENTITY, EXACT RATIONAL.  Over a grid of (n, rho, p, q, u) with
     rational data, including the degenerate faces u = 0, p = 0, q = 0:
         J_EE = p q Delta^2 / (8 (p+q))
         J_EM = a p q u / (2 (n p q + 2 p u + 4 q u))
         J_MM = p u / (4 (n p + 2 u))
     each equals the exact rational pair value of the corresponding ordered pair
     under the symmetric allocation, and min(J_EE, J_EM, J_MM) equals the exact
     minimum over ALL ordered pairs of cells (the quantity N7 calls J_symmetric_ref).

  B. GLOBAL UPPER BOUND (the inequality the Lean proof turns into a theorem).
     For EVERY allocation of the full 4+n simplex, not just symmetric ones,
         J(w) <= a / (2 (n/u + 2/q + 4/p))  <=  a / (2 H^2).

  C. FINITE OPTIMUM.  Whenever   Delta^2 H >= (2 + 2 sqrt 2) a  and  H >= 2 a (x+1),
         Gamma_n(rho) = a / (2 H^2)   at   (p,q,u) = (2, sqrt 2, sqrt n)/H,
     checked against N7's gamma_symmetric and, for small n, gamma_full (the
     unrestricted concave maximisation in full dimension).

  D. THE DOMAIN IS NOT VACUOUS AND NOT GLOBAL: points where a condition fails and
     the formula is genuinely wrong are exhibited, so the region is a real region.

  E. CONCAVITY and the INVARIANCES used by the symmetry argument, numerically.

NOT CHECKED HERE: any limit statement in n; the value of Gamma_n outside the
region of C; any claim about the full alternative set beyond this family.

    .venv/bin/python scripts/A1_functional_crossover_exact_region.py
"""
import itertools
import json
import math
import os
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from N7_functional_extrema_crossover import (  # noqa: E402
    J_closed, J_symmetric, J_symmetric_ref, gamma_symmetric, gamma_full,
)

OUT = "/Users/phanan/cig-amf-main/research/worker_gopA_20260913"
SQRT2 = math.sqrt(2.0)


class Mismatch(AssertionError):
    pass


def req(cond, msg):
    if not cond:
        raise Mismatch(msg)


# --------------------------------------------------------------- exact rational core

def hh(x, y):
    """(1/2) x y / (x + y), the pair constant of a two-point quadratic. 0 if a
    cell is massless: a massless cell is displaced for free."""
    if x <= 0 or y <= 0:
        return F(0)
    return F(1, 2) * x * y / (x + y)


def pair_value(A, B, D):
    """min over z of  A (1-z)^2 + B (z-D)^2  =  A B (1-D)^2 / (A+B).
    Zero if either constant is zero (that side moves for free)."""
    if A <= 0 or B <= 0:
        return F(0)
    return A * B * (1 - D) ** 2 / (A + B)


def J_allpairs_exact(p, q, u, rho, n):
    """min over ALL ordered pairs of outsider cells, exact rational, for the
    symmetric allocation (p over 2 incumbent cells, q over 2 outsider endpoints,
    u over n middle cells). No closed form is used."""
    if min(p, q, u) < 0:
        raise Mismatch("negative mass")
    A = hh(p / 2, p / 2)                       # = p/8
    means = [rho / 2, -rho / 2] + [F(0)] * n
    mass = [q / 2, q / 2] + [u / n] * n
    if A <= 0 or any(m <= 0 for m in mass):
        return F(0)                            # a massless cell makes the flip free
    best = None
    for i, j in itertools.permutations(range(len(mass)), 2):
        D = means[i] - means[j]
        if D >= 1:
            return F(0)
        v = pair_value(A, hh(mass[i], mass[j]), D)
        best = v if best is None else min(best, v)
    return best


def J_EE(p, q, u, rho, n):
    return p * q * (1 - rho) ** 2 / (8 * (p + q))


def J_EM(p, q, u, rho, n):
    a = (1 - rho / 2) ** 2
    return a * p * q * u / (2 * (n * p * q + 2 * p * u + 4 * q * u))


def J_MM(p, q, u, rho, n):
    return p * u / (4 * (n * p + 2 * u))


# ------------------------------------------------------- A. three-cost identity, exact

def check_three_cost_identity():
    """Each closed form is the exact pair value of its ordered pair, and their
    minimum is the exact all-pairs minimum. Rational arithmetic throughout."""
    rows, skipped = [], []
    grid = []
    for pn, qn in [(1, 1), (1, 2), (2, 1), (3, 1), (1, 5), (5, 3), (7, 2), (1, 97)]:
        for den in (10, 16, 101):
            p, q = F(pn, den), F(qn, den)
            if p + q < 1:
                grid.append((p, q, 1 - p - q))
    faces = [(F(1, 2), F(1, 2), F(0)),          # u = 0
             (F(0), F(1, 2), F(1, 2)),          # p = 0
             (F(1, 2), F(0), F(1, 2)),          # q = 0
             (F(1, 3), F(1, 3), F(1, 3))]
    grid += faces
    nchecked = 0
    for n in (2, 3, 5, 9, 17):
        for rho in (F(0), F(1, 4), F(1, 2), F(3, 4), F(9, 10), F(99, 100)):
            a = (1 - rho / 2) ** 2
            for p, q, u in grid:
                # the three named pair values, computed from the definition
                A = p / 8
                vEE = pair_value(A, hh(q / 2, q / 2), rho)
                vEM = pair_value(A, hh(q / 2, u / n), rho / 2)
                vMM = pair_value(A, hh(u / n, u / n), F(0)) if n >= 2 else None
                # the claimed closed forms; denominators vanish only at the
                # vertices of the simplex, which are excluded and recorded
                if p + q == 0 or (n * p * q + 2 * p * u + 4 * q * u) == 0 \
                        or (n * p + 2 * u) == 0:
                    skipped.append({"n": n, "rho": str(rho), "p": str(p), "q": str(q),
                                    "u": str(u), "why": "closed form has a zero denominator "
                                                        "(two of p,q,u vanish)"})
                    continue
                fEE, fEM, fMM = (J_EE(p, q, u, rho, n), J_EM(p, q, u, rho, n),
                                 J_MM(p, q, u, rho, n))
                req(vEE == fEE, f"J_EE identity: n={n} rho={rho} (p,q,u)=({p},{q},{u}) "
                                f"pair={vEE} formula={fEE}")
                req(vEM == fEM, f"J_EM identity: n={n} rho={rho} (p,q,u)=({p},{q},{u}) "
                                f"pair={vEM} formula={fEM}")
                req(vMM == fMM, f"J_MM identity: n={n} rho={rho} (p,q,u)=({p},{q},{u}) "
                                f"pair={vMM} formula={fMM}")
                # and their minimum is the exact minimum over all ordered pairs
                mn = min(fEE, fEM, fMM)
                allp = J_allpairs_exact(p, q, u, rho, n)
                req(mn == allp, f"three-cost min != all-pairs min: n={n} rho={rho} "
                                f"(p,q,u)=({p},{q},{u}) min3={mn} all={allp}")
                # and the float evaluator of N7 agrees
                fl, _ = J_symmetric_ref(float(p), float(q), float(u), float(rho), n)
                req(abs(fl - float(mn)) <= 1e-12 * max(1.0, abs(fl)),
                    f"N7 float evaluator disagrees: n={n} rho={rho} ({p},{q},{u}) "
                    f"{fl} vs {float(mn)}")
                nchecked += 1
                if len(rows) < 6:
                    rows.append({"n": n, "rho": str(rho), "p": str(p), "q": str(q),
                                 "u": str(u), "J_EE": str(fEE), "J_EM": str(fEM),
                                 "J_MM": str(fMM), "min": str(mn)})
    return {"points_checked": nchecked, "sample": rows,
            "skipped_zero_denominator": skipped[:8],
            "skipped_count": len(skipped)}


# ------------------------------------------------- B. global upper bound, full simplex

def check_global_upper_bound(trials=400):
    """J(w) <= a / (2 (n/u + 2/q + 4/p)) <= a/(2H^2) for EVERY allocation of the
    full 4+n simplex - no symmetry assumed. This is the inequality the Lean
    theorem proves; here it is stress-tested against the all-pairs evaluator."""
    rng = random.Random(20260913)
    worst_slack_1 = worst_slack_2 = float("inf")
    for _ in range(trials):
        n = rng.choice([2, 3, 4, 6, 9])
        rho = rng.choice([0.0, 0.25, 0.5, 0.75, 0.9])
        # deliberately lopsided allocations: the bound must survive p != q etc.
        raw = [math.exp(rng.uniform(-6, 1)) for _ in range(4 + n)]
        s = sum(raw)
        w = [t / s for t in raw]
        wI0, wI1, wO = w[0], w[1], w[2:]
        J, _ = J_closed(wI0, wI1, wO, rho, n)
        p = wI0 + wI1
        q = wO[0] + wO[1]
        u = sum(wO[2:])
        a = (1 - rho / 2) ** 2
        S = n / u + 2 / q + 4 / p
        b1 = a / (2 * S)
        H = math.sqrt(n) + 2 + SQRT2
        b2 = a / (2 * H * H)
        req(J <= b1 * (1 + 1e-9), f"masswise bound violated: n={n} rho={rho} J={J} b={b1}")
        req(b1 <= b2 * (1 + 1e-12), f"Cauchy-Schwarz step violated: n={n} S={S} H^2={H*H}")
        worst_slack_1 = min(worst_slack_1, (b1 - J) / b1)
        worst_slack_2 = min(worst_slack_2, (b2 - b1) / b2)
    return {"trials": trials, "min_relative_slack_J_vs_masswise": worst_slack_1,
            "min_relative_slack_masswise_vs_H": worst_slack_2}


# ------------------------------------------------------------ C. the finite optimum

def in_region(n, rho):
    x = math.sqrt(n)
    H = x + 2 + SQRT2
    a = (1 - rho / 2) ** 2
    D = 1 - rho
    return D * D * H - (2 + 2 * SQRT2) * a, H - 2 * a * (x + 1)


def predicted(n, rho):
    x = math.sqrt(n)
    H = x + 2 + SQRT2
    a = (1 - rho / 2) ** 2
    return a / (2 * H * H), (2 / H, SQRT2 / H, x / H)


def check_finite_optimum():
    """Gamma_n(rho) = a/(2H^2) at (2, sqrt2, sqrt n)/H inside the region."""
    pts = [(1024, 0.75), (65536, 0.9), (4096, 0.6)]           # the supervisor's points
    pts += [(n, rho) for n in (4, 9, 16, 64, 256, 2048)
            for rho in (0.0, 0.3, 0.5, 0.75, 0.9)]
    rows, skipped = [], []
    for n, rho in pts:
        c1, c2 = in_region(n, rho)
        g, w = predicted(n, rho)
        if c1 < 0 or c2 < 0:
            skipped.append({"n": n, "rho": rho, "cond1": c1, "cond2": c2,
                            "why": "outside the region; the formula is not claimed here"})
            continue
        jw, tag = J_symmetric(w[0], w[1], w[2], rho, n)
        req(abs(jw - g) <= 1e-11 * g,
            f"value at the stated allocation: n={n} rho={rho} {jw} vs {g}")
        req(tag == "EM", f"active pair at the optimum is {tag}, not EM: n={n} rho={rho}")
        gs, ws, tg = gamma_symmetric(rho, n)
        req(gs <= g * (1 + 1e-9), f"search beats the claimed optimum: n={n} rho={rho} "
                                  f"{gs} > {g}")
        req(gs >= g * (1 - 1e-7), f"search falls short of the claimed optimum: "
                                  f"n={n} rho={rho} {gs} < {g}")
        for k, name in enumerate(("p", "q", "u")):
            req(abs(ws[k] - w[k]) <= 1e-4 + 1e-3 * w[k],
                f"argmax {name}: n={n} rho={rho} search={ws[k]} claimed={w[k]}")
        rows.append({"n": n, "rho": rho, "cond1": c1, "cond2": c2, "Gamma_claimed": g,
                     "Gamma_search": gs, "rel": (gs - g) / g, "active": tg,
                     "p*": w[0], "q*": w[1], "u*": w[2], "p_over_q": w[0] / w[1]})
    return {"rows": rows, "skipped_outside_region": skipped}


def check_finite_optimum_full_dimension():
    """The same claim refereed by the UNRESTRICTED maximisation over the whole
    4+n simplex (scipy, concave program). Only small n is affordable."""
    rows = []
    # The region is a narrow band at small n (empty at n = 4), so the points are
    # chosen INSIDE it: scanning rho in 0.01 steps, the admissible band is
    # n=9: [0.21,0.23], n=16: [0.28,0.32], n=25: [0.33,0.39], n=36: [0.36,0.44],
    # n=49: [0.39,0.48], n=64: [0.41,0.51], n=100: [0.44,0.57].
    # A few out-of-region points are kept to record that they are NOT refereed.
    for n, rho in [(9, 0.22), (16, 0.30), (25, 0.36), (36, 0.40), (49, 0.44),
                   (64, 0.46), (64, 0.50), (100, 0.50),
                   (4, 0.0), (16, 0.0), (64, 0.75)]:
        c1, c2 = in_region(n, rho)
        if c1 < 0 or c2 < 0:
            rows.append({"n": n, "rho": rho, "skipped": "outside the region"})
            continue
        g, _ = predicted(n, rho)
        # N7's gamma_full returns (value, allocation, n_converged) and RAISES if
        # no feasible start converged; unpack it rather than comparing the tuple.
        gf, wf, nconv = gamma_full(rho, n, starts=8)
        req(nconv >= 1, f"full-dimensional referee reported no converged start: n={n} rho={rho}")
        req(wf is not None and abs(sum(wf) - 1.0) < 1e-6 and min(wf) >= -1e-8,
            f"full-dimensional referee returned an infeasible allocation: n={n} rho={rho} {wf}")
        req(gf <= g * (1 + 1e-6),
            f"full-dimensional search beats the claimed optimum: n={n} rho={rho} "
            f"{gf} > {g}")
        req(gf >= g * (1 - 1e-5),
            f"full-dimensional search falls short: n={n} rho={rho} {gf} < {g}")
        rows.append({"n": n, "rho": rho, "Gamma_claimed": g, "gamma_full": gf,
                     "rel": (gf - g) / g, "converged_starts": nconv})
    return rows


# ------------------------------------------------------ D. the region is a real region

def check_region_is_sharp():
    """Outside the region the formula must actually fail, otherwise the two
    conditions would be decoration. We look for witnesses of both kinds."""
    fails = {"cond1": None, "cond2": None}
    for n in (4, 9, 16, 64, 256, 1024, 4096):
        for rho in [i / 100 for i in range(0, 100, 1)]:
            c1, c2 = in_region(n, rho)
            g, _ = predicted(n, rho)
            gs, _, tag = gamma_symmetric(rho, n)
            wrong = gs < g * (1 - 1e-6)
            if c1 < 0 <= c2 and wrong and fails["cond1"] is None:
                fails["cond1"] = {"n": n, "rho": rho, "cond1": c1, "cond2": c2,
                                  "Gamma_true": gs, "formula": g, "active": tag}
            if c2 < 0 <= c1 and wrong and fails["cond2"] is None:
                fails["cond2"] = {"n": n, "rho": rho, "cond1": c1, "cond2": c2,
                                  "Gamma_true": gs, "formula": g, "active": tag}
    req(fails["cond1"] is not None,
        "no witness found where condition 1 fails and the formula breaks")
    req(fails["cond2"] is not None,
        "no witness found where condition 2 fails and the formula breaks")
    return fails


# ------------------------------------------------- E. concavity and the invariances

def check_concavity_and_invariance(trials=120):
    """J is an infimum of functions linear in the allocation, so it is concave;
    and it is invariant under permuting the middle cells and under the global
    reflection. Both are the hypotheses of the averaging argument."""
    rng = random.Random(77)
    worst_gap = 0.0
    for _ in range(trials):
        n = rng.choice([2, 3, 5])
        rho = rng.choice([0.0, 0.5, 0.9])
        dim = 4 + n

        def rand():
            r = [rng.uniform(0.02, 1.0) for _ in range(dim)]
            s = sum(r)
            return [t / s for t in r]

        w1, w2 = rand(), rand()
        t = rng.uniform(0.05, 0.95)
        mix = [t * x + (1 - t) * y for x, y in zip(w1, w2)]
        j1 = J_closed(w1[0], w1[1], w1[2:], rho, n)[0]
        j2 = J_closed(w2[0], w2[1], w2[2:], rho, n)[0]
        jm = J_closed(mix[0], mix[1], mix[2:], rho, n)[0]
        req(jm >= t * j1 + (1 - t) * j2 - 1e-12,
            f"concavity violated: n={n} rho={rho} {jm} < {t*j1+(1-t)*j2}")
        worst_gap = max(worst_gap, (t * j1 + (1 - t) * j2) - jm)
        # permuting the middle cells
        mid = w1[4:]
        perm = mid[:]
        rng.shuffle(perm)
        wp = w1[:4] + perm
        jp = J_closed(wp[0], wp[1], wp[2:], rho, n)[0]
        req(abs(jp - j1) <= 1e-12 * max(1.0, j1),
            f"middle-cell permutation changed J: {jp} vs {j1}")
        # the reflection that swaps both endpoint pairs
        wr = [w1[1], w1[0], w1[3], w1[2]] + w1[4:]
        jr = J_closed(wr[0], wr[1], wr[2:], rho, n)[0]
        req(abs(jr - j1) <= 1e-12 * max(1.0, j1),
            f"reflection changed J: {jr} vs {j1}")
    return {"trials": trials, "worst_concavity_gap_observed": worst_gap}


def main():
    os.makedirs(OUT, exist_ok=True)
    res = {}
    res["A_three_cost_identity_exact"] = check_three_cost_identity()
    print("A. three-cost identity (exact rational): "
          f"{res['A_three_cost_identity_exact']['points_checked']} points OK, "
          f"{res['A_three_cost_identity_exact']['skipped_count']} skipped "
          "(zero denominator at simplex vertices)")
    res["B_global_upper_bound"] = check_global_upper_bound()
    print(f"B. global upper bound over the FULL simplex: OK "
          f"(min slack {res['B_global_upper_bound']['min_relative_slack_J_vs_masswise']:.2e})")
    res["C_finite_optimum"] = check_finite_optimum()
    print(f"C. finite optimum inside the region: "
          f"{len(res['C_finite_optimum']['rows'])} points OK, "
          f"{len(res['C_finite_optimum']['skipped_outside_region'])} outside the region")
    res["C_full_dimension"] = check_finite_optimum_full_dimension()
    print(f"C'. refereed in full dimension: {len(res['C_full_dimension'])} points")
    res["D_region_sharpness"] = check_region_is_sharp()
    print("D. both conditions have failure witnesses: "
          f"cond1 at {res['D_region_sharpness']['cond1']['n'], res['D_region_sharpness']['cond1']['rho']}, "
          f"cond2 at {res['D_region_sharpness']['cond2']['n'], res['D_region_sharpness']['cond2']['rho']}")
    res["E_concavity_invariance"] = check_concavity_and_invariance()
    print("E. concavity + middle-permutation + reflection invariance: OK")

    path = os.path.join(OUT, "A1_functional_crossover_exact_region.json")
    with open(path, "w") as f:
        json.dump(res, f, indent=2, sort_keys=True, default=str)
    print("wrote", path)
    print("\nall checks passed")


if __name__ == "__main__":
    main()
