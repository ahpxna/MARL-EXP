#!/usr/bin/env python3
"""P18 -- D6: a STRICT separation between the full design and the two-class family,
plus the two checks the audit says P7 skipped.

Audit items:

 D2  `P7.full_over_two` compares `L_full` with `L_two` -- BOTH lower bounds.  `L_full >
     L_two` proves nothing about the two optima.  What is needed is an UPPER bound
     `U_two` for every design supported on the two classes, and then `L_full > U_two`.
     This script computes `U_two` from the restricted LP's own cut multipliers, with
     charges at their certified LOWER end (which can only raise the bound), and reports
     the strict gap.

 D3  P7 checks the information at x = 0, 1 only and then calls the affine dependence
     pinned.  Means are affine but information is QUADRATIC.  Part 2 extracts the
     coefficients from x in {0, 1, -1} and then verifies them at three further points
     for every class and several d -- so the quadratic extraction itself is certified.

 D4  If the cutting-plane loop exhausts its rounds and appends a final cut, `cuts` can
     be longer than the LP's multiplier vector.  This script tracks the cuts that were
     actually in the SOLVED LP and records a convergence flag; multipliers are never
     paired with an unsolved cut.

The certificates are exact rationals; the LP is only a search.
"""
import json, os, sys
from fractions import Fraction as F

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from P7_d6_full_design import (all_classes, info_of, best_response, dual_upper,
                               enclose_zstar, enclose_charge, charge2, coarsen)

OUT = "research/worker_P18_d6_20260915"


def solve_tracked(q, mu, costs, classes, rounds=60):
    """Like P7.solve_full but returns the cuts that were in the SOLVED LP and a
    convergence flag, so multipliers are never paired with an unsolved cut."""
    n = len(classes)
    cuts = [(1, F(0)), (1, mu), (q, F(0))]
    inv = [F(1) / c for c in costs]
    w = None
    solved_cuts = None
    lp = None
    converged = False
    for _ in range(rounds):
        A_ub = [[-float(inv[i] * info_of(q, mu, classes[i][0], d, x))
                 for i in range(n)] + [1.0] for (d, x) in cuts]
        res = linprog(np.r_[np.zeros(n), -1.0], A_ub=np.array(A_ub),
                      b_ub=np.zeros(len(cuts)),
                      A_eq=np.array([np.r_[np.ones(n), 0.0]]), b_eq=[1.0],
                      bounds=[(0, None)] * n + [(None, None)], method="highs")
        if not res.success:
            return None
        w, lp = res.x[:n], res
        solved_cuts = list(cuts)
        wq = [F(float(v)).limit_denominator(10 ** 8) for v in w]
        sw = sum(wq)
        wq = [v / sw for v in wq]
        nq = [wq[i] * inv[i] for i in range(n)]
        br = best_response(q, mu, nq, classes)
        if (br[1], br[2]) in cuts:
            converged = True
            break
        cuts.append((br[1], br[2]))
    wq = [F(float(v)).limit_denominator(10 ** 8) for v in w]
    sw = sum(wq)
    wq = [v / sw for v in wq]
    nq = [wq[i] * inv[i] for i in range(n)]
    L, dstar, xstar = best_response(q, mu, nq, classes)
    return {"w": wq, "L": L, "solved_cuts": solved_cuts, "all_cuts": cuts,
            "converged": converged, "lp": lp, "argmin": (dstar, xstar), "nq": nq}


def lam_from(sol):
    """Rational mixture over the cuts ACTUALLY in the solved LP."""
    cuts = sol["solved_cuts"]
    mult = np.abs(np.array(sol["lp"].ineqlin.marginals, dtype=float))
    assert len(mult) == len(cuts), (len(mult), len(cuts))
    if mult.sum() <= 0:
        mult = np.ones(len(cuts))
    mult = mult / mult.sum()
    lam = [(cuts[k], F(float(mult[k])).limit_denominator(10 ** 8))
           for k in range(len(cuts)) if mult[k] > 1e-12]
    sl = sum(p for _c, p in lam)
    return [(c, p / sl) for c, p in lam]


def coefficient_test(q, mu):
    """D3: the information is EXACTLY quadratic in x; the coefficients extracted from
    {0, 1, -1} reproduce it at further points."""
    classes = all_classes(q)
    checks = 0
    for lab, _r in classes:
        for d in sorted({1, max(1, q // 2), q}):
            i0 = info_of(q, mu, lab, d, F(0))
            i1 = info_of(q, mu, lab, d, F(1))
            im = info_of(q, mu, lab, d, F(-1))
            c = i0
            a = (i1 + im - 2 * i0) / 2
            b = (i1 - im) / 2
            for xt in (F(1, 2), F(-1, 3), F(2, 7)):
                got = info_of(q, mu, lab, d, xt)
                want = c + b * xt + a * xt * xt
                assert got == want, (lab, d, xt, got, want)
                checks += 1
    return checks


def main():
    os.makedirs(OUT, exist_ok=True)
    cells = []
    print("PART 2 -- D3: information is exactly quadratic in x")
    coef = {}
    for mu in (F(1, 4), F(2, 5)):
        for q in (8, 16):
            n = coefficient_test(q, mu)
            coef[f"mu={mu},q={q}"] = n
            print(f"   mu={mu} q={q}: {n} exact coefficient checks PASS")

    print("\nPART 1 -- D2: L_full versus U_two (an UPPER bound for the two-class family)")
    for mu in (F(1, 4), F(2, 5)):
        g = 1 - mu
        for q in (8, 16):
            for t in (F(1, 2), F(1), F(2)):
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
                full = solve_tracked(q, mu, costs_hi, classes)
                if full is None:
                    print(f"   mu={mu} q={q} t={t}: full LP failed; skipped")
                    continue
                two_idx = [i for i, (lab, _r) in enumerate(classes)
                           if lab in (("scalar", "B"), ("query", 0, 2, 0))]
                cls2 = [classes[i] for i in two_idx]
                two = solve_tracked(q, mu, [costs_hi[i] for i in two_idx], cls2)
                if two is None:
                    print(f"   mu={mu} q={q} t={t}: two-class LP failed; skipped")
                    continue
                lam2 = lam_from(two)
                U_two, arg2 = dual_upper(q, mu, lam2, cls2,
                                         [costs_lo[i] for i in two_idx])
                L_full = full["L"]
                strict = L_full > U_two
                cells.append({
                    "mu": str(mu), "q": q, "t": str(t),
                    "L_full": str(L_full), "L_two": str(two["L"]),
                    "U_two": str(U_two),
                    "L_full_gt_U_two": bool(strict),
                    "separation_ratio_L_full_over_U_two": float(L_full / U_two),
                    "full_converged": full["converged"],
                    "two_converged": two["converged"],
                    "full_solved_cuts": len(full["solved_cuts"]),
                    "full_all_cuts": len(full["all_cuts"]),
                    "two_solved_cuts": len(two["solved_cuts"]),
                    "two_all_cuts": len(two["all_cuts"]),
                    "two_dual_argmax": list(map(str, arg2)),
                    "two_binding_alternatives": [[d, str(x), str(p)] for (d, x), p in lam2],
                })
                mark = "STRICT" if strict else "  --  "
                print(f"   mu={mu} q={q:3d} t={t}: L_full={float(L_full):.6e}  "
                      f"U_two={float(U_two):.6e}  {mark}  "
                      f"ratio={float(L_full/U_two):.6f}  "
                      f"conv(full/two)={full['converged']}/{two['converged']}")

    nstrict = sum(1 for c in cells if c["L_full_gt_U_two"])
    out = {
        "script": "P18_d6_full_vs_two.py",
        "D2_strict_separation": {
            "definition": "L_full is the exact value of one full design (a LOWER bound "
                          "on Gamma_full); U_two is a dual certificate valid for EVERY "
                          "design supported on {scalar B, B-pair}, with charges at their "
                          "certified LOWER end.  L_full > U_two therefore proves "
                          "Gamma_full > Gamma_two strictly.",
            "cells_strict": nstrict, "cells_total": len(cells),
        },
        "D3_coefficient_checks": coef,
        "D4_cut_accounting": "multipliers are read only from the cuts that were in the "
                             "SOLVED LP; a convergence flag is recorded per cell.",
        "cells": cells,
        "not_established": [
            "Gamma_full itself is not a closed form; only a certified bracket per cell.",
            "The alternative family is (d, x) as in the rest of the D6 chain.",
            "Charges r^z for r >= 3 use the z* bracket widened onto the 1/480 lattice, "
            "so bounds involving wide queries are conservative.",
            "No phase boundary is certified here.",
        ],
        "lean": "LeanD6ScalarInformationV1 (dual_over_all_queries is the certificate shape)",
    }
    path = os.path.join(OUT, "P18_d6_full_vs_two.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nstrict separations: {nstrict}/{len(cells)}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
