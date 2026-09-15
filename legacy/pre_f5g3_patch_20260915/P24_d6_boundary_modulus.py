#!/usr/bin/env python3
"""P24 -- D6: a CERTIFIED statement between the grid points.

Audit item D5: `sup_err_grid` is a supremum over a GRID.  Values at grid nodes say
nothing about the points between them, so a sign change on the grid is not a boundary
and no sign change is not an absence.  What repairs this is a MODULUS.

Here the modulus is exact, not estimated.  The charge of a width-`r` class is
`kappa_r(t) = c_r * r^(-t/q)` (the `z* - t/q` exponent), so for `t` in a cell
`[t0, t1]`,

    1/kappa_r(t) = (1/kappa_r(t0)) * r^((t-t0)/q),    1 <= r^((t-t0)/q) <= rho,
    rho := r_max^((t1-t0)/q).

Every information coefficient therefore scales by a factor in `[1, rho]` across the
cell, so for the max-min value of ANY family of classes

    V(t0) <= V(t) <= rho * V(t0)        for all t in [t0, t1].

Consequently, with `L_full(t)` a primal lower bound for the full design and `U_two(t)`
a dual upper bound for the two-class family:

    L_full(t0) > rho * U_two(t0)   ==>   Gamma_full(t) > Gamma_two(t)  for EVERY t in the cell,

and the same test from the right endpoint with `L_full(t1)/rho > U_two(t1)`.  That is a
continuous statement obtained from two grid evaluations and an exact modulus.

The Lean counterparts are `LeanD6AlternativeReductionV1.no_crossing_of_modulus`
(a cell with no crossing) and `.crossing_bracket` (a cell that brackets one).

NOTE ON WHAT IS **NOT** CERTIFIED.  Failing the test certifies nothing: `L_full` is only
a lower bound, so a cell where the test fails may or may not contain a separation.  The
script reports those cells as UNDECIDED, never as "no separation".
"""
import json, os, sys
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from P7_d6_full_design import (all_classes, enclose_zstar, enclose_charge, charge2,
                               coarsen, dual_upper)
from P18_d6_full_vs_two import solve_tracked, lam_from

OUT = "research/worker_P24_d6_20260915"


def cell_costs(q, mu, t):
    g = 1 - mu
    h = t / q
    zs_lo, zs_hi = enclose_zstar(g, mu)
    zlo, zhi = coarsen(zs_lo - h, False), coarsen(zs_hi - h, True)
    cl, ch = charge2(g, mu, h)
    classes = all_classes(q)
    hi, lo = [], []
    for lab, r in classes:
        if r == 1:
            hi.append(F(1)); lo.append(F(1))
        elif r == 2:
            hi.append(ch); lo.append(cl)
        else:
            a, bb = enclose_charge(r, zlo, zhi, 12)
            hi.append(bb); lo.append(a)
    return classes, hi, lo


def evaluate(q, mu, t):
    classes, hi, lo = cell_costs(q, mu, t)
    full = solve_tracked(q, mu, hi, classes)
    if full is None:
        return None
    two_idx = [i for i, (lab, _r) in enumerate(classes)
               if lab in (("scalar", "B"), ("query", 0, 2, 0))]
    cls2 = [classes[i] for i in two_idx]
    two = solve_tracked(q, mu, [hi[i] for i in two_idx], cls2)
    if two is None:
        return None
    U_two, _arg = dual_upper(q, mu, lam_from(two), cls2, [lo[i] for i in two_idx])
    return {"L_full": full["L"], "U_two": U_two, "converged": full["converged"] and two["converged"]}


def main():
    os.makedirs(OUT, exist_ok=True)
    cells = []
    # Only the TWO-CLASS family's widths enter the upper side: the B-scalar has r = 1
    # (cost 1, CONSTANT in t) and the B-pair has r = 2.  So the modulus for
    # Gamma_two is 2^((t1-t0)/q), not (q+1)^((t1-t0)/q).  The lower side needs only
    # monotonicity, which holds for every r >= 1.
    RMAX_TWO = 2.0
    for mu in (F(1, 4), F(2, 5)):
        for q in (8, 16):
            # coarse pass: find where the separation is strongest
            coarse = [F(1), F(3, 2), F(2), F(5, 2), F(3)]
            ratios = {}
            vals = {}
            for t in coarse:
                v = evaluate(q, mu, t)
                if v is None:
                    continue
                vals[t] = v
                ratios[t] = float(v["L_full"]) / float(v["U_two"])
            if not ratios:
                continue
            tbest = max(ratios, key=ratios.get)
            rbest = ratios[tbest]
            if rbest <= 1.0:
                print(f"  mu={mu} q={q}: no separation on the coarse grid; skipped")
                continue
            # the cell width the modulus can afford: 2^(w/q) < rbest
            import math
            wmax = q * math.log(rbest, 2.0)
            # take a dyadic width strictly below it
            w = F(1, 2)
            while float(w) >= wmax and w > F(1, 64):
                w = w / 2
            grid = [tbest - w, tbest, tbest + w]
            grid = [t for t in grid if t > 0]
            fine = {}
            for t in grid:
                v = vals.get(t) or evaluate(q, mu, t)
                if v is not None:
                    fine[t] = v
            for i in range(len(grid) - 1):
                t0, t1 = grid[i], grid[i + 1]
                if t0 not in fine or t1 not in fine:
                    continue
                width = float(t1 - t0)
                rho = RMAX_TWO ** (width / q)
                v0, v1 = fine[t0], fine[t1]
                left_ok = float(v0["L_full"]) > rho * float(v0["U_two"])
                right_ok = float(v1["L_full"]) / rho > float(v1["U_two"])
                certified = left_ok or right_ok
                cells.append({
                    "mu": str(mu), "q": q, "t0": str(t0), "t1": str(t1),
                    "cell_width": width, "rho_modulus": rho,
                    "rho_rule": "2^((t1-t0)/q): only the two-class widths {1,2} enter",
                    "L_full_t0": float(v0["L_full"]), "U_two_t0": float(v0["U_two"]),
                    "L_full_t1": float(v1["L_full"]), "U_two_t1": float(v1["U_two"]),
                    "ratio_t0": float(v0["L_full"]) / float(v0["U_two"]),
                    "ratio_t1": float(v1["L_full"]) / float(v1["U_two"]),
                    "test_from_left": left_ok, "test_from_right": right_ok,
                    "separation_certified_on_whole_cell": certified,
                    "converged": v0["converged"] and v1["converged"],
                })
                mark = "CERTIFIED" if certified else "UNDECIDED"
                print(f"  mu={mu} q={q:3d} t in [{t0},{t1}] w={width:.4f}: "
                      f"rho={rho:.6f}  ratio t0={float(v0['L_full'])/float(v0['U_two']):.6f} "
                      f"t1={float(v1['L_full'])/float(v1['U_two']):.6f}  {mark}")

    ncert = sum(1 for c in cells if c["separation_certified_on_whole_cell"])
    out = {
        "script": "P24_d6_boundary_modulus.py",
        "modulus": "exact and multiplicative: 1/kappa_r(t) scales by r^((t-t0)/q) in "
                   "[1, rho] with rho = r_max^((t1-t0)/q), so V(t0) <= V(t) <= rho V(t0) "
                   "for the max-min value of any family of classes",
        "test": "L_full(t0) > rho*U_two(t0)  OR  L_full(t1)/rho > U_two(t1)  certifies "
                "Gamma_full > Gamma_two on the WHOLE cell",
        "cells_certified": ncert, "cells_total": len(cells),
        "cells": cells,
        "not_established": [
            "Failing the test certifies NOTHING: L_full is only a lower bound, so an "
            "UNDECIDED cell may or may not contain a separation.  These cells are "
            "never reported as 'no separation'.",
            "No phase BOUNDARY is certified.  What is certified is, cell by cell, that "
            "the strict separation holds throughout -- not where it starts.",
            "The modulus uses r_max = 2, the widest class in the TWO-CLASS family, "
            "because only that family bounds Gamma_two from above; the B-scalar has "
            "cost 1, constant in t.  The cell width is chosen from the observed "
            "separation ratio so that rho is below it.",
        ],
        "lean": "LeanD6AlternativeReductionV1.no_crossing_of_modulus / .crossing_bracket",
    }
    path = os.path.join(OUT, "P24_d6_boundary_modulus.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\ncells with the separation certified on the whole cell: {ncert}/{len(cells)}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
