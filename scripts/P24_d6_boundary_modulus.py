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

The right-endpoint test instead uses the maximum width of the FULL primal support:
`L_full(t1)/rho_primal > U_two(t1)`. Reusing the two-class rho there is invalid. This is a
continuous statement obtained from two grid evaluations and an exact modulus.

The Lean counterparts are `LeanD6AlternativeReductionV1.no_crossing_of_modulus`
(a cell with no crossing) and `.crossing_bracket` (a cell that brackets one).

NOTE ON WHAT IS **NOT** CERTIFIED.  Failing the test certifies nothing: `L_full` is only
a lower bound, so a cell where the test fails may or may not contain a separation.  The
script reports those cells as UNDECIDED, never as "no separation".
"""
import argparse, json, os, sys
from pathlib import Path
from fractions import Fraction as F

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from P7_d6_full_design import (all_classes, enclose_zstar, enclose_charge, charge2,
                               coarsen, dual_upper)
from P18_d6_full_vs_two import solve_tracked, lam_from

OUT = "research/worker_P24_d6_corrected_20260915"

def enclose_power(base, exponent, bits=48):
    """Outward dyadic enclosure of base**exponent by integer comparisons only."""
    exponent = F(exponent)
    assert base >= 1 and exponent >= 0
    a, b = exponent.numerator, exponent.denominator
    den = 1 << bits
    target = base ** a * den ** b
    lo, hi = 0, den
    while hi ** b < target:
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** b <= target:
            lo = mid
        else:
            hi = mid
    low = F(lo, den)
    high = low if lo ** b == target else F(hi, den)
    assert low ** b <= F(base) ** a <= high ** b
    return low, high

def endpoint_record(v):
    return {"L_full": str(v["L_full"]), "U_two": str(v["U_two"]),
            "converged": v["converged"], "primal_max_width": v["primal_max_width"],
            "certificate": v["certificate"]}



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
    lam2 = lam_from(two)
    U_two, _arg = dual_upper(q, mu, lam2, cls2, [lo[i] for i in two_idx])
    assert sum(full['w']) == 1 and all(v >= 0 for v in full['w'])
    assert sum(p for _cut, p in lam2) == 1 and all(p >= 0 for _cut, p in lam2)
    support = [{'label': list(lab), 'width': r, 'budget_weight': str(w),
                'count_weight': str(n), 'charge_upper': str(ch)}
               for (lab, r), w, n, ch in zip(classes, full['w'], full['nq'], hi) if w > 0]
    return {'L_full': full['L'], 'U_two': U_two,
            'converged': full['converged'] and two['converged'],
            'primal_max_width': max(row['width'] for row in support),
            'certificate': {'q': q, 'mu': str(mu), 't': str(t),
                'primal_support': support,
                'primal_argmin': [full['argmin'][0], str(full['argmin'][1])],
                'dual_mixture': [[d, str(x), str(p)] for (d, x), p in lam2],
                'two_classes': [{'label': list(lab), 'width': r, 'charge_lower': str(lo[i])}
                                for i, (lab, r) in zip(two_idx, cls2)]}}



def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--out', default=str(Path(OUT) / 'P24_d6_boundary_modulus_v2.json'))
    args = parser.parse_args()
    out_path = Path(args.out)
    if out_path.exists():
        raise SystemExit(f'Refusing to overwrite {out_path}')
    cells = []
    # Only the TWO-CLASS family's widths enter the upper side: the B-scalar has r = 1
    # (cost 1, CONSTANT in t) and the B-pair has r = 2.  So the modulus for
    # Gamma_two is 2^((t1-t0)/q), not (q+1)^((t1-t0)/q).  The lower side needs only
    # monotonicity, which holds for every r >= 1.
    RMAX_TWO = 2
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
                width = float(t1 - t0)  # display only
                v0, v1 = fine[t0], fine[t1]
                exponent = (t1 - t0) / q
                rho_lo, rho_hi = enclose_power(RMAX_TWO, exponent)
                rp_lo, rp_hi = enclose_power(v1['primal_max_width'], exponent)
                left_gap = v0['L_full'] - rho_hi * v0['U_two']
                right_gap = v1['L_full'] - rp_hi * v1['U_two']
                left_ok, right_ok = left_gap > 0, right_gap > 0
                certified = left_ok or right_ok
                rho = float(rho_hi)  # display only
                cells.append({
                    "mu": str(mu), "q": q, "t0": str(t0), "t1": str(t1),
                    "cell_width": width, "rho_modulus": rho,
                    "rho_rule": "left: two-class width 2; right: actual full primal support width",
                    "exponent": str(exponent),
                    "rho_two_interval": [str(rho_lo), str(rho_hi)],
                    "rho_primal_interval": [str(rp_lo), str(rp_hi)],
                    "left_gap_exact": str(left_gap), "right_gap_exact": str(right_gap),
                    "endpoint_t0": endpoint_record(v0), "endpoint_t1": endpoint_record(v1),
                    "evidence_class": "RATIONAL_CERTIFICATE" if certified else "UNDECIDED",
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
        "test": "L_full(t0) > rho_two*U_two(t0) OR L_full(t1) > rho_primal*U_two(t1) certifies "
                "Gamma_full > Gamma_two on the WHOLE cell",
        "cells_certified": ncert, "cells_total": len(cells),
        "cells": cells,
        "not_established": [
            "Failing the test certifies NOTHING: L_full is only a lower bound, so an "
            "UNDECIDED cell may or may not contain a separation.  These cells are "
            "never reported as 'no separation'.",
            "No phase BOUNDARY is certified.  What is certified is, cell by cell, that "
            "the strict separation holds throughout -- not where it starts.",
            "The left test uses width 2 for Gamma_two; the right test uses the widest "
            "query in the full primal certificate. Cell selection uses floats but "
            "both final verdicts use outward rational enclosures and exact gaps.",
        ],
        "lean": "LeanD6AlternativeReductionV1.no_crossing_of_modulus / .crossing_bracket",
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open('x') as f:
        json.dump(out, f, indent=1)
    print(f"\ncells with the separation certified on the whole cell: {ncert}/{len(cells)}")
    print(f"artifact: {out_path}")


if __name__ == "__main__":
    main()
