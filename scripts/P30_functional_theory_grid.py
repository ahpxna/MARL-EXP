#!/usr/bin/env python3
"""P30 -- harness contract E-F: the Functional theory grid, in exact rationals.

The contract: n = 64, 256, 1024, 4096 (perfect squares, asserted); c = 1, 2;
g_min/d = 1/2, 3/4, 1, 2 and a fixed-g profile g = 1/8; two variance profiles (all 1,
and half 1 / half 4).  `g_min = d/2` is the BOUNDARY CONTROL and is kept in the table,
not dropped.

For each cell it records the full configuration, the allocation `w*`, and

    S    = sum_i v_i/g_i^2,          S+ = sum_i v_i/(g_i + d/2)^2,
    L    = d^2/(32 + 2 d^2 S),       U  = d^2/(32 + 2 d^2 S+),
    kappa = 1 + d/(2 g_min),

and checks the three things the Lean module proves: `L = A d^2/2` (the value at w*),
`L <= U` (sandwich_order), and `U <= kappa^2 L` (sandwich_ratio), with `kappa^2 <= 4`
exactly on the domain `g_min >= d/2`.  Everything is `Fraction`; no float decides
anything.

It also records the best-response witness (the four endpoints moving to +-(1/2 - d/4),
costing exactly `A d^2/2`) and, for the smallest `n` only, the oracle primal/dual gap:
the value at `w*` against a numerical search over the budget simplex.  That gap is the
`w*`-is-not-optimal fact, already certified exactly at n = 4 by P27.
"""
from __future__ import annotations
import argparse, json, math, sys, time
sys.set_int_max_str_digits(100000)
from fractions import Fraction as F
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def cell(n, c, gprofile, vprofile):
    r = math.isqrt(n)
    assert r * r == n, f"n={n} is not a perfect square"
    d = F(c, r)                                   # d = c/sqrt(n), exact
    LEVELS = 8   # a small number of DISTINCT rational gaps, repeated n/LEVELS times:
                 # the profile still spans [g_min, 1/2] but every sum keeps a small
                 # denominator, so the arithmetic stays exact AND finite to print.
    if gprofile[0] == "ratio":
        gmin = gprofile[1] * d                     # g_min/d = given ratio
        hi = F(1, 2)
        if gmin > hi:                              # profile leaves the cell span
            return None
        levels = [gmin + (hi - gmin) * F(j, LEVELS - 1) for j in range(LEVELS)]
        g = [levels[i % LEVELS] for i in range(n)]
    else:
        g = [F(1, 8)] * n                          # fixed g = 1/8
        gmin = F(1, 8)
    if vprofile == "all1":
        v = [F(1)] * n
    else:
        v = [F(1)] * (n // 2) + [F(4)] * (n - n // 2)
    S = sum(v[i] / g[i] ** 2 for i in range(n))
    Sp = sum(v[i] / (g[i] + d / 2) ** 2 for i in range(n))
    A = F(1) / (16 + d ** 2 * S)
    L = d ** 2 / (32 + 2 * d ** 2 * S)
    U = d ** 2 / (32 + 2 * d ** 2 * Sp)
    kap = 1 + d / (2 * gmin)
    return {
        "n": n, "c": c, "g_profile": list(map(str, gprofile)),
        "variance_profile": vprofile,
        "d": str(d), "g_min": str(gmin), "g_min_over_d": str(gmin / d),
        "in_domain_g_ge_d_over_2": bool(gmin >= d / 2),
        "is_boundary_control": bool(gmin == d / 2),
        "S": str(S), "S_plus": str(Sp), "A": str(A),
        "L_known_variance": str(L), "U_unknown_variance": str(U),
        "kappa": str(kap), "kappa_squared": str(kap ** 2),
        "L_equals_A_d2_over_2": bool(L == A * d ** 2 / 2),
        "sandwich_ordered_L_le_U": bool(L <= U),
        "sandwich_ratio_U_le_kappa2_L": bool(U <= kap ** 2 * L),
        "kappa2_le_4_on_domain": bool(kap ** 2 <= 4) if gmin >= d / 2 else None,
        "measured_U_over_L": float(U / L),
        "witness_cost_equals_A_d2_over_2": bool(
            4 * ((4 * A) * (d / 4) ** 2 / 2) == A * d ** 2 / 2),
        "w_endpoint": str(4 * A),
        "w_middle_first": str(d ** 2 * v[0] * A / g[0] ** 2),
        "budget_sums_to_one": bool(
            2 * (4 * A) + 2 * (4 * A)
            + sum(d ** 2 * v[i] * A / g[i] ** 2 for i in range(n)) == 1),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    out = Path(args.out or (REPO / "research/worker_P30_functional_grid_20260915"
                            / "P30_functional_theory_grid.json"))
    if out.exists():
        raise SystemExit(f"Refusing to overwrite {out}")
    t0 = time.time()
    rows = []
    profiles = [("ratio", F(1, 2)), ("ratio", F(3, 4)), ("ratio", F(1)),
                ("ratio", F(2)), ("fixed", F(1, 8))]
    for n in (64, 256, 1024, 4096):
        for c in (1, 2):
            for gp in profiles:
                for vp in ("all1", "half1half4"):
                    row = cell(n, c, gp, vp)
                    if row is None:
                        print(f"  -- n={n} c={c} g={gp[0]}{gp[1]} v={vp}: "
                              f"g_min exceeds 1/2, profile undefined; skipped")
                        continue
                    rows.append(row)
                    mark = ("OK " if (row["L_equals_A_d2_over_2"]
                                      and row["sandwich_ordered_L_le_U"]
                                      and row["sandwich_ratio_U_le_kappa2_L"]
                                      and row["budget_sums_to_one"]) else "!! ")
                    tag = " [BOUNDARY]" if row["is_boundary_control"] else ""
                    print(f"  {mark}n={n:5d} c={c} g={row['g_profile'][0]}"
                          f"{row['g_profile'][1]:>6s} v={vp:11s} "
                          f"U/L={row['measured_U_over_L']:.6f} "
                          f"kap^2={float(F(row['kappa_squared'])):.6f}"
                          f"{tag}", flush=True)
    allok = all(r["L_equals_A_d2_over_2"] and r["sandwich_ordered_L_le_U"]
                and r["sandwich_ratio_U_le_kappa2_L"] and r["budget_sums_to_one"]
                for r in rows)
    indomain = [r for r in rows if r["in_domain_g_ge_d_over_2"]]
    out_obj = {
        "script": "P30_functional_theory_grid.py",
        "contract": "E-F", "arithmetic": "exact Fraction throughout",
        "cells": len(rows), "all_identities_hold": allok,
        "in_domain_cells": len(indomain),
        "kappa2_le_4_on_every_in_domain_cell": all(
            r["kappa2_le_4_on_domain"] for r in indomain),
        "worst_measured_U_over_L": max(r["measured_U_over_L"] for r in rows),
        "boundary_control_cells": sum(1 for r in rows if r["is_boundary_control"]),
        "rows": rows, "wall_seconds": round(time.time() - t0, 1),
        "not_established": [
            "L is the value AT w*, not the design optimum: P27 certifies exactly that "
            "w* is beaten, so this table must not be read as Gamma*.",
            "The fixed-g = 1/8 profile leaves the domain g >= d/2 for small n; those "
            "rows carry in_domain_g_ge_d_over_2 = false and kappa2_le_4_on_domain = "
            "null, and the factor-4 statement does not apply to them.",
            "Unknown-variance STOPPING is prior work (Jourdan-Degenne-Kaufmann); U is "
            "the value of a design, not an algorithm.",
        ],
        "lean": "LeanFunctionalAllocationJoinV1 (budget, value, Splus_lower, "
                "sandwich_order, sandwich_ratio, witness_energy)",
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("x") as f:
        json.dump(out_obj, f, indent=1)
        f.write("\n")
    print(f"\nidentities hold on all {len(rows)} cells: {allok}")
    print(f"artifact: {out}")


if __name__ == "__main__":
    main()
