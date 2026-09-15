#!/usr/bin/env python3
"""F-N7-Lower: exact-rational cross-check of the constants proved in
`work/p13_conjectures/LeanFunctionalCrossoverLowerV1.lean`.

The Lean module proves, with NO symmetry assumption:

  * `energy_ge_pairV` - every flipping alternative costs at least the pinch value
    of SOME pair of outsider cells (the "actual alternative" bridge);
  * `explicit_pairV_ge` - at the allocation p = q = 2/S, u = n d^2/S (S = 4+n d^2)
    every pair value is at least L = d^2/(8 S);
  * `crossover_sandwich` - that allocation is feasible, forces every alternative
    to cost at least L, and every allocation admits one costing at most 2 L.

This script re-derives the same three pair values in exact `Fraction` arithmetic
from the SAME harmonic-half formulas the N7 evaluator uses, and checks the three
ratio identities the Lean proof relies on:

    J_EE = L,    J_MM = L * 2/(1+d^2),    J_EM = L * (1+d)^2/(1+3 d^2),

so that min = L exactly. Raises on any mismatch.

    python3 scripts/F1_crossover_lower_check.py
"""
from fractions import Fraction as F
import json
from pathlib import Path


def harmonic_half(x, y):
    if x <= 0 or y <= 0:
        return F(0)
    return F(1, 2) * x * y / (x + y)


def pair_value(A, B, D):
    if A + B == 0:
        return F(0)
    return A * B * (1 - D) ** 2 / (A + B)


def three_costs(p, q, u, n, rho):
    """The three pair types at a symmetric allocation, from harmonic halves."""
    A = harmonic_half(F(p, 1) / 2 if isinstance(p, int) else p / 2,
                      p / 2 if not isinstance(p, int) else F(p, 1) / 2)
    A = harmonic_half(p / 2, p / 2)
    B_ee = harmonic_half(q / 2, q / 2)
    B_em = harmonic_half(q / 2, u / n)
    B_mm = harmonic_half(u / n, u / n)
    return (pair_value(A, B_ee, rho),
            pair_value(A, B_em, rho / 2),
            pair_value(A, B_mm, F(0)))


def main():
    rows = []
    checked = 0
    for n in (2, 3, 4, 7, 16, 64, 256, 1024, 4096):
        for num, den in ((1, 1), (99, 100), (3, 4), (1, 2), (2, 5), (1, 4),
                         (1, 10), (1, 100), (1, 1000)):
            d = F(num, den)
            rho = 1 - d
            S = 4 + n * d * d
            p = q = F(2) / S
            u = n * d * d / S
            if p + q + u != 1:
                raise AssertionError(f"allocation not a probability vector: n={n} d={d}")
            jee, jem, jmm = three_costs(p, q, u, n, rho)
            L = d * d / (8 * S)
            if jee != L:
                raise AssertionError(f"J_EE != L at n={n} d={d}: {jee} vs {L}")
            if jmm != L * F(2) / (1 + d * d):
                raise AssertionError(f"J_MM identity failed at n={n} d={d}")
            if jem != L * (1 + d) ** 2 / (1 + 3 * d * d):
                raise AssertionError(f"J_EM identity failed at n={n} d={d}")
            if min(jee, jem, jmm) != L:
                raise AssertionError(f"min over pair types != L at n={n} d={d}")
            # the upper bound of `crossover_upper`, and the factor 2
            kappa = min(F(1, 4), (1 - rho / 2) ** 2 / 2)
            U = kappa * d * d / (32 * kappa + n * d * d)
            if not (L <= U):
                raise AssertionError(f"lower exceeds upper at n={n} d={d}: {L} > {U}")
            if not (U <= 2 * L):
                raise AssertionError(f"upper exceeds 2*lower at n={n} d={d}")
            checked += 1
            if n in (16, 1024) and den in (1, 2, 100):
                rows.append({"n": n, "d": str(d), "L": str(L), "U": str(U),
                             "U_over_L": float(U / L)})
    print(f"exact-rational check passed on {checked} (n, d) configurations")
    print("  J_EE = L, J_MM = L*2/(1+d^2), J_EM = L*(1+d)^2/(1+3d^2), min = L")
    print("  L <= U <= 2L in every configuration")
    print(f"\n{'n':>6}{'d':>10}{'U/L':>10}")
    for r in rows:
        print(f"{r['n']:>6}{r['d']:>10}{r['U_over_L']:>10.5f}")
    out = Path("research/worker_F_N7_lower_20260914/F1_crossover_lower_check.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "claim": "at p=q=2/S, u=n d^2/S with S=4+n d^2, every pair value equals or "
                 "exceeds L=d^2/(8S); and L <= U <= 2L with U the three-witness bound",
        "lean_module": "work/p13_conjectures/LeanFunctionalCrossoverLowerV1.lean",
        "arithmetic": "exact Fraction throughout; no floating point decides anything",
        "configurations_checked": checked,
        "skipped": "n >= 8192 and d < 1/1000 were not swept (no reason to expect a "
                   "change; the identities are polynomial and were verified symbolically "
                   "by the Lean proof, which quantifies over all n and all 0 < d <= 1)",
        "sample_rows": rows,
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
