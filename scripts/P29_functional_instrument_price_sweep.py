#!/usr/bin/env python3
"""P29 -- F5.5 item 4: scalar-only versus primitive contrast at EQUAL TOTAL PRICE.

SCOPE, FIRST.  This is the Top-1 identification SIDE model (audit F5).  Nothing here
transfers to the Functional group-range claim; the range model is
`LeanFunctionalRangeAlternativeUnionV1` and `P28`.  What this file settles is how the
three instrument models compare once price, setup and retention are all accounted for.

THREE OBSERVATION LAWS, one price budget `B = 1`:

  S  scalar only     -- independent reads of cell e, variance nu_e, price p per sample,
                        free allocation.  Opens K channels.
  A  primitive contrast -- an instrument returning ONLY the difference on pair (0,j),
                        variance nu_c, price c_c per read.  Opens K-1 channels.  The
                        raw cell values do not exist.
  D  retained pair   -- reads BOTH cells of the pair and KEEPS both values, price c_p
                        per read.  Opens K channels.  Cell 0's samples accumulate
                        across every pair, so its information is preserved and reused
                        for every alternative.  This is the model the audit says must
                        not be replaced by "two reads, values discarded".

Setup `kappa` is paid ONCE per channel opened, before any sample.  Feasibility is
checked BEFORE any information is computed: a support whose setup exceeds the budget
gets `INFEASIBLE_SETUP` and NO value and NO ratio.  A support whose setup exactly
exhausts the budget gets `NO_SAMPLING_BUDGET` and information 0.

CLOSED FORMS USED (all for the Top-1 alternative set, gaps `Delta_j = mu_0 - mu_j`):

  A:  max min_j Delta_j^2 x_j/(2 nu_c)  s.t.  sum_j x_j = X
      equalises Delta_j^2 x_j, giving  X/(2 nu_c sum_j Delta_j^{-2}).
  S:  numerical, max min_j Delta_j^2/(2(nu_0/w_0 + nu_j/w_j)) s.t. sum_e w_e = W.
  D:  numerical, with y_j reads of pair (0,j): cell 0 has sum_j y_j samples and cell j
      has y_j, so  min_j Delta_j^2/(2(nu_0/sum y + nu_j/y_j)).

THE TWO-CELL THRESHOLD AND WHY IT DOES NOT TRANSFER.  For K = 2 the optimal scalar
value is `Delta^2 W/(2(sqrt(nu_0)+sqrt(nu_1))^2)` and the contrast value is
`Delta^2 X/(2 nu_c)`; at equal price they tie exactly when `c_c nu_c =
(sqrt(nu_0)+sqrt(nu_1))^2`, which is 4 for unit variances and unit contrast price.
With several alternatives the scalar design SHARES cell 0 across all of them, so the
pairwise threshold moves.  This script reports the measured break-even per `(K, kappa,
prices)` and never quotes 4 as a constant.
"""
from __future__ import annotations
import argparse, json, time
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

REPO = Path(__file__).resolve().parents[1]


# ------------------------------------------------------------- feasibility ---
def budget_after_setup(total, kappa, channels):
    total, kappa = F(str(total)), F(str(kappa))
    assert total >= 0 and kappa >= 0 and channels >= 0
    remaining = total - kappa * channels
    if remaining < 0:
        return {"status": "INFEASIBLE_SETUP", "sample_budget": None,
                "setup_cost": float(kappa * channels)}
    if remaining == 0:
        return {"status": "NO_SAMPLING_BUDGET", "sample_budget": 0.0,
                "setup_cost": float(kappa * channels)}
    return {"status": "FEASIBLE", "sample_budget": float(remaining),
            "setup_cost": float(kappa * channels)}


# ------------------------------------------------------------------ models ---
def value_A(budget_price, gaps, nu_c, c_c):
    """primitive contrast: closed form."""
    if budget_price is None or budget_price <= 0:
        return 0.0 if budget_price == 0 else None
    reads = budget_price / c_c
    return float(reads / (2 * nu_c * np.sum(1.0 / gaps ** 2)))


def value_S(budget_price, gaps, nu, p):
    """scalar only: numerical max-min over the free allocation."""
    if budget_price is None or budget_price <= 0:
        return (0.0, None) if budget_price == 0 else (None, None)
    W = budget_price / p
    K = len(nu)

    def neg(z):
        w = np.abs(z) + 1e-14
        w = w / w.sum() * W
        return -min(gaps[j - 1] ** 2 / (2 * (nu[0] / w[0] + nu[j] / w[j]))
                    for j in range(1, K))

    best = None
    rng = np.random.default_rng(20260915)
    for z0 in [np.ones(K)] + [rng.random(K) + 0.1 for _ in range(24)]:
        r = minimize(neg, z0, method="Nelder-Mead",
                     options={"maxiter": 40000, "maxfev": 40000,
                              "xatol": 1e-12, "fatol": 1e-15})
        if best is None or r.fun < best.fun:
            best = r
    w = np.abs(best.x) + 1e-14
    w = w / w.sum() * W
    return float(-best.fun), w.tolist()


def value_D(budget_price, gaps, nu, c_p):
    """retained pair: cell 0 accumulates across every pair, so its information is
    preserved and reused for every alternative."""
    if budget_price is None or budget_price <= 0:
        return (0.0, None) if budget_price == 0 else (None, None)
    Y = budget_price / c_p
    K = len(nu)

    def neg(z):
        y = np.abs(z) + 1e-14
        y = y / y.sum() * Y
        tot = y.sum()
        return -min(gaps[j - 1] ** 2 / (2 * (nu[0] / tot + nu[j] / y[j - 1]))
                    for j in range(1, K))

    best = None
    rng = np.random.default_rng(20260916)
    for z0 in [np.ones(K - 1)] + [rng.random(K - 1) + 0.1 for _ in range(24)]:
        r = minimize(neg, z0, method="Nelder-Mead",
                     options={"maxiter": 40000, "maxfev": 40000,
                              "xatol": 1e-12, "fatol": 1e-15})
        if best is None or r.fun < best.fun:
            best = r
    y = np.abs(best.x) + 1e-14
    y = y / y.sum() * Y
    return float(-best.fun), y.tolist()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    out_path = Path(args.out or (REPO / "research/worker_P29_functional_price_20260915"
                                 / "P29_instrument_price_sweep.json"))
    if out_path.exists():
        raise SystemExit(f"Refusing to overwrite {out_path}")

    t0 = time.time()
    rows = []
    B, p, c_p = 1.0, 1.0, 2.0        # scalar price 1/sample; a retained pair costs 2
    for K in (2, 3, 4, 5):
        mu = np.array([1.0] + [1.0 - 0.3 * (i + 1) for i in range(K - 1)])
        gaps = mu[0] - mu[1:]
        nu = np.ones(K)
        for kappa in (0.0, 0.05, 0.1, 0.2, 0.3):
            bS = budget_after_setup(B, kappa, K)        # S opens K cell channels
            bA = budget_after_setup(B, kappa, K - 1)    # A opens K-1 contrast channels
            bD = budget_after_setup(B, kappa, K)        # D opens the same K cells
            vS, wS = value_S(bS["sample_budget"], gaps, nu, p)
            vD, yD = value_D(bD["sample_budget"], gaps, nu, c_p)
            for c_c in (1.0, 2.0):
                sweep, ratios = {}, {}
                for nu_c in (1.0, 2.0, 3.0, 4.0, 6.0, 8.0):
                    vA = value_A(bA["sample_budget"], gaps, nu_c, c_c)
                    sweep[str(nu_c)] = vA
                    ratios[str(nu_c)] = (vA / vS if (vA is not None and vS
                                                     and vS > 0) else None)
                # break-even: value_A scales exactly as 1/nu_c, so it is the ratio at 1
                be = ratios["1.0"]
                rows.append({
                    "K": K, "kappa": kappa, "scalar_price": p,
                    "contrast_price": c_c, "retained_pair_price": c_p,
                    "gaps": gaps.tolist(), "variances": nu.tolist(),
                    "budget_S": bS, "budget_A": bA, "budget_D": bD,
                    "S_scalar_only": vS, "S_allocation": wS,
                    "D_retained_pair": vD, "D_allocation": yD,
                    "A_by_contrast_variance": sweep,
                    "A_over_S_by_contrast_variance": ratios,
                    "break_even_contrast_variance_vs_S": be,
                    "D_over_S": (vD / vS if (vD is not None and vS and vS > 0)
                                 else None),
                    "comparable": bool(bS["status"] == "FEASIBLE"
                                       and bA["status"] == "FEASIBLE"
                                       and bD["status"] == "FEASIBLE"),
                })
                st = (f"S:{bS['status'][:4]} A:{bA['status'][:4]} D:{bD['status'][:4]}")
                if rows[-1]["comparable"]:
                    print(f"  K={K} kappa={kappa:.2f} c_c={c_c}: {st}  "
                          f"S={vS:.5e} D={vD:.5e} D/S={vD/vS:.4f}  "
                          f"break-even nu_c={be:.4f}", flush=True)
                else:
                    print(f"  K={K} kappa={kappa:.2f} c_c={c_c}: {st}  "
                          f"NOT COMPARABLE -- no ratio reported", flush=True)

    comp = [r for r in rows if r["comparable"]]
    two_cell = [r for r in comp if r["K"] == 2]
    out = {
        "script": "P29_functional_instrument_price_sweep.py",
        "experiment": "F5.5 item 4: scalar-only vs primitive contrast vs retained pair, "
                      "at equal TOTAL price, sweeping contrast variance and setup",
        "scope": "Top-1 identification SIDE model.  No transfer to the Functional "
                 "group-range claim (audit F5).",
        "feasibility_rule": "setup is charged per channel opened BEFORE any sample; a "
                            "support whose setup exceeds the budget is INFEASIBLE_SETUP "
                            "with no value and no ratio; one that exactly exhausts it is "
                            "NO_SAMPLING_BUDGET with information 0",
        "retention_rule": "the retained pair keeps BOTH raw values, so cell 0's samples "
                          "accumulate across every pair and inform every alternative; "
                          "discarding them would be a different experiment",
        "rows": rows,
        "comparable_cells": len(comp), "total_cells": len(rows),
        "two_cell_check": {
            "closed_form_threshold": "c_c * nu_c = (sqrt(nu_0)+sqrt(nu_1))^2",
            "value_for_unit_variances_and_unit_price": 4.0,
            "measured_break_even_at_K2": [r["break_even_contrast_variance_vs_S"]
                                          for r in two_cell],
        },
        "wall_seconds": round(time.time() - t0, 1),
        "not_established": [
            "The break-even contrast variance is measured PER INSTANCE FAMILY.  It is "
            "not a constant, and the two-cell value 4 must not be quoted for K > 2.",
            "S and D are numerical max-min candidates from 25 restarts; A is a closed "
            "form.  No global-optimality certificate is claimed for S or D.",
            "Real instrument noise, real prices and the real setup cost are modelling "
            "inputs, not findings.",
            "Top-1 alternatives only; this says nothing about the range problem.",
        ],
        "lean": "none -- this is a numerical instrument-cost study",
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("x") as f:
        json.dump(out, f, indent=1)
        f.write("\n")
    print(f"\ncomparable cells: {len(comp)}/{len(rows)}")
    print(f"artifact: {out_path}")


if __name__ == "__main__":
    main()
