#!/usr/bin/env python3
"""R2: does the scalar-only design become optimal again below mu = 1/2?

The sharpened certificate (LeanD6ScalarWidthSharpV1) says the B-scalar design's
mixture bound holds as soon as

    (1 - mu)^2 * width  <=  mu^2 * (cost * variance).

In this game cost*variance = width^z, so the condition is
`(1-mu)^2 * width^(1-z) <= mu^2`. For z > 1 the binding width is the smallest
admissible one, 2, giving the threshold

    z*(mu) = 1 + 2 * log((1-mu)/mu) / log 2.

At mu = 1/4 that is 4.1699. The published 48-cell sweep stops at z = 2.5, so it
could not have seen the scalar-optimal region below 1/2. This probe runs the
SAME solver at z values straddling z*(mu) and checks:

  * below z*(mu): the optimum exceeds the scalar value mu^2/(2q), and the
    allocation is not scalar-only;
  * above z*(mu): the optimum equals mu^2/(2q) and the allocation is scalar-only.

Raises on mismatch. Re-run:
    .venv/bin/python scripts/R2_below_half_threshold.py
"""
import importlib.util
import json
import math
import sys
from pathlib import Path

# in-repo solver: the outside checkout is not a reproducible dependency.
REPO = Path(__file__).resolve().parents[1]
SOLVER = REPO / "research/worker_distinct_completion_20260913/width_cost_game.py"
GAME = REPO / "research/worker_distinct_research_acceptance_20260913/approximate_game.py"


def load_solver():
    if not SOLVER.exists():
        sys.exit(f"solver not found: {SOLVER}")
    spec = importlib.util.spec_from_file_location("wcg", SOLVER)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def z_star(mu, width=2.0):
    """Smallest z for which the sharp certificate holds at this width."""
    return 1.0 + 2.0 * math.log((1.0 - mu) / mu) / math.log(width)


def scalar_value(q, mu):
    return mu * mu / (2.0 * q)


def main():
    m = load_solver()
    rows = []
    for q in (3, 4):
        for mu in (0.25, 0.4):
            zs = z_star(mu)
            grid = [round(zs - 1.0, 4), round(zs - 0.25, 4),
                    round(zs + 0.25, 4), round(zs + 1.0, 4)]
            for z in grid:
                r = m.solve(q, mu, z)
                sv = scalar_value(q, mu)
                by_width = r["cost_mass_by_width"]
                # by_width carries explicit zero entries for the unused widths,
                # so test the width-1 (scalar) mass directly.
                scalar_only = float(by_width.get("1", by_width.get(1, 0.0))) > 1 - 1e-9
                rows.append({
                    "q": q, "mu": mu, "z": z, "z_star": zs,
                    "value": r["lower"], "scalar_value": sv,
                    "gap": r["gap"], "cost_mass_by_width": by_width,
                    "scalar_only": scalar_only,
                })
                print(f"q={q} mu={mu} z={z:<7} z*={zs:.4f}  value={r['lower']:.8f} "
                      f"scalar={sv:.8f}  widths={by_width}  gap={r['gap']:.2e}", flush=True)

    for row in rows:
        # the solver's own primal-dual gap must stay tight
        assert row["gap"] < 1e-7, row
        if row["z"] > row["z_star"]:
            assert abs(row["value"] - row["scalar_value"]) < 1e-7, (
                "above the threshold the optimum must equal the scalar value", row)
            assert row["scalar_only"], (
                "above the threshold the optimal design must be scalar-only", row)
        else:
            assert row["value"] > row["scalar_value"] + 1e-7, (
                "below the threshold the scalar value must be beaten", row)
            assert not row["scalar_only"], (
                "below the threshold the design must not be scalar-only", row)

    out = Path("research/worker_distinct_completion_20260913/R2_below_half_threshold.json")
    out.write_text(json.dumps({
        "claim": "scalar-only optimal iff (1-mu)^2 * width^(1-z) <= mu^2; "
                 "binding width 2 for z>1, so threshold z*(mu)=1+2log((1-mu)/mu)/log 2",
        "solver": str(SOLVER),
        "results": rows,
    }, indent=2) + "\n")
    print(f"\nall {len(rows)} cells matched the threshold prediction -> {out}")


if __name__ == "__main__":
    main()
