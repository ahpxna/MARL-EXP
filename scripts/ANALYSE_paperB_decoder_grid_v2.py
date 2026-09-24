#!/usr/bin/env python3
"""Reanalyse saved decoder COUNTS; never sample or call the producer.

Both CP tails are budgeted simultaneously. No monotonicity of a fixed decoder's
error in N is assumed. Only a CONTIGUOUS failed prefix of tested budgets gives
a lower bound on the first successful TESTED budget. This is not minimax sample
complexity and does not exclude any untested integer budget.
"""
import argparse
import hashlib
import json
import math
from collections import defaultdict
from pathlib import Path

from scipy.stats import beta


def sha(data):
    return hashlib.sha256(data).hexdigest()


def cp_two_sided(bad, n, tail):
    if not 0 <= bad <= n or n <= 0 or not 0 < tail < 0.5:
        raise ValueError((bad, n, tail))
    lo = 0.0 if bad == 0 else float(beta.ppf(tail, bad, n - bad + 1))
    hi = 1.0 if bad == n else float(beta.isf(tail, bad + 1, n - bad))
    if not 0 <= lo <= hi <= 1:
        raise ArithmeticError((lo, hi))
    return lo, hi


def grid_bracket(bounds, delta):
    """bounds[N]=(lower/upper on worst-world error at N).

The first unexcluded rung is a lower bound on the optimum over THIS finite
grid. One later failed rung cannot skip over an earlier unknown rung.
"""
    ns = sorted(bounds)
    if not ns:
        raise ValueError("empty grid")
    high = next((n for n in ns if bounds[n][1] <= delta), None)
    failed_prefix = []
    for n in ns:
        if bounds[n][0] > delta:
            failed_prefix.append(n)
        else:
            break
    low = ns[len(failed_prefix)] if len(failed_prefix) < len(ns) else None
    if high is not None and (low is None or low > high):
        raise AssertionError("contradictory simultaneous bounds")
    return {
        "grid": ns,
        "failed_prefix": failed_prefix,
        "grid_min_lower_inclusive": low,
        "certified_upper": high,
        "all_tested_budgets_ruled_out": len(failed_prefix) == len(ns),
        "has_data_on_both_sides": bool(failed_prefix and high is not None),
        "lower_bound_on_all_integer_budget_minimum": None,
    }


def slope_interval(points):
    """Exact range of OLS slope over the rectangular log-budget brackets.

No power-law assumption or finite-h bias correction is smuggled in.
"""
    if len(points) < 2:
        return None
    xs = [math.log(p["h"]) for p in points]
    xbar = sum(xs) / len(xs)
    den = sum((x - xbar) ** 2 for x in xs)
    if den == 0:
        return None
    coefficients = [(x - xbar) / den for x in xs]
    lo = hi = 0.0
    for c, p in zip(coefficients, points):
        a, b = math.log(p["total_lower"]), math.log(p["total_upper"])
        lo += c * (a if c >= 0 else b)
        hi += c * (b if c >= 0 else a)
    return {"lower": lo, "upper": hi, "points": points,
            "scope": "OLS slope of the first successful tested budget; finite h; not an asymptotic or minimax exponent"}


def analyse(data, confidence=0.95):
    rows = data["results"]
    if not rows:
        raise ValueError("no raw count rows")
    tail = (1.0 - confidence) / (2 * len(rows))
    panels = defaultdict(lambda: defaultdict(dict))
    corrected = []
    for row in rows:
        m, h, dec = int(row["m"]), float(row["h"]), row["decoder"]
        if dec not in {"safe", "identification"}:
            raise ValueError(dec)
        n, world = int(row["N_per_query"]), int(row["world"])
        bad, reps = int(row["bad"]), int(row["reps"])
        multiplier = 1 if dec == "safe" else m - 1
        if n <= 0 or int(row["total_budget"]) != multiplier * n:
            raise ValueError("total-budget mismatch")
        lo, hi = cp_two_sided(bad, reps, tail)
        cell = panels[(m, h, dec)][n]
        if world in cell:
            raise ValueError("duplicate world/budget row")
        cell[world] = (lo, hi)
        corrected.append({"m": m, "h": h, "decoder": dec, "world": world,
                          "N_per_query": n, "total_budget": multiplier*n,
                          "bad": bad, "reps": reps, "error_lower": lo, "error_upper": hi})
    out = []
    delta = float(data["delta_target"])
    for (m, h, dec), by_n in sorted(panels.items()):
        if not 0 < delta < 1:
            raise ValueError("invalid target")
        for n, worlds in by_n.items():
            if set(worlds) != set(range(1, m + 1)):
                raise ValueError(("missing world", m, h, dec, n, sorted(worlds)))
        bounds = {n: (max(v[0] for v in ws.values()), max(v[1] for v in ws.values()))
                  for n, ws in by_n.items()}
        bracket = grid_bracket(bounds, delta)
        multiplier = 1 if dec == "safe" else m - 1
        low, high = bracket["grid_min_lower_inclusive"], bracket["certified_upper"]
        out.append({"m": m, "h": h, "decoder": dec, **bracket,
                    "total_lower": None if low is None else multiplier*low,
                    "total_upper": None if high is None else multiplier*high,
                    "worst_world_bounds": [{"N": n, "lower": lo, "upper": hi}
                                           for n, (lo, hi) in sorted(bounds.items())]})
    slopes = []
    for m in sorted({p["m"] for p in out}):
        for dec in ["safe", "identification"]:
            points = [{k: p[k] for k in ["h", "total_lower", "total_upper"]}
                      for p in out if p["m"] == m and p["decoder"] == dec
                      and p["has_data_on_both_sides"]]
            si = slope_interval(points)
            if si is not None:
                predicted = -2 if dec == "safe" else -2*(m-1)
                slopes.append({"m": m, "decoder": dec, **si,
                               "asymptotic_reference_only": predicted,
                               "contains_reference": si["lower"] <= predicted <= si["upper"]})
    return {
        "confidence": confidence, "count_rows": len(rows), "one_sided_endpoints": 2*len(rows),
        "per_tail_error_budget": tail, "delta_target": delta,
        "scope": "simultaneous bounds from saved counts; no observation generation; no error-monotonicity assumption",
        "panels": out, "finite_grid_slope_intervals": slopes, "corrected_rows": corrected,
        "counts": {"certified_upper": sum(p["certified_upper"] is not None for p in out),
                   "with_failed_prefix_and_upper": sum(p["has_data_on_both_sides"] for p in out),
                   "without_certified_upper": sum(p["certified_upper"] is None for p in out)},
    }


def self_test():
    # An isolated failed rung at 40 CANNOT exclude the unclassified rung 20.
    b = grid_bracket({10: (.10, .20), 20: (.01, .08), 40: (.10, .20), 80: (.01, .04)}, .05)
    assert b["failed_prefix"] == [10]
    assert b["grid_min_lower_inclusive"] == 20 and b["certified_upper"] == 80
    b = grid_bracket({10: (.10, .20), 20: (.10, .20), 40: (.01, .04)}, .05)
    assert b["grid_min_lower_inclusive"] == b["certified_upper"] == 40
    b = grid_bracket({10: (.01, .08), 20: (.01, .04)}, .05)
    assert not b["has_data_on_both_sides"]
    assert cp_two_sided(0, 400, .025)[0] == 0
    assert cp_two_sided(400, 400, .025)[1] == 1
    s = slope_interval([{"h": 1, "total_lower": 1, "total_upper": 1},
                        {"h": .5, "total_lower": 4, "total_upper": 4}])
    assert abs(s["lower"]+2) < 1e-12 and abs(s["upper"]+2) < 1e-12


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--input", type=Path)
    ap.add_argument("--out", type=Path)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    self_test()
    if args.self_test and args.input is None:
        print("6 deterministic checks passed; no experiments run")
        return
    if args.input is None or args.out is None:
        ap.error("--input and --out required for reanalysis")
    if args.out.exists():
        raise FileExistsError("choose a fresh output; do not overwrite historical evidence")
    raw = args.input.read_bytes()
    data = json.loads(raw)
    result = analyse(data)
    result.update({"input_path": str(args.input.resolve()), "input_sha256": sha(raw),
                   "input_producer_sha256": data.get("source_sha256"),
                   "analysis_sha256": sha(Path(__file__).read_bytes())})
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("x") as f:
        json.dump(result, f, indent=2, allow_nan=False)
        f.write("\n")
    print(json.dumps(result["counts"]))
    for s in result["finite_grid_slope_intervals"]:
        print(s["m"], s["decoder"], s["lower"], s["upper"])


if __name__ == "__main__":
    main()
