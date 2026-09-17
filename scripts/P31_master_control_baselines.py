#!/usr/bin/env python3
"""P31 -- harness contract E-M: the MASTER calibration baselines.

The contract asks for K = 1,2,4,8; m = 2,4; kappa = 1/4, 2/3, 1, 4; Delta = 1/2, with
the query means, the nuisance and the alternative domain recorded, and FOUR baselines
beside the analytic optimum:

    no controls            -- every z_g = 0
    one control missing    -- z_g = 0 for a single group
    all controls uniform   -- every weight equal, budget-normalised
    analytic optimum       -- Delta^2 / (2 K (sqrt m + sqrt kappa)^2)

and it insists the exact hidden-shift witness is checked BEFORE any solver runs, so
that a positive number from a solver can never stand in for identifiability.

The witness (exact rationals): theta = (1,0,0,1) with offsets (0,0) against
lambda = (1/4,-3/4,0,1) with offsets (3/4,0), items 0,1 in group 0 and 2,3 in group 1.
Every ordinary query mean is (1,0,0,1) in both worlds; the answer {i : theta_i > 1/2}
changes from {0,3} to {3}.  So a group with no calibration query has Gamma = 0, and the
`no controls` and `one control missing` baselines are ZERO by identifiability, not by
a numerical shortfall.
"""
from __future__ import annotations
import argparse, json, math, time
from fractions import Fraction as F
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def hidden_shift_witness():
    grp = [0, 0, 1, 1]
    theta = [F(1), F(0), F(0), F(1)]
    off = [F(0), F(0)]
    lam = [F(1, 4), F(-3, 4), F(0), F(1)]
    off2 = [F(3, 4), F(0)]
    tau = F(1, 2)
    m0 = [theta[i] + off[grp[i]] for i in range(4)]
    m1 = [lam[i] + off2[grp[i]] for i in range(4)]
    a0 = sorted(i for i in range(4) if theta[i] > tau)
    a1 = sorted(i for i in range(4) if lam[i] > tau)
    return {
        "group_of_item": grp,
        "world0": {"theta": [str(x) for x in theta], "offsets": [str(x) for x in off],
                   "ordinary_query_means": [str(x) for x in m0], "answer": a0},
        "world1": {"theta": [str(x) for x in lam], "offsets": [str(x) for x in off2],
                   "ordinary_query_means": [str(x) for x in m1], "answer": a1},
        "means_identical": bool(m0 == m1),
        "answers_differ": bool(a0 != a1),
        "consequence": "a group with no calibration query has Gamma = 0",
    }, (m0 == m1 and a0 != a1)


def group_min_cost(h, m, kap):
    """min over z > h of  m h z/(z-h) + kappa z, by ternary search.  No closed form."""
    lo, hi = h * (1 + 1e-12), h * 1e6 + 1e6
    f = lambda z: m * h * z / (z - h) + kap * z
    for _ in range(400):
        a = lo + (hi - lo) / 3
        b = hi - (hi - lo) / 3
        if f(a) < f(b):
            hi = b
        else:
            lo = a
    return f((lo + hi) / 2)


def numeric_optimum(K, m, kap, Delta):
    lo, hi = 0.0, 1.0
    for _ in range(200):
        V = (lo + hi) / 2
        h = 2 * V / Delta ** 2
        if h <= 0 or K * group_min_cost(h, m, kap) <= 1.0:
            lo = V
        else:
            hi = V
    return lo


def uniform_controls(K, m, kap, Delta):
    """every ordinary weight and every control weight equal, budget K(m x + kappa z)=1."""
    x = 1.0 / (K * (m + kap))
    z = x
    return Delta ** 2 / (2 * (1 / x + 1 / z))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    out = Path(args.out or (REPO / "research/worker_P31_master_baselines_20260915"
                            / "P31_master_control_baselines.json"))
    if out.exists():
        raise SystemExit(f"Refusing to overwrite {out}")
    t0 = time.time()

    wit, wit_ok = hidden_shift_witness()
    print("PART 1 -- identifiability witness, checked BEFORE any solver")
    print(f"   ordinary means identical: {wit['means_identical']};  "
          f"answers {wit['world0']['answer']} vs {wit['world1']['answer']}")
    if not wit_ok:
        raise SystemExit("witness FAILED -- refusing to run the solver")
    print("   => `no controls` and `one control missing` are ZERO by identifiability\n")

    print("PART 2 -- baselines against the analytic optimum")
    rows = []
    Delta = 0.5
    for K in (1, 2, 4, 8):
        for m in (2, 4):
            for kap in (0.25, 2 / 3, 1.0, 4.0):
                closed = Delta ** 2 / (2 * K * (math.sqrt(m) + math.sqrt(kap)) ** 2)
                num = numeric_optimum(K, m, kap, Delta)
                unif = uniform_controls(K, m, kap, Delta)
                rows.append({
                    "K": K, "m": m, "kappa": kap, "Delta": Delta,
                    "alternative_domain": "boundary alternatives theta_i = tau for each "
                                          "item i, with the group offset b_g free and "
                                          "profiled out",
                    "query_means": "Y_i = theta_i + b_{g(i)}; a control on group g "
                                   "observes b_g",
                    "analytic_optimum": closed,
                    "numeric_optimum_bisection": num,
                    "relative_gap_numeric_vs_analytic": abs(num - closed) / closed,
                    "baseline_no_controls": 0.0,
                    "baseline_one_control_missing": 0.0,
                    "baseline_reason_zero": "unidentifiable by the hidden-shift witness, "
                                            "not a numerical shortfall",
                    "baseline_all_controls_uniform": unif,
                    "uniform_over_optimum": unif / closed,
                    "agrees": bool(abs(num - closed) / closed < 2e-6),
                })
                print(f"   K={K} m={m} kappa={kap:<6.4g}  optimum={closed:.8e}  "
                      f"uniform={unif:.8e} ({unif/closed:6.2%} of optimum)  "
                      f"no-control=0  numeric rel={abs(num-closed)/closed:.1e}",
                      flush=True)

    allagree = all(r["agrees"] for r in rows)
    out_obj = {
        "script": "P31_master_control_baselines.py", "contract": "E-M",
        "part1_identifiability_witness": wit,
        "part2_rows": rows, "all_cells_agree_with_closed_form": allagree,
        "worst_uniform_over_optimum": max(r["uniform_over_optimum"] for r in rows),
        "wall_seconds": round(time.time() - t0, 1),
        "not_established": [
            "The zero for `no controls` and `one control missing` is an "
            "IDENTIFIABILITY fact from the exact witness; no solver was consulted and "
            "none could have produced it correctly.",
            "The analytic rate assumes equal variances, equal prices and a common gap.",
            "P6's four-alternative game is a different problem and its V0 = 1/64 must "
            "not be compared with these numbers.",
        ],
        "lean": "LeanMasterCalibrationLawV1 (hidden_shift_witness, group_cost_lower, "
                "calibration_rate_upper, calibration_rate_attained)",
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("x") as f:
        json.dump(out_obj, f, indent=1)
        f.write("\n")
    print(f"\nall cells agree with the closed form: {allagree}")
    print(f"artifact: {out}")


if __name__ == "__main__":
    main()
