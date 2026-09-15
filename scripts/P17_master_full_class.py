#!/usr/bin/env python3
"""P17 -- MASTER: the hidden-shift witness, and the FULL-CLASS calibration rate.

Audit item M1: `P6_master_group_calibration.py` builds four alternatives, each moving
ONE item and pinning every other coordinate.  With theta free in R^4 and both group
offsets free, that is not the alternative class of the threshold problem.  An
alternative may shift a whole group and pay the shift back with the offset: every
ordinary query mean is unchanged and the answer changes.  Part 1 certifies one such
witness in exact rationals.  Consequently a group with NO calibration query has
Gamma = 0, and P6's positive number is the value of a four-alternative game, not the
threshold rate.

Part 2 solves the actual model:

  report {i : theta_i > tau};  Y_i = theta_i + b_{g(i)} + noise (variance 1);
  a control on group g observes b_g (variance 1) at price kappa;
  ordinary queries cost 1.  K groups, m items each, common gap Delta.

Profiling the group shift out of the boundary alternative for item i gives
I_i = Delta^2 / (2(1/x_i + 1/z_g)), and the cost of delivering information h in one
group is at least h(sqrt(m)+sqrt(kappa))^2 by Cauchy-Schwarz, with equality at
z/x = sqrt(m/kappa).  Hence

  Gamma* = Delta^2 / (2 K (sqrt(m) + sqrt(kappa))^2).

Part 2 checks this against a numerical optimum over the full (x, z) space, including
ASYMMETRIC allocations across groups.

Lean counterpart: `LeanMasterCalibrationLawV1` (hidden_shift_witness,
profiled_information, group_cost_lower, group_cost_attained, calibration_rate_upper,
calibration_rate_attained).
"""
import json, os
from fractions import Fraction as F
from math import sqrt
import numpy as np
from scipy.optimize import minimize

OUT = "research/worker_P17_master_20260915"


def part1_witness():
    grp = [0, 0, 1, 1]
    theta = [F(1), F(0), F(0), F(1)]
    off = [F(0), F(0)]
    lam = [F(1, 4), F(-3, 4), F(0), F(1)]
    off2 = [F(3, 4), F(0)]
    tau = F(1, 2)
    means0 = [theta[i] + off[grp[i]] for i in range(4)]
    means1 = [lam[i] + off2[grp[i]] for i in range(4)]
    ans0 = sorted(i for i in range(4) if theta[i] > tau)
    ans1 = sorted(i for i in range(4) if lam[i] > tau)
    assert means0 == means1, (means0, means1)
    assert ans0 != ans1, (ans0, ans1)
    # and the same is true if only the SECOND control is bought: group 0 is still blind
    return {
        "grp": grp,
        "theta": [str(v) for v in theta], "offsets": [str(v) for v in off],
        "lambda": [str(v) for v in lam], "offsets_alt": [str(v) for v in off2],
        "ordinary_means_world0": [str(v) for v in means0],
        "ordinary_means_world1": [str(v) for v in means1],
        "means_identical": True,
        "answer_world0": ans0, "answer_world1": ans1,
        "conclusion": "a group with no calibration query has Gamma = 0",
    }


def group_min_cost(h, m, kap):
    """minimal cost of ONE group delivering profiled information parameter h,
    computed by 1-D minimisation of  m*h*z/(z-h) + kappa*z  over z > h.
    No closed form is used."""
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
    """Bisect on the achievable value V.  Feasibility of V uses only the budget's
    separability across groups and a 1-D minimisation inside each group -- the closed
    form is never used."""
    lo, hi = 0.0, 1.0
    for _ in range(200):
        V = (lo + hi) / 2
        h = 2 * V / Delta ** 2
        if h <= 0:
            lo = V
            continue
        if K * group_min_cost(h, m, kap) <= 1.0:
            lo = V
        else:
            hi = V
    return lo


def nelder_mead_optimum(K, m, kap, Delta):
    """A weaker, structure-free cross-check.  It degrades in dimension 2K and can only
    UNDERSHOOT the optimum, which is what the theorem predicts."""
    def neg(v):
        v = np.abs(v) + 1e-12
        x = v[:K]; z = v[K:]
        tot = (m * x + kap * z).sum()
        x = x / tot; z = z / tot
        return -min(Delta ** 2 / (2 * (1 / x[g] + 1 / z[g])) for g in range(K))
    best = None
    rng = np.random.default_rng(20260915)
    for _ in range(40):
        v0 = rng.random(2 * K) + 0.05
        r = minimize(neg, v0, method="Nelder-Mead",
                     options={"maxiter": 60000, "maxfev": 60000,
                              "xatol": 1e-12, "fatol": 1e-14})
        if best is None or r.fun < best.fun:
            best = r
    return -best.fun


def main():
    os.makedirs(OUT, exist_ok=True)
    w = part1_witness()
    print("PART 1 -- hidden-shift witness")
    print(f"  ordinary means identical: {w['ordinary_means_world0']}")
    print(f"  answers differ: {w['answer_world0']} vs {w['answer_world1']}")
    print("  => a group without a calibration query is blind: Gamma = 0\n")

    print("PART 2 -- the full-class calibration rate")
    rows = []
    for K in [1, 2, 4, 8]:
        for m in [2, 4]:
            for kap in [0.25, 2 / 3, 1.0, 4.0]:
                Delta = 0.5
                closed = Delta ** 2 / (2 * K * (sqrt(m) + sqrt(kap)) ** 2)
                num = numeric_optimum(K, m, kap, Delta)
                nm = nelder_mead_optimum(K, m, kap, Delta)
                rel = abs(num - closed) / closed
                rows.append({
                    "K": K, "m": m, "kappa": kap, "Delta": Delta,
                    "closed_form": closed, "bisection_optimum": num,
                    "nelder_mead_optimum": nm,
                    "relative_gap": rel,
                    "nelder_mead_shortfall": (closed - nm) / closed,
                    "agrees": bool(rel < 2e-6),
                    "nelder_mead_never_exceeds": bool(nm <= closed * (1 + 1e-9)),
                })
                flag = "OK " if rel < 2e-6 else "!! "
                print(f"  {flag}K={K} m={m} kappa={kap:<6.4g} "
                      f"closed={closed:.10f} bisect={num:.10f} rel={rel:.2e} "
                      f"NM_shortfall={(closed-nm)/closed:.2e}")

    agree = all(r["agrees"] for r in rows)
    nm_ok = all(r["nelder_mead_never_exceeds"] for r in rows)
    out = {
        "script": "P17_master_full_class.py",
        "part1_hidden_shift_witness": w,
        "part2_formula": "Gamma* = Delta^2 / (2 K (sqrt(m) + sqrt(kappa))^2)",
        "part2_rows": rows,
        "part2_all_agree": agree,
        "part2_nelder_mead_never_exceeds_closed_form": nm_ok,
        "relation_to_P6": (
            "P6 solves a FOUR-ALTERNATIVE game and reports V0 = 1/64.  That is a "
            "different problem from the full threshold class solved here, and the two "
            "numbers must not be substituted for one another."
        ),
        "relation_to_other_master_results": (
            "The symmetric-family price threshold c* = (m-1)^2/(m+3)^2 "
            "(LeanMasterAnchorThresholdV1) and the finite three-alternative "
            "mandatory-anchor certificate U0 < L1 at c0 = 1/10 (P12) are two further "
            "distinct problems.  None of the three implies another."
        ),
        "not_established": [
            "Heterogeneous variances, unequal prices and unequal gaps are not covered.",
            "The bisection optimum uses the budget's separability across groups and a "
            "1-D minimisation inside a group; it CONFIRMS the closed form, it does not "
            "certify it.  The proof is LeanMasterCalibrationLaw.group_cost_lower plus "
            "calibration_rate_upper/attained.",
            "The Nelder-Mead column is a structure-free cross-check.  It degrades in "
            "dimension 2K and UNDERSHOOTS at K = 4, 8; it never exceeds the closed "
            "form, which is the direction the theorem predicts.  Its shortfall is "
            "optimiser error, not evidence against the formula.",
        ],
        "lean": "LeanMasterCalibrationLawV1",
    }
    path = os.path.join(OUT, "P17_master_full_class.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nall cells agree with the closed form: {agree}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
