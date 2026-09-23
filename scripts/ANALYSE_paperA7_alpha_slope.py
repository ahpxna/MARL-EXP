#!/usr/bin/env python3
"""Paper A7: the alpha axis, read as a SLOPE rather than as four levels.

WHY A SEPARATE SCRIPT.  `EXP_paperA7_learner.py` produces the panel; this reads it.  The
panel's own self-check states that the panel cannot test `E tau ~ log(1/alpha)/Gamma`, and
that is right about the LEVELS: the threshold is

    b(alpha) = log(1/alpha) + (1/2) sum_e log(1 + N_e/a),

and the second term measures ~19.7 here against `log(1/alpha) <= 4.61`, so no level can be
compared with `log(1/alpha)/Gamma`.  The SLOPE is a different quantity.  An additive,
alpha-independent penalty cancels in `d E tau / d log(1/alpha)`, so the slope is testable on
exactly the panel the levels are not.

WHAT MAKES THE SLOPE READABLE AT ALL.  Common random numbers.  `alpha` enters the algorithm
only at the stopping test, so with a seed free of alpha the four alphas are the SAME path
and `tau` is monotone in alpha pathwise.  Differencing along a path removes the run-to-run
variation that swamped an earlier, independently-seeded panel -- in that panel the cell
means were not even monotone in alpha, which was at one point misread as an effect of the
penalty.  This script REFUSES to run on a panel that is not under common random numbers.

WHAT THE SLOPE DOES AND DOES NOT ESTIMATE, STATED HONESTLY.  Write the stopping identity as

    Z_tau = Gamma * tau + R_tau,        Z_tau = log(1/alpha) + b_tau + O_alpha,

with `b_tau` the regularisation penalty, `O_alpha` the OVERSHOOT past the threshold at the
crossing, and `R_tau` the finite-time information residual (the gap between the accumulated
statistic and its asymptotic rate).  Taking expectations,

    Gamma * E[tau] = log(1/alpha) + E[b_tau] + E[O_alpha] - E[R_tau].

Differencing along the alpha axis therefore removes the CONSTANT part of the penalty, and
this script also measures and removes the penalty's DRIFT.  It does **not** remove
`E[O_alpha]` or `E[R_tau]`, and neither is bounded anywhere in this corpus.  Both vary with
alpha in an uncontrolled way.

Consequently the comparison below is a **heuristic diagnostic**, not an upper bound on
`1/Gamma` and not an independent test of the rate.  An earlier version of this file called
the drift-corrected figure an "upper estimate of 1/Gamma"; that was wrong, because the two
unbounded terms can push the slope in either direction.  What the number is good for is
noticing gross disagreement; agreement, as found here, is consistent with the rate theorem
and establishes nothing on its own.  The rate claim rests on the theorem.
"""

import hashlib
import json
import pathlib
import sys

import numpy as np

ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC = ROOT / "research/unified_20260919/paperA7_learner.json"
OUT = ROOT / "research/unified_20260919/paperA7_alpha_slope.json"

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def sha(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()


def ols(x, y):
    """Slope, intercept and the slope's standard error, by least squares."""
    x, y = np.asarray(x, float), np.asarray(y, float)
    n = x.size
    xm, ym = x.mean(), y.mean()
    sxx = ((x - xm) ** 2).sum()
    slope = ((x - xm) * (y - ym)).sum() / sxx
    inter = ym - slope * xm
    if n > 2:
        resid = y - (inter + slope * x)
        s2 = (resid ** 2).sum() / (n - 2)
        se = float(np.sqrt(s2 / sxx))
    else:
        se = float("nan")
    return float(slope), float(inter), se


def main():
    print("=" * 78)
    print("Paper A7: the alpha axis as a slope")
    print("=" * 78)
    d = json.loads(SRC.read_text())

    scope = d.get("panel_scope")
    if scope is None:
        print("REFUSING: the panel carries no `panel_scope`; it predates the coupling.")
        return 1
    if not check("the panel is under COMMON RANDOM NUMBERS -- without it the four alphas"
                 " sit on independent paths and a slope along the alpha axis is not"
                 " identified from 12 runs per cell",
                 scope.get("common_random_numbers") is True,
                 f"seed recipe: {scope.get('seed_recipe')}"):
        print("REFUSING to report a slope on an independently-seeded panel.")
        return 1

    rows = d["rows"]
    alphas = [r["alpha"] for r in rows]
    L = np.log(1.0 / np.array(alphas, float))
    arms = ("learner", "oracle", "uniform")

    # ---- pathwise slopes: the four alphas of one (arm, run) share a path -------
    by_path, per_arm = {}, {}
    for r in rows:
        for arm in arms:
            for ix, rn in enumerate(r["arms"][arm]["runs"]):
                by_path.setdefault((arm, ix), {})[r["alpha"]] = rn["tau"]

    mono_viol = []
    for (arm, ix), m in by_path.items():
        taus = [m[a] for a in sorted(m, reverse=True)]     # alpha descending
        if any(b < a for a, b in zip(taus, taus[1:])):
            mono_viol.append((arm, ix, taus))
    check("tau is non-increasing in alpha on EVERY path, re-derived here from the stored"
          " runs rather than taken from the producing script.  This is what makes the"
          " within-path difference a clean estimate of the slope",
          not mono_viol,
          f"{len(by_path)} paths, {len(mono_viol)} violations")

    print("\n  per-path slope of tau against log(1/alpha)")
    print("  " + "-" * 74)
    for arm in arms:
        slopes = []
        for (a, ix), m in by_path.items():
            if a != arm:
                continue
            xs = np.log(1.0 / np.array(sorted(m), float))
            ys = np.array([m[k] for k in sorted(m)], float)
            slopes.append(ols(xs, ys)[0])
        slopes = np.array(slopes, float)
        cell_means = [np.mean([rn["tau"] for rn in r["arms"][arm]["runs"]]) for r in rows]
        ps, pi, pse = ols(L, cell_means)
        per_arm[arm] = {
            "path_slopes": slopes.tolist(),
            "slope_mean": float(slopes.mean()),
            "slope_sem": float(slopes.std(ddof=1) / np.sqrt(slopes.size)),
            "slope_ci95": [float(slopes.mean() - 1.96 * slopes.std(ddof=1) / np.sqrt(slopes.size)),
                           float(slopes.mean() + 1.96 * slopes.std(ddof=1) / np.sqrt(slopes.size))],
            "pooled_slope": ps, "pooled_intercept": pi, "pooled_slope_se": pse,
            "cell_means": [float(c) for c in cell_means],
        }
        s = per_arm[arm]
        print(f"      {arm:8s} slope = {s['slope_mean']:7.2f} +/- {s['slope_sem']:5.2f}"
              f"   95% CI [{s['slope_ci95'][0]:7.2f}, {s['slope_ci95'][1]:7.2f}]"
              f"   pooled {ps:7.2f}, intercept {pi:8.1f}")

    # ---- the drift in the penalty, which the slope also picks up ---------------
    thr = scope.get("threshold_decomposition", {})
    pen = {float(k): v["penalty_mean"] for k, v in thr.items()} if thr else {}
    drift = None
    if len(pen) >= 2:
        xs = np.log(1.0 / np.array(sorted(pen), float))
        ys = np.array([pen[k] for k in sorted(pen)], float)
        drift = ols(xs, ys)[0]
        print(f"\n      the regularisation penalty itself drifts at {drift:+.3f} per unit"
              f" log(1/alpha)")
        print(f"      (it depends on the counts at stopping, so it is not alpha-free)")

    gl, gu = d["Gamma_comp_lower"], d["Gamma_comp_upper"]
    inv_lo, inv_hi = 1.0 / gu, 1.0 / gl
    s = per_arm["learner"]
    predicted = None
    if drift is not None:
        predicted = [inv_lo * (1.0 + drift), inv_hi * (1.0 + drift)]

    print(f"\n      1/Gamma_comp bracket          [{inv_lo:.2f}, {inv_hi:.2f}]")
    if predicted:
        print(f"      predicted slope, drift incl.  [{predicted[0]:.2f}, {predicted[1]:.2f}]")
    print(f"      measured learner slope        {s['slope_mean']:.2f}"
          f" +/- {s['slope_sem']:.2f}")

    covered = predicted is not None and (
        s["slope_ci95"][0] <= predicted[1] and s["slope_ci95"][1] >= predicted[0])
    ratio = s["slope_mean"] / inv_hi
    check("the slope is REPORTED against the prediction as a HEURISTIC DIAGNOSTIC, and the"
          " comparison is recorded whichever way it falls.  It is not an upper bound on"
          " 1/Gamma and not an independent test of the rate: differencing removes the"
          " penalty's constant part and (measured) its drift, but NOT the threshold"
          " overshoot or the finite-time information residual, neither of which is bounded"
          " anywhere in this corpus",
          np.isfinite(s["slope_mean"]) and np.isfinite(s["slope_sem"]) and predicted is not None,
          f"measured {s['slope_mean']:.2f} against predicted"
          f" [{predicted[0]:.2f}, {predicted[1]:.2f}]:"
          f" {'CI overlaps' if covered else 'CI does NOT overlap'};"
          f" measured/1Gamma = {ratio:.3f}")

    check("the LEVELS remain untestable and are not used: only differences along a path"
          " enter the slope, so the additive penalty (~19.7, i.e. 4.3x the largest"
          " log(1/alpha)) cancels.  This does not rehabilitate the levels",
          len(pen) == 0 or min(pen.values()) > 2.0 * float(max(np.log(1.0 / np.array(list(pen), float)))),
          f"penalty {min(pen.values()):.1f}-{max(pen.values()):.1f}"
          if pen else "no decomposition stored")

    out = {
        "source_sha256": sha(__file__),
        "dependency_sha256": {"paperA7_learner.json": sha(SRC)},
        "depends_on_panel_scope": {k: scope[k] for k in
                                   ("common_random_numbers", "seed_recipe", "M", "scale",
                                    "runs_per_cell", "worlds")
                                   if k in scope},
        "alphas": alphas,
        "log_inv_alpha": L.tolist(),
        "per_arm": per_arm,
        "penalty_by_alpha": pen,
        "penalty_drift_per_log_unit": drift,
        "Gamma_comp_bracket": [gl, gu],
        "inv_Gamma_comp_bracket": [inv_lo, inv_hi],
        "predicted_slope_with_drift": predicted,
        "measured_over_inv_Gamma": ratio,
        "ci_overlaps_prediction": bool(covered),
        "what_this_is_not": "A HEURISTIC DIAGNOSTIC at one world. Differencing along the"
                            " alpha axis removes the penalty's constant part and its"
                            " measured drift, but NOT the threshold overshoot O_alpha nor"
                            " the finite-time information residual R_tau; neither is bounded"
                            " in this corpus, and either can move the slope in either"
                            " direction. So this is not an upper bound on 1/Gamma and not an"
                            " independent test of the rate. The four-point baseline in"
                            " log(1/alpha) spans only 2.30 to 4.61, and the LEVELS are not"
                            " testable on this panel at all.",
        "unbounded_terms_not_removed": ["threshold overshoot O_alpha",
                                        "finite-time information residual R_tau"],
        "checks": CHECKS,
        "all_passed": all(c["ok"] for c in CHECKS),
    }
    OUT.write_text(json.dumps(out, indent=1))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed")
    print(f"  artifact: {OUT.relative_to(ROOT)}")
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
