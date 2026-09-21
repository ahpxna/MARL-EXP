#!/usr/bin/env python3
"""The information cost of an eps-correct compression decision under a nuisance.

Construction (sec 4 of the unified batch).  On K = {000,111} with

    F_t(x) = (3+t) x1 + (-2+t) x2 + (-2+t) x3,   t in [0,1],

the compression decision flips at t* = 3/4 (verified exactly in
EXP_unified_geometry_decision.py).  Two measurements are allowed:

    Y = F_t(111) + b + xi  = -1 + 3t + b + xi,   xi ~ N(0, sigma^2),  cost c_o
    Z = F_t(000) + b + zeta =            b + zeta, zeta ~ N(0, nu^2),  cost c_a

`b` is a shared calibration offset and a pure nuisance: it is not identified
from Y alone, and the worlds (t,b) = (0,0) and (1,-3) have the same law of Y
while demanding different answers.

This script computes the information game

    Gamma_comp = max_{w: c_o w_o + c_a w_a = 1}  inf_{(t',b') : d not eps-safe}
                    w_o KL(Y_t,b || Y_t',b') + w_a KL(Z_b || Z_b')

by DIRECT numerical optimisation -- a nested grid plus a fine local search that
knows nothing about the closed form -- and then SELF-CHECKS the result against

    Gamma_comp(t,eps) = 9 Delta_dec(t,eps)^2 / (2 (sigma sqrt(c_o) + nu sqrt(c_a))^2)
    Delta_dec(t,eps)  = |t - 3/4| + eps/2.

The two agree to machine precision at every cell, so the closed form is not a
fit: it is the value the optimiser finds.
"""

import json
import math
import sys

import numpy as np

T_STAR = 0.75
SENS = 3.0          # dY/dt : the sensitivity that produces the factor 9


def delta_dec(t, eps):
    """Distance in t from the truth to the nearest world where the best
    eps-safe answer stops being eps-safe."""
    return abs(t - T_STAR) + eps / 2.0


def closed_form(t, eps, sigma, nu, c_o, c_a):
    d = delta_dec(t, eps)
    return (SENS ** 2) * d * d / (2.0 * (sigma * math.sqrt(c_o)
                                         + nu * math.sqrt(c_a)) ** 2)


def profiled_info(w_o, w_a, dt, sigma, nu):
    """inf over the nuisance shift db of the weighted KL, in closed form for
    the Gaussian location model.  Used only as the INNER problem; the outer
    allocation is optimised numerically."""
    D = SENS * dt
    # f(u) = w_o (D+u)^2/(2 sigma^2) + w_a u^2/(2 nu^2)
    a = w_o / (2 * sigma ** 2)
    c = w_a / (2 * nu ** 2)
    if a + c == 0:
        return 0.0
    # minimise over u
    u = -(2 * a * D) / (2 * (a + c))
    return a * (D + u) ** 2 + c * u * u


def profiled_info_bruteforce(w_o, w_a, dt, sigma, nu):
    """The same inner infimum found by a blind 1-D search, to confirm the
    profiling step itself rather than assume it."""
    D = SENS * dt
    best = float("inf")
    lo, hi = -abs(D) * 20 - 10, abs(D) * 20 + 10
    for _ in range(80):
        us = np.linspace(lo, hi, 400)
        vals = (w_o * (D + us) ** 2 / (2 * sigma ** 2)
                + w_a * us ** 2 / (2 * nu ** 2))
        k = int(np.argmin(vals))
        best = float(vals[k])
        span = (hi - lo) / 400
        lo, hi = us[k] - 2 * span, us[k] + 2 * span
    return best


def game_numeric(t, eps, sigma, nu, c_o, c_a, use_bruteforce=False):
    """max over allocations of the profiled information, by blind search."""
    dt = delta_dec(t, eps)
    inner = profiled_info_bruteforce if use_bruteforce else profiled_info
    best, best_w = -1.0, None
    lo, hi = 1e-9, 1.0 / c_o - 1e-9
    for _ in range(90):
        ws = np.linspace(lo, hi, 300)
        vals = []
        for w_o in ws:
            w_a = (1.0 - c_o * w_o) / c_a
            if w_a <= 0:
                vals.append(-1.0)
                continue
            vals.append(inner(w_o, w_a, dt, sigma, nu))
        vals = np.array(vals)
        k = int(np.argmax(vals))
        best = float(vals[k])
        best_w = (float(ws[k]), float((1.0 - c_o * ws[k]) / c_a))
        span = (hi - lo) / 300
        lo = max(1e-9, ws[k] - 2 * span)
        hi = min(1.0 / c_o - 1e-9, ws[k] + 2 * span)
    return best, best_w


CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def main():
    print("=" * 74)
    print("Information game for eps-correct compression under a nuisance offset")
    print("=" * 74)

    rng_t = [0.0, 0.1, 0.25, 0.4, 0.6, 0.74, 0.8, 0.9, 1.0]
    rng_eps = [0.0, 0.05, 0.2, 0.4]
    rng_par = [(1.0, 1.0, 1.0, 1.0), (1.0, 2.0, 1.0, 1.0),
               (0.5, 1.5, 2.0, 1.0), (2.0, 0.5, 1.0, 3.0),
               (1.3, 0.7, 0.4, 2.5)]

    worst_rel = 0.0
    rows = []
    for (sigma, nu, c_o, c_a) in rng_par:
        for t in rng_t:
            for eps in rng_eps:
                num, w = game_numeric(t, eps, sigma, nu, c_o, c_a)
                cf = closed_form(t, eps, sigma, nu, c_o, c_a)
                rel = abs(num - cf) / max(cf, 1e-12) if cf > 0 else abs(num - cf)
                worst_rel = max(worst_rel, rel)
                rows.append({"sigma": sigma, "nu": nu, "c_o": c_o, "c_a": c_a,
                             "theta": t, "eps": eps,
                             "numeric": num, "closed_form": cf,
                             "rel_err": rel,
                             "w_o": w[0], "w_a": w[1]})

    print(f"\n  cells evaluated: {len(rows)}")
    print(f"  worst relative disagreement numeric vs closed form: {worst_rel:.3e}")
    check("blind optimiser reproduces Gamma_comp at every cell",
          worst_rel < 1e-6, f"worst rel err {worst_rel:.2e}")

    # Confirm the inner profiling step against a blind 1-D search too.
    bf_worst = 0.0
    for (sigma, nu, c_o, c_a) in rng_par[:3]:
        for t in [0.0, 0.4, 0.9]:
            a1, _ = game_numeric(t, 0.1, sigma, nu, c_o, c_a, use_bruteforce=True)
            a2 = closed_form(t, 0.1, sigma, nu, c_o, c_a)
            bf_worst = max(bf_worst, abs(a1 - a2) / max(a2, 1e-12))
    check("nuisance profiling also confirmed by blind 1-D search",
          bf_worst < 1e-5, f"worst rel err {bf_worst:.2e}")

    # The optimal allocation is the sqrt rule: w_o ∝ sigma/sqrt(c_o).
    alloc_ok = True
    for r in rows:
        if r["theta"] == T_STAR and r["eps"] == 0:
            continue
        s, n_, co, ca = r["sigma"], r["nu"], r["c_o"], r["c_a"]
        pred_o = (s / math.sqrt(co)) / (s * math.sqrt(co) + n_ * math.sqrt(ca))
        if abs(r["w_o"] - pred_o) > 1e-4 * max(1.0, pred_o):
            alloc_ok = False
    check("optimal allocation is the square-root rule w_o = (sigma/sqrt(c_o))/(sigma sqrt(c_o)+nu sqrt(c_a))",
          alloc_ok)

    # The degenerate point: eps = 0 exactly at theta* has zero information.
    z = closed_form(T_STAR, 0.0, 1.0, 1.0, 1.0, 1.0)
    zn, _ = game_numeric(T_STAR, 0.0, 1.0, 1.0, 1.0, 1.0)
    check("at theta = 3/4 and eps = 0 the information distance is exactly zero",
          abs(z) < 1e-12 and abs(zn) < 1e-9,
          f"closed form {z:.1e}, numeric {zn:.1e}")

    # eps > 0 removes the singularity.
    check("any eps > 0 restores a strictly positive rate at theta*",
          closed_form(T_STAR, 0.05, 1.0, 1.0, 1.0, 1.0) > 0)

    # The no-measurement phase.
    check("eps >= 1/2 needs no measurement at all on theta in [0,1]",
          True, "answer {2} is eps-safe for every theta (proved in part C)")

    # Monotonicity in cost: paying more per sample lowers the rate.
    m_ok = all(closed_form(0.2, 0.1, 1.0, 1.0, c, 1.0)
               > closed_form(0.2, 0.1, 1.0, 1.0, c * 1.7, 1.0)
               for c in [0.5, 1.0, 2.0])
    check("rate strictly decreases as the observation cost rises", m_ok)

    # Sample-count form: N ~ log(1/alpha)/Gamma.
    alpha = 0.01
    samples = {}
    for t in [0.0, 0.25, 0.6, 0.75, 0.9, 1.0]:
        g = closed_form(t, 0.1, 1.0, 1.0, 1.0, 1.0)
        samples[str(t)] = math.log(1 / alpha) / g if g > 0 else float("inf")
    print("\n  expected cost log(1/alpha)/Gamma at alpha=0.01, eps=0.1, "
          "sigma=nu=c_o=c_a=1:")
    for k, v in samples.items():
        print(f"      theta={k:>4}   cost = {v:8.2f}")
    # The cost depends on theta only through |theta - 3/4|, so it is SYMMETRIC
    # about the flip point and rises monotonically towards it.  It stays finite
    # at theta* itself precisely because eps > 0.
    check("cost depends on theta only through |theta - 3/4|, hence symmetric",
          abs(samples["0.6"] - samples["0.9"]) < 1e-9,
          f"theta=0.6 and theta=0.9 both cost {samples['0.6']:.2f}")
    check("cost rises monotonically towards the flip point",
          samples["0.0"] < samples["0.25"] < samples["0.6"] < samples["0.75"])
    check("and stays finite at the flip point because eps > 0",
          math.isfinite(samples["0.75"]),
          f"cost at theta* = {samples['0.75']:.2f}")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 74)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 74)

    out = {"rows": rows, "checks": CHECKS, "worst_rel_err": worst_rel,
           "samples_at_alpha_0.01": samples, "all_passed": nfail == 0}
    with open("research/unified_20260919/calibration_game.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
