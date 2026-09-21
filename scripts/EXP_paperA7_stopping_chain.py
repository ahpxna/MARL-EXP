#!/usr/bin/env python3
"""Paper A7: the stopping chain and the alpha-dependent grid, against their theorems.

Two things closed recently, and this script is the falsification test for both.

(1) THE PRIOR.  `fixed_grid_rate_negative` says a mixture over a grid whose mesh does NOT
move misses the exponent: with smallest non-zero tilt d and true gap 0 < Delta < d/2, every
non-zero grid tilt has rate u Delta - u^2/2 < 0 while the information is Delta^2/2 > 0.
`tiltRate_eq` says why that is the whole story:

    u Delta - u^2/2  =  Delta^2/2 - (u - Delta)^2/2,

so the loss is the SQUARED miss and a mesh-m grid gives up only m^2/2.  `grid_penalty_
negligible` says the price of the extra grid points, log(2 B L + 1) against L = log(1/alpha),
can be made arbitrarily small.  All three are checked here.

(2) THE STOPPING CHAIN, Steps 5-8.  `good_window_accumulation` gives

    Z_t/t  >=  G - 2 Gamma n/t - C/t     on a window on which the confidence holds,

`stopping_subset_window_failure` turns that into the event inclusion the union bound needs
-- DERIVED, not assumed -- `sqrt_window_admissible` and `window_bound_decays` give the
t^{-3/2} tail at n = ceil(sqrt t), `sqrt_tail_sum_le` sums it by its own telescoping, and
`expected_stopping_bound_at_level` gives E tau <= log(1/alpha)/Gamma + 19.

The accumulation and the inclusion are checked by SIMULATING the deterministic chain: a
window is drawn, the increments are drawn subject only to the hypotheses, and the script
asserts the conclusion at every draw.  A single counterexample would falsify the theorem.

SCOPE.  Every statement checked is a theorem, so a failure means a defect in the
formalisation or in this transcription.  Nothing here is evidence for an open claim: the
one input the chain still needs -- the per-step confidence guarantee Pr(fails at s) <= s^-4
for the algorithm's own statistic -- is NOT simulated, and this script does not pretend to.
"""

import hashlib
import json
import math
import pathlib
import sys

import numpy as np

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(("  PASS  " if ok else "  FAIL  ") + name)
    if detail:
        print("        " + detail)


def tilt_rate(u, d):
    return u * d - u ** 2 / 2.0


def grid_point(m, delta):
    return m * math.floor(delta / m)


def main():
    smoke = "--smoke" in sys.argv
    rng = np.random.default_rng(20260921)
    ntrial = 300 if smoke else 20000

    print("=" * 78)
    print("Paper A7: the stopping chain and the alpha-dependent grid")
    print("=" * 78)

    # ---- (1) the prior --------------------------------------------------------
    ids = []
    for _ in range(ntrial):
        u, d = rng.uniform(-4, 4), rng.uniform(-4, 4)
        ids.append(abs(tilt_rate(u, d) - (d ** 2 / 2.0 - (u - d) ** 2 / 2.0)))
    check("`tiltRate_eq`: u Delta - u^2/2 = Delta^2/2 - (u-Delta)^2/2, so the rate is the "
          "information minus the SQUARED miss",
          max(ids) < 1e-12, f"max |lhs - rhs| = {max(ids):.3e}")

    neg_ok, neg_worst = True, -np.inf
    for _ in range(ntrial):
        d = rng.uniform(0.2, 4.0)
        delta = rng.uniform(1e-6, d / 2.0 - 1e-9)
        u = rng.choice([1.0, -1.0]) * rng.uniform(d, 8.0)
        r = tilt_rate(u, delta)
        neg_ok &= r < 0
        neg_worst = max(neg_worst, r)
    check("`fixed_grid_rate_negative`: with a FIXED mesh, every non-zero grid tilt has "
          "negative rate once the gap drops below d/2, while the information stays "
          "strictly positive",
          neg_ok, f"worst (largest) rate over {ntrial} draws = {neg_worst:.3e} (must be < 0)")

    mesh_ok, mesh_worst = True, 0.0
    for _ in range(ntrial):
        delta = rng.uniform(-4.0, 4.0)
        m = rng.uniform(1e-4, 1.0)
        u = grid_point(m, delta)
        mesh_ok &= abs(u - delta) <= m + 1e-12
        lhs = delta ** 2 / 2.0 - m ** 2 / 2.0
        mesh_ok &= lhs <= tilt_rate(u, delta) + 1e-12
        mesh_worst = max(mesh_worst, lhs - tilt_rate(u, delta))
    check("`gridPoint_close` and `mesh_grid_rate_ge`: the mesh-m grid point is within m of "
          "the truth and its rate is at least Delta^2/2 - m^2/2, so the loss is second "
          "order in the mesh",
          mesh_ok, f"worst violation = {mesh_worst:.3e} (must be <= 0)")

    eps_rows = []
    pen_ok = True
    for eps in ([0.5] if smoke else [0.5, 0.2, 0.05, 0.01]):
        B = 3.0
        L0 = max(1.0, 2 * math.log(3 * B) / eps, 16 / eps ** 2)
        worst = max(math.log(2 * B * L + 1) / L
                    for L in np.linspace(L0, L0 * 50, 400))
        pen_ok &= worst <= eps + 1e-12
        eps_rows.append({"eps": eps, "L0": L0, "worst_ratio": worst})
    check("`grid_penalty_negligible`: log(2 B L + 1)/L <= eps for every L >= L0(eps), so "
          "the grid's own penalty is of smaller order than L = log(1/alpha)",
          pen_ok,
          "; ".join(f"eps={r['eps']}: L0={r['L0']:.1f}, worst={r['worst_ratio']:.4f}"
                    for r in eps_rows))

    # ---- (2) Steps 5-8 --------------------------------------------------------
    acc_ok, acc_worst = True, 0.0
    for _ in range(ntrial):
        t = int(rng.integers(1, 400))
        n = int(rng.integers(0, t + 1))
        Gamma = rng.uniform(0.0, 3.0)
        G = rng.uniform(-3.0, Gamma) if Gamma > -3.0 else -3.0
        C = rng.uniform(0.0, 5.0)
        z = np.empty(t)
        if n > 0:
            z[:n] = -Gamma + rng.exponential(1.0, size=n)      # only -Gamma <= z_s
        if t > n:
            z[n:] = G + rng.exponential(1.0, size=t - n)       # only G <= z_s
        Zt = float(z.sum()) - C + rng.exponential(1.0)          # only sum - C <= Zt
        lhs = G - 2 * Gamma * n / t - C / t
        acc_ok &= lhs <= Zt / t + 1e-9
        acc_worst = max(acc_worst, lhs - Zt / t)
    check("`good_window_accumulation`: Z_t/t >= G - 2 Gamma n/t - C/t, under nothing but "
          "the head bound -Gamma <= z_s, the window bound G <= z_s and sum z - C <= Z_t",
          acc_ok, f"worst violation over {ntrial} draws = {acc_worst:.3e} (must be <= 0)")

    # the derived inclusion: if every window event holds, the rule has stopped by t
    incl_ok = True
    for _ in range(ntrial // 4):
        t = int(rng.integers(2, 300))
        n = int(rng.integers(0, t + 1))
        Gamma = rng.uniform(0.1, 3.0)
        G = rng.uniform(-1.0, Gamma)
        C = rng.uniform(0.0, 5.0)
        z = np.concatenate([-Gamma + rng.exponential(1.0, size=n),
                            G + rng.exponential(1.0, size=t - n)])
        Zt = float(z.sum()) - C
        thr = G * t - 2 * Gamma * n - C - rng.exponential(1.0)   # thr < G t - 2 Gamma n - C
        incl_ok &= (thr < Zt)      # so the rule fires at t, i.e. tau <= t
    check("`stopping_subset_window_failure`: when every confidence event on the window "
          "holds and the threshold sits below G t - 2 Gamma n - C, the statistic HAS "
          "crossed it -- so {tau > t} is contained in the window's failures, derived",
          incl_ok, f"{ntrial // 4} draws, no draw left the rule un-fired")

    win_ok, tail_rows = True, []
    for t in ([16, 64] if smoke else [16, 32, 64, 128, 256, 1024, 4096]):
        n = math.ceil(math.sqrt(t))
        a1 = 2 <= n
        a2 = n <= t
        a3 = math.sqrt(t) / 2 <= n - 1
        b = 1.0 / (n - 1) ** 3
        c = 8.0 / math.sqrt(t) ** 3
        win_ok &= a1 and a2 and a3 and (b <= c + 1e-15)
        tail_rows.append({"t": t, "n": n, "window_bound": b, "t_pow": c})
    check("`sqrt_window_admissible` and `window_bound_decays`: n = ceil(sqrt t) is a legal "
          "window for t >= 16, and 1/(n-1)^3 <= 8 t^{-3/2}",
          win_ok,
          "; ".join(f"t={r['t']}: {r['window_bound']:.3e} <= {r['t_pow']:.3e}"
                    for r in tail_rows[:4]))

    tel_ok, tel_worst = True, 0.0
    for n in ([2, 8] if smoke else [2, 3, 8, 50, 500]):
        for M in [n, n + 1, n + 37, n + 5000]:
            s = sum(8.0 / math.sqrt(t) ** 3 for t in range(n, M))
            bd = 16.0 / math.sqrt(n - 1)
            tel_ok &= s <= bd + 1e-12
            tel_worst = max(tel_worst, s / bd)
    check("`sqrt_tail_sum_le`: sum_{t in [n,M)} 8 t^{-3/2} <= 16/sqrt(n-1), by the "
          "telescoping 1/sqrt(t-1) - 1/sqrt t = 1/(sqrt(t-1) sqrt t (sqrt(t-1)+sqrt t))",
          tel_ok, f"worst ratio sum/bound = {tel_worst:.4f} (must be <= 1)")

    exp_ok, exp_worst = True, 0.0
    for _ in range(ntrial // 4):
        Gamma = rng.uniform(0.05, 3.0)
        alpha = float(np.exp(-rng.uniform(0.01, 25.0)))
        L = math.log(1.0 / alpha)
        t0 = math.ceil(L / Gamma) + 2
        M = t0 + int(rng.integers(0, 4000))
        Esum = t0 + sum(8.0 / math.sqrt(t) ** 3 for t in range(t0, M))
        bound = L / Gamma + 19.0
        exp_ok &= Esum <= bound + 1e-9
        exp_worst = max(exp_worst, Esum - bound)
    check("`expected_stopping_bound_at_level`: with t0 = ceil(log(1/alpha)/Gamma) + 2 and "
          "the t^{-3/2} tail, E tau <= log(1/alpha)/Gamma + 19 -- an explicit constant, "
          "not an asymptotic one",
          exp_ok, f"worst violation = {exp_worst:.3e} (must be <= 0)")

    ratio_rows, ratio_ok = [], True
    for Gamma in ([0.5] if smoke else [0.2, 0.5, 1.0, 2.0]):
        for eps in [0.1, 0.01]:
            # `ratio_eventually_le` picks L >= C/eps + 1 with C = 19; transcribe that
            # threshold exactly rather than inventing one, and test AT it and beyond.
            L0 = max(19.0 / eps + 1.0, 2.0)
            for L in [L0, 2 * L0, 37 * L0]:
                alpha = math.exp(-L)
                Etau = L / Gamma + 19.0
                r = Etau / L
                ratio_ok &= r <= 1.0 / Gamma + eps + 1e-12
                ratio_rows.append({"Gamma": Gamma, "eps": eps, "L": L, "alpha": alpha,
                                   "ratio": r, "target": 1.0 / Gamma + eps})
    check("`a7_rate_limsup`: E tau / log(1/alpha) is within eps of 1/Gamma once alpha is "
          "small enough, i.e. the limsup is at most 1/Gamma",
          ratio_ok,
          f"{len(ratio_rows)} (Gamma, eps, L) points, worst margin "
          f"{max(r['ratio'] - r['target'] for r in ratio_rows):.3e} (must be <= 0); "
          + "; ".join(f"G={r['Gamma']}, eps={r['eps']}: {r['ratio']:.4f}"
                      f" <= {r['target']:.4f}" for r in ratio_rows[:3]))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    print("\n  SCOPE.  Every statement checked is a theorem in LeanPaperA7StreamV1 or")
    print("  LeanPaperA7TailV1, so a failure would indicate a defect, not an open")
    print("  question.  The one input the chain still needs -- the per-step confidence")
    print("  guarantee Pr(fails at s) <= s^-4 for the algorithm's own statistic -- is NOT")
    print("  simulated here, and the chain remains conditional on it.")

    # the rate curve, so the figure plots computed values and not a formula
    d_true, d_mesh, d_fixed = 0.30, 0.05, 1.00
    us = np.linspace(-1.2, 1.6, 401)
    curve = {"u": us.tolist(),
             "rate": [tilt_rate(u, d_true) for u in us],
             "delta": d_true, "info": d_true ** 2 / 2.0,
             "fixed_grid": [u for u in np.arange(-3, 3.0001, d_fixed) if u != 0.0],
             "fixed_rate": [tilt_rate(u, d_true)
                            for u in np.arange(-3, 3.0001, d_fixed) if u != 0.0],
             "mesh": d_mesh,
             "mesh_point": grid_point(d_mesh, d_true),
             "mesh_rate": tilt_rate(grid_point(d_mesh, d_true), d_true),
             "mesh_floor": d_true ** 2 / 2.0 - d_mesh ** 2 / 2.0}

    out = {"trials": ntrial, "smoke": bool(smoke), "curve": curve,
           "grid_penalty": eps_rows, "window": tail_rows, "ratio": ratio_rows,
           "scope": "transcription of the proved grid and stopping chain; the per-step"
                    " confidence guarantee is NOT simulated and the chain stays"
                    " conditional on it",
           "source_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperA7_stopping_chain.py").read_bytes()
           ).hexdigest(),
           "checks": CHECKS, "all_passed": nfail == 0}
    dest = ("research/unified_20260919/paperA7_stopping_chain"
            + ("_smoke" if smoke else "") + ".json")
    with open(dest, "w") as f:
        json.dump(out, f, indent=2)
    print(f"\n  artifact: {dest}")
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
