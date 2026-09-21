#!/usr/bin/env python3
"""Paper B: the (B4) envelope chain, measured against the theorems that now prove it.

`EXP_paperB_uniform_hellinger` measures the SUPREMUM of `H^2` over the query class and
reports the order.  This script is the complement: it checks the four inequalities that the
Lean proof of (B4) is built from, each one transcribed from its theorem, on the objects the
construction actually produces.  If any of them failed numerically, the corresponding Lean
statement would be false, so these are falsification tests and not illustrations.

WHAT IS BEING CHECKED, and against which theorem.

  `gaussDeriv_envelope`        phi^(n) = P_n phi with deg P_n <= n, and
                               |phi^(n)(y)| <= A_n (1+|y|)^n phi(y), A_n the coefficient
                               mass.  Checked by (a) reconstructing P_n from the recursion
                               P_{n+1} = P_n' - (y/sigma^2) P_n and comparing P_n phi to a
                               high-order finite difference of phi, and (b) the inequality
                               itself on a grid.

  `iterDiff_eq_signSum`        the recursive iterated difference equals the alternating sum
                               over the sign cube.  Two independent implementations.

  `iterDiff_mixture_envelope`  |D_b (mixture)(y)| <= prod|b_i| * envUp(sigma, R+h0, r, y),
                               with the window widening R to R+h0.  This is the LOCALISED
                               bound; the global one would need a uniform bound on phi^(r),
                               which a Gaussian envelope is not, and the script checks the
                               localised constant is the one that holds.

  `envRatio_le`                envUp^2/envLo <= envConst * exp(-y^2/(4 sigma^2)).

  `mixture_hellinger_rate`     int Delta^2/l <= h^{2r} r^{-2r} int envUp^2/envLo, the
                               headline, at the Gaussian mixture.

  `prod_abs_le_of_sum_le_one`  prod|a_i| <= r^{-r} under ||a||_1 <= 1.

A FIFTH CHECK IS A RATE, NOT AN INEQUALITY: the measured order of int Delta^2/l in h must
be no shallower than 2r.  An upper bound is what (B4) asserts, so the test is one-sided:
a steeper measured order is consistent, a shallower one is not.

SCOPE.  Every inequality here is now a theorem, so a failure would mean a defect in the
formalisation or in this transcription, not an open question.  The rate measurement is
numerical evidence at the sizes run.
"""

import hashlib
import math
import json
import pathlib
import sys
from itertools import product

import numpy as np

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(("  PASS  " if ok else "  FAIL  ") + name)
    if detail:
        print("        " + detail)


# ---------------------------------------------------------------- the Lean objects

def gkern(sigma, y):
    """`gkern sigma y = exp(-(y^2)/(2 sigma^2))`, unnormalised, as in Lean."""
    return np.exp(-(np.asarray(y) ** 2) / (2.0 * sigma ** 2))


def herm_poly(sigma, n):
    """`hermP sigma n`, as a coefficient list c with P(y) = sum_i c[i] y^i.

    P_0 = 1,  P_{n+1} = P_n' - (sigma^-2) y P_n.
    """
    c = [1.0]
    for _ in range(n):
        d = [i * c[i] for i in range(1, len(c))]            # P_n'
        s = [0.0] + [x / sigma ** 2 for x in c]             # (y/sigma^2) P_n
        m = max(len(d), len(s))
        d += [0.0] * (m - len(d))
        s += [0.0] * (m - len(s))
        c = [d[i] - s[i] for i in range(m)]
    return c


def poly_eval(c, y):
    y = np.asarray(y, dtype=float)
    out = np.zeros_like(y)
    for i in range(len(c) - 1, -1, -1):
        out = out * y + c[i]
    return out


def herm_mass(sigma, n):
    """`hermMass sigma n`: the coefficient mass of `hermP sigma n`."""
    return float(sum(abs(x) for x in herm_poly(sigma, n)))


def gauss_deriv(sigma, n, y):
    """`gaussDeriv sigma n y = (hermP sigma n).eval y * gkern sigma y`."""
    return poly_eval(herm_poly(sigma, n), y) * gkern(sigma, y)


def env_up(sigma, R, r, y):
    y = np.asarray(y, dtype=float)
    return (herm_mass(sigma, r) * (1.0 + R + np.abs(y)) ** r
            * gkern(sigma, y) * np.exp(R * np.abs(y) / sigma ** 2))


def env_lo(sigma, R, y):
    y = np.asarray(y, dtype=float)
    return (gkern(sigma, y) * np.exp(-(R * np.abs(y)) / sigma ** 2)
            * np.exp(-(R ** 2) / (2.0 * sigma ** 2)))


def env_const(sigma, R, r):
    return (herm_mass(sigma, r) ** 2 * np.exp(2.0 * r * R)
            * np.exp(R ** 2 / (2.0 * sigma ** 2))
            * np.exp((3.0 * R / sigma ** 2 + 2.0 * r) ** 2 * sigma ** 2))


def sym_diff(f, b, x):
    return (f(x - b) - f(x + b)) / 2.0


def iter_diff(f, bs, x):
    """`iterDiff f bs x`, by the same recursion as Lean."""
    if not bs:
        return f(x)
    return sym_diff(lambda z: iter_diff(f, bs[1:], z), bs[0], x)


def sign_sum(f, bs, x):
    """`2^{-r} sum_z (prod chi) f(x - sum b_i chi_i)`, the alternating form."""
    r = len(bs)
    tot = np.zeros_like(np.asarray(x, dtype=float))
    for z in product([1.0, -1.0], repeat=r):
        tot = tot + np.prod(z) * f(x - sum(b * s for b, s in zip(bs, z)))
    return tot / (2.0 ** r)


# ---------------------------------------------------------------- the run

def main():
    smoke = "--smoke" in sys.argv
    sigma = 1.0
    R = 0.75
    h0 = 0.25
    rs = [2] if smoke else [2, 3, 4]
    grid = np.linspace(-12.0, 12.0, 2001 if smoke else 24001)
    dy = grid[1] - grid[0]
    rng = np.random.default_rng(20260921)

    print("=" * 78)
    print("Paper B: the (B4) envelope chain")
    print("=" * 78)
    print(f"  sigma={sigma}  R={R}  h0={h0}  r in {rs}  grid={len(grid)} points")

    # --- the derivative identity ------------------------------------------------
    # `gaussDeriv_hasDerivAt`: each level differentiates to the next.  A five-point
    # fourth-order stencil keeps the truncation error well under the tolerance.
    deriv_err = 0.0
    step = 1e-2
    m = np.abs(grid) <= 8.0
    for n in range(0, 6):
        f = lambda z: gauss_deriv(sigma, n, z)
        fd = (8.0 * (f(grid + step) - f(grid - step))
              - (f(grid + 2 * step) - f(grid - 2 * step))) / (12.0 * step)
        ex = gauss_deriv(sigma, n + 1, grid)
        deriv_err = max(deriv_err, float(np.max(np.abs(fd[m] - ex[m]))))
    check("`gaussDeriv_hasDerivAt`: the recursion "
          "P_{n+1} = P_n' - (y/sigma^2) P_n makes gaussDeriv(n) differentiate exactly to "
          "gaussDeriv(n+1), for n = 0..5",
          deriv_err < 1e-6,
          f"max |d/dy gaussDeriv(n) - gaussDeriv(n+1)| = {deriv_err:.3e}")

    env_ok, env_worst = True, 0.0
    for n in range(0, 7):
        lhs = np.abs(gauss_deriv(sigma, n, grid))
        rhs = herm_mass(sigma, n) * (1.0 + np.abs(grid)) ** n * gkern(sigma, grid)
        env_ok &= bool(np.all(lhs <= rhs + 1e-12))
        with np.errstate(divide="ignore", invalid="ignore"):
            ratio = np.nanmax(np.where(rhs > 0, lhs / rhs, 0.0))
        env_worst = max(env_worst, float(ratio))
    check("`gaussDeriv_envelope`: |phi^(n)(y)| <= A_n (1+|y|)^n phi(y) at every "
          "grid point, for n = 0..6, with A_n the coefficient mass",
          env_ok, f"worst ratio lhs/rhs = {env_worst:.6f} (must be <= 1)")

    # --- the sign-sum identity --------------------------------------------------
    ss_err = 0.0
    for r in rs:
        for _ in range(5):
            bs = list(rng.uniform(-0.3, 0.3, size=r))
            f = lambda z: gkern(sigma, z - 0.3)
            ss_err = max(ss_err, float(np.max(np.abs(
                iter_diff(f, bs, grid) - sign_sum(f, bs, grid)))))
    check("`iterDiff_eq_signSum`: the recursive iterated difference and the alternating "
          "sum over the sign cube are the same function",
          ss_err < 1e-12, f"max discrepancy = {ss_err:.3e}")

    # --- the AM-GM input --------------------------------------------------------
    amgm_ok, amgm_worst = True, 0.0
    for r in rs:
        for _ in range(2000 if not smoke else 200):
            a = rng.normal(size=r)
            a = a / max(np.sum(np.abs(a)), 1e-12) * rng.uniform(0.1, 1.0)
            lhs = float(np.prod(np.abs(a)))
            rhs = (1.0 / r) ** r
            amgm_ok &= lhs <= rhs + 1e-15
            amgm_worst = max(amgm_worst, lhs / rhs)
    check("`prod_abs_le_of_sum_le_one`: prod|a_i| <= r^{-r} whenever ||a||_1 <= 1",
          amgm_ok, f"worst ratio = {amgm_worst:.6f} (must be <= 1)")

    # --- the ratio bound --------------------------------------------------------
    ratio_ok, ratio_worst = True, 0.0
    for r in rs:
        Rp = R + h0
        lhs = env_up(sigma, Rp, r, grid) ** 2 / env_lo(sigma, Rp, grid)
        rhs = env_const(sigma, Rp, r) * np.exp(-(1.0 / (4.0 * sigma ** 2)) * grid ** 2)
        ratio_ok &= bool(np.all(lhs <= rhs * (1 + 1e-12)))
        ratio_worst = max(ratio_worst, float(np.max(lhs / rhs)))
    check("`envRatio_le`: envUp^2/envLo <= envConst * exp(-y^2/(4 sigma^2)) at every grid "
          "point -- the polynomial absorbed by 1+x <= e^x and both linear exponentials by "
          "completing the square",
          ratio_ok, f"worst ratio lhs/rhs = {ratio_worst:.3e} (must be <= 1)")

    # --- the localised mixture bound and the rate -------------------------------
    n_comp = 4
    cs = np.linspace(-R, R, n_comp)
    w = np.array([0.4, 0.3, 0.2, 0.1])
    assert abs(w.sum() - 1.0) < 1e-15

    def mixture(z):
        return sum(wj * gkern(sigma, z - cj) for wj, cj in zip(w, cs))

    hs = [0.2, 0.1, 0.05, 0.025] if not smoke else [0.2, 0.1]
    rate_rows, mix_ok, mix_worst = {}, True, 0.0
    head_ok = True
    for r in rs:
        Rp = R + h0
        a = np.ones(r) / r                      # ||a||_1 = 1, prod|a_i| = r^{-r} exactly
        env_int = float(np.sum(env_up(sigma, Rp, r, grid) ** 2
                               / env_lo(sigma, Rp, grid)) * dy)
        rows = []
        for h in hs:
            bs = list(h * a)
            assert sum(abs(b) for b in bs) <= h0 + 1e-15
            delta = iter_diff(mixture, bs, grid)
            lhs_pt = np.abs(delta)
            rhs_pt = float(np.prod(np.abs(bs))) * env_up(sigma, Rp, r, grid)
            mix_ok &= bool(np.all(lhs_pt <= rhs_pt * (1 + 1e-9) + 1e-300))
            with np.errstate(divide="ignore", invalid="ignore"):
                mix_worst = max(mix_worst, float(np.nanmax(
                    np.where(rhs_pt > 0, lhs_pt / rhs_pt, 0.0))))
            ell = mixture(grid)
            integral = float(np.sum(delta ** 2 / ell) * dy)
            head = h ** (2 * r) * ((1.0 / r) ** r) ** 2 * env_int
            head_ok &= integral <= head * (1 + 1e-9)
            rows.append({"h": h, "integral": integral, "head_bound": head,
                         "slack": head / max(integral, 1e-300)})
        lo = np.polyfit(np.log([x["h"] for x in rows]),
                        np.log([x["integral"] for x in rows]), 1)[0]
        rate_rows[r] = {"rows": rows, "order": float(lo), "env_integral": env_int}
        print(f"    r={r}: measured order of int Delta^2/l in h = {lo:.3f}  (>= {2*r})")

    check("`iterDiff_mixture_envelope`: |D_b(mixture)(y)| <= prod|b_i| * "
          "envUp(sigma, R+h0, r, y) pointwise -- the LOCALISED bound, with the window "
          "widening R to R+h0",
          mix_ok, f"worst ratio lhs/rhs = {mix_worst:.6f} (must be <= 1)")

    check("`mixture_hellinger_rate`: int Delta^2/l <= h^{2r} r^{-2r} int envUp^2/envLo "
          "at every h and r measured",
          head_ok,
          "; ".join(f"r={r}: tightest slack "
                    f"{min(x['slack'] for x in rate_rows[r]['rows']):.2e}" for r in rs))

    order_ok = all(rate_rows[r]["order"] >= 2 * r - 0.25 for r in rs)
    check("the measured order of int Delta^2/l in h is no shallower than 2r, the "
          "direction an upper bound asserts",
          order_ok,
          "; ".join(f"r={r}: {rate_rows[r]['order']:.3f} vs 2r={2*r}" for r in rs))

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    print("\n  SCOPE.  Every inequality checked here is a theorem in LeanPaperBRatesV1, so")
    print("  a failure would indicate a defect in the formalisation or in this")
    print("  transcription, not an open question.  Only the fitted order is evidence.")

    # the envelope curve, subsampled, so the figure plots computed values
    sub = grid[::max(1, len(grid) // 400)]
    Rp = R + h0
    curve = {"y": sub.tolist()}
    for r in rs:
        curve[f"ratio_r{r}"] = (env_up(sigma, Rp, r, sub) ** 2
                                / env_lo(sigma, Rp, sub)).tolist()
        curve[f"dom_r{r}"] = (env_const(sigma, Rp, r)
                              * np.exp(-(1.0 / (4.0 * sigma ** 2)) * sub ** 2)).tolist()

    out = {"sigma": sigma, "R": R, "h0": h0, "smoke": bool(smoke),
           "rs": rs, "hs": hs, "curve": curve,
           "rate": {str(k): v for k, v in rate_rows.items()},
           "herm_mass": {str(n): herm_mass(sigma, n) for n in range(7)},
           "scope": "transcription of the proved (B4) envelope chain; the fitted order is"
                    " the only numerical claim",
           "source_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperB_envelope_rate.py").read_bytes()
           ).hexdigest(),
           "checks": CHECKS, "all_passed": nfail == 0}
    dest = ("research/unified_20260919/paperB_envelope_rate"
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
