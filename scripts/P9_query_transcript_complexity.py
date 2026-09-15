#!/usr/bin/env python3
"""Query: from the observation law to a MATCHING two-sided sample complexity.

THE GAP THIS CLOSES.  `Q2_weak_leakage_order.py` decides the LEAKAGE ORDER r of a
measurement `g` (the smallest r with a non-zero r-th density derivative gap), and
`P5_query_h4_robustness.py` pins the h^4 coefficient of the KL when r = 2.  Neither
says anything about a TRANSCRIPT: how many observations are needed to tell the two
worlds apart, and whether the h^{-2r} rate is the truth or only an upper bound.
That is what this file supplies, and it does it with the Hellinger affinity rather
than the KL, because the affinity TENSORISES exactly and gives both directions.

THE CHAIN.
 1. Observation law.  Y = F_W(X) + h g(X) + Z, the corpus's own model.  The two
    worlds are raw-indistinguishable at h = 0, so the densities differ only through
    h, and the difference is computed with the h = 0 part removed ANALYTICALLY
    (level histograms agree) and each level's term evaluated with `expm1`.
 2. One observation.  The squared Hellinger distance
        H^2 = (1/2) int (sqrt p_A - sqrt p_B)^2 = (1/2) int d^2/(sqrt p_A + sqrt p_B)^2
    is computed in that stable form.  It is checked to obey H^2 = Theta(h^{2r}) with
    the order r that Q2 assigns to the measurement, and for r = 2 its coefficient is
    checked against KL/4 with the KL coefficient P5 computed.
 3. Transcript.  The affinity rho = 1 - H^2 satisfies rho(P^N, Q^N) = rho^N exactly
    (Fubini on a product law; the observations are i.i.d. given the world because X
    and Z are drawn afresh each time).  rho itself is recomputed with an INDEPENDENT
    quadrature rule so the number is not an artefact of one rule.
 4. Matching testing bounds.  For equal priors the Bayes error of the N-sample test
    satisfies
        (1/4) rho^{2N}  <=  err_N  <=  (1/2) rho^N,
    the left from 1 - TV >= (1/2) rho_N^2 and the right from the Bhattacharyya bound.
    Hence to reach error eps,
        N >= log(1/(4 eps)) / (2 L)   is NECESSARY,
        N <= log(1/(2 eps)) / L       is SUFFICIENT,     L = -log rho,
    so that  N_necessary <= N*(h, eps) <= N_sufficient, and their RATIO is
        2 log(1/(2 eps)) / log(1/(4 eps)),
    which is 2.861 at eps = 0.05 and 2.431 at eps = 0.01 -- NOT "within a factor of
    2".  N_sufficient is a value of N that suffices; it is not true that every
    N <= N_sufficient suffices.
 5. The rate.  L = -log rho ~ H^2 ~ c_r h^{2r}, so N* = Theta(h^{-2r}) with BOTH
    constants explicit.  The run reports N*(h) h^{2r} at a sequence of h and checks
    that the necessary and sufficient counts bracket each other with the predicted
    ratio.

WHAT THIS DOES NOT ESTABLISH
  * The quadrature is float64 with a stabilised integrand and a refinement check,
    not a certified enclosure.
  * The N-sample Bayes error itself is not computed for this model (it is an
    N-dimensional integral); what is computed is the pair of bounds that sandwich
    it.  Tensorisation is Fubini on a product law, so it is an identity; the
    BRACKET it feeds is validated instead, against a Gaussian pair whose N-sample
    Bayes error is known in closed form.
  * The leakage order r is taken from Q2's exact rational test on the level sums;
    this file checks the resulting rate, it does not re-derive the order.
  * Two worlds, one measurement family, one noise level.  Nothing adaptive.

    .venv/bin/python scripts/P9_query_transcript_complexity.py
"""
from __future__ import annotations

import importlib.util, json, math
from fractions import Fraction as F
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "p5", REPO / "scripts/P5_query_h4_robustness.py")
p5 = importlib.util.module_from_spec(spec); spec.loader.exec_module(p5)
q2, g4 = p5.q2, p5.g4

phi, SIG = p5.phi, p5.SIG


def hellinger2(Y, W, cube, p, FA, FB, gfun, h):
    """H^2 = (1/2) int d^2/(sqrt p_A + sqrt p_B)^2 -- the stable form, with d
    itself computed with the h = 0 part cancelled analytically."""
    d = p5.gap_stable(Y, cube, p, FA, FB, gfun, h)
    pA = p5.densities(Y, cube, p, FA, gfun, h)
    pB = p5.densities(Y, cube, p, FB, gfun, h)
    den = (np.sqrt(np.maximum(pA, 0)) + np.sqrt(np.maximum(pB, 0))) ** 2
    m = den > 0
    return 0.5 * float(np.sum(W[m] * d[m] ** 2 / den[m]))


def kl(Y, W, cube, p, FA, FB, gfun, h):
    d = p5.gap_stable(Y, cube, p, FA, FB, gfun, h)
    pB = p5.densities(Y, cube, p, FB, gfun, h)
    return float(np.sum(W * (pB + d) * np.log1p(d / pB)))


def affinity_simpson(cube, p, FA, FB, gfun, h, lo, hi, n=20001):
    """rho by an INDEPENDENT quadrature rule (composite Simpson on a uniform grid)
    rather than the Gauss-Legendre rule used everywhere else, so that agreement is a
    check on both rules and not a tautology."""
    y = np.linspace(lo, hi, n)
    pA = p5.densities(y, cube, p, FA, gfun, h)
    pB = p5.densities(y, cube, p, FB, gfun, h)
    f = np.sqrt(np.maximum(pA * pB, 0))
    w = np.ones(n); w[1:-1:2] = 4.0; w[2:-1:2] = 2.0
    return float((hi - lo) / (3 * (n - 1)) * np.sum(w * f))


def gaussian_control():
    """The bracket (1/4) rho^{2N} <= err_N <= (1/2) rho^N, against a case where the
    N-sample Bayes error is known in closed form: P = N(0,1), Q = N(D,1) gives
    err_N = Phi(-sqrt(N) D/2) and rho = exp(-D^2/8)."""
    from math import erf, exp, sqrt
    Phi = lambda z: 0.5 * (1 + erf(z / sqrt(2)))
    rows = []
    for D in (0.05, 0.2, 0.5, 1.0):
        rho = exp(-D * D / 8)
        for N in (1, 4, 16, 64, 256):
            err = Phi(-sqrt(N) * D / 2)
            lo, hi = 0.25 * rho ** (2 * N), 0.5 * rho ** N
            rows.append({"Delta": D, "N": N, "rho": rho, "bayes_error": err,
                         "lower": lo, "upper": hi,
                         "bracket_holds": bool(lo <= err <= hi + 1e-15)})
    return rows


def main():
    print("Query: observation law -> KL/Hellinger order -> transcript -> "
          "matching testing bounds\n")
    cfg, m, cube, p, FA, FB, levels, H = p5.setup()
    g0, gap2, _c = p5.find_g0(m, cube, p, FA, FB, levels)
    u, ugaps, uname = p5.pick_u(m, cube, p, FA, FB, levels)
    Y, W = p5.grid(levels)
    p0 = p5.densities(Y, cube, p, FA, lambda x: 0.0, 0.0)

    res = {}
    print("PART 1 -- two measurements of DIFFERENT leakage order, from Q2's test")
    meas = [("g0 (order 2: kills the first-order gap)", lambda x: float(g0[x]), 2),
            (f"u = {uname} (order 1: first-order gap alive)",
             lambda x: float(u[x]), 1)]
    for name, gf, r in meas:
        s1 = max(abs(v) for v in p5._order_gaps(cube, p, FA, FB, levels,
                                                {x: F(gf(x)).limit_denominator(10**9)
                                                 for x in cube}, 1))
        print(f"   {name}: first-order gap {float(s1):.6g}  -> order r = {r}")
    res["measurements"] = [{"name": n, "order": r} for n, _f, r in meas]

    print("\nPART 2 -- H^2 and KL at one observation, and their orders")
    p2 = []
    for name, gf, r in meas:
        rows = []
        for h in (0.2, 0.1, 0.05, 0.025, 0.0125):
            h2 = hellinger2(Y, W, cube, p, FA, FB, gf, h)
            kk = kl(Y, W, cube, p, FA, FB, gf, h)
            rows.append((h, h2, kk))
        # empirical order from consecutive ratios
        orders = [math.log(rows[i][1] / rows[i + 1][1]) / math.log(2)
                  for i in range(len(rows) - 1)]
        print(f"   {name}")
        print("      H^2/h^{2r} = " + ", ".join(
            f"h={h}:{h2/h**(2*r):.6g}" for h, h2, _k in rows))
        print(f"      empirical order of H^2 (should be {2*r}): "
              + ", ".join(f"{o:.4f}" for o in orders))
        print("      KL/(4 H^2) = " + ", ".join(
            f"{k/(4*h2):.6f}" for _h, h2, k in rows))
        if abs(orders[-1] - 2 * r) > 0.05:
            raise AssertionError(f"{name}: H^2 order {orders[-1]} != {2*r}")
        if abs(rows[-1][2] / (4 * rows[-1][1]) - 1) > 0.02:
            raise AssertionError("KL and 4 H^2 do not agree in the small-h limit")
        p2.append({"name": name, "order": r,
                   "rows": [{"h": h, "H2": h2, "KL": k,
                             "H2_over_h2r": h2 / h ** (2 * r),
                             "KL_over_4H2": k / (4 * h2)} for h, h2, k in rows],
                   "empirical_orders": orders})
    res["one_observation"] = p2

    print("\nPART 3 -- the two ingredients of the transcript step, each checked")
    print("   (a) rho, by an INDEPENDENT quadrature rule")
    p3 = []
    lo_y = float(min(levels)) - 12 * SIG
    hi_y = float(max(levels)) + 12 * SIG
    for name, gf, r in meas:
        for h in (0.2, 0.05):
            h2 = hellinger2(Y, W, cube, p, FA, FB, gf, h)
            rho = 1 - h2
            rho_s = affinity_simpson(cube, p, FA, FB, gf, h, lo_y, hi_y)
            # COMPARE AT THE H^2 SCALE.  Both affinities are within 1e-6 of 1, so a
            # relative comparison of rho hides an error far larger than the signal.
            h2_s = 1 - rho_s
            rel = abs(h2_s - h2) / h2
            print(f"      {name[:28]:28s} h={h}: Gauss H^2 = {h2:.6e}, "
                  f"Simpson H^2 = {h2_s:.6e}  (relative, AT THE H^2 SCALE: "
                  f"{rel:.2e})")
            if rel > 1e-5:
                raise AssertionError("the two quadrature rules disagree on H^2")
            p3.append({"name": name, "h": h, "H2_gauss": h2, "H2_simpson": h2_s,
                       "relative_difference_at_H2_scale": rel})
    print("   (b) tensorisation rho(P^N, Q^N) = rho^N is Fubini on a product law, so")
    print("       it is an identity, not a measurement: the observations are i.i.d.")
    print("       given the world because X and Z are drawn afresh each time.  What")
    print("       is worth testing is the BRACKET it feeds, so that is done against")
    print("       a case with a closed-form N-sample Bayes error.")
    gc = gaussian_control()
    bad = [r for r in gc if not r["bracket_holds"]]
    print(f"      Gaussian control: (1/4) rho^{{2N}} <= err_N <= (1/2) rho^N holds in "
          f"{len(gc)-len(bad)}/{len(gc)} cells (4 separations x 5 transcript lengths)")
    for r in gc[:3]:
        print(f"         D={r['Delta']} N={r['N']}: {r['lower']:.6e} <= "
              f"{r['bayes_error']:.6e} <= {r['upper']:.6e}")
    if bad:
        raise AssertionError(f"the bracket fails on the Gaussian control: {bad[:2]}")
    res["transcript"] = {"rho_two_rules": p3, "gaussian_control": gc}

    print("\nPART 4 -- matching two-sided sample complexity")
    p4 = []
    for eps in (0.05, 0.01):
        print(f"   target error eps = {eps}")
        for name, gf, r in meas:
            rows = []
            for h in (0.2, 0.1, 0.05, 0.025):
                h2 = hellinger2(Y, W, cube, p, FA, FB, gf, h)
                L = -math.log1p(-h2)   # log1p: 1-H^2 is within 1e-6 of 1
                n_nec = math.log(1 / (4 * eps)) / (2 * L)
                n_suf = math.log(1 / (2 * eps)) / L
                rows.append((h, L, n_nec, n_suf))
            ratio = rows[-1][3] / rows[-1][2]
            pred = 2 * math.log(1 / (2 * eps)) / math.log(1 / (4 * eps))
            print(f"      {name[:28]:28s}: N_necessary h^{{{2*r}}} = " + ", ".join(
                f"{nn*h**(2*r):.4g}" for h, _L, nn, _ns in rows))
            print(f"      {'':28s}  N_sufficient h^{{{2*r}}} = " + ", ".join(
                f"{ns*h**(2*r):.4g}" for h, _L, _nn, ns in rows)
                + f"   ratio {ratio:.4f} (predicted {pred:.4f})")
            if abs(ratio - pred) > 1e-9:
                raise AssertionError("the bracket ratio is not the predicted one")
            # the rate itself: N * h^{2r} must settle
            v = [nn * h ** (2 * r) for h, _L, nn, _ns in rows]
            if abs(v[-1] / v[0] - 1) > 0.15:
                raise AssertionError(
                    f"N_nec h^{2*r} is not settling for {name}: {v}")
            p4.append({"eps": eps, "name": name, "order": r,
                       "rows": [{"h": h, "minus_log_rho": L, "N_necessary": nn,
                                 "N_sufficient": ns,
                                 "N_nec_times_h2r": nn * h ** (2 * r),
                                 "N_suf_times_h2r": ns * h ** (2 * r)}
                                for h, L, nn, ns in rows],
                       "bracket_ratio": ratio, "predicted_ratio": pred})
    res["sample_complexity"] = p4

    print("\nPART 5 -- the separation the two orders produce")
    p5rows = []
    for eps in (0.01,):
        for h in (0.1, 0.05, 0.025):
            ns = []
            for name, gf, r in meas:
                h2 = hellinger2(Y, W, cube, p, FA, FB, gf, h)
                L = -math.log1p(-h2)   # log1p: 1-H^2 is within 1e-6 of 1
                ns.append(math.log(1 / (2 * eps)) / L)
            print(f"   h={h}: order-2 measurement needs N <= {ns[0]:.1f}, order-1 "
                  f"needs N <= {ns[1]:.1f}   ratio {ns[0]/ns[1]:.1f}")
            p5rows.append({"h": h, "eps": eps, "N_order2": ns[0],
                           "N_order1": ns[1], "ratio": ns[0] / ns[1]})
    print("   the ratio grows like h^{-2}: killing the first-order gap costs a")
    print("   whole factor h^{-2} in transcript length, which is the operational")
    print("   content of the leakage order.")
    res["order_separation"] = p5rows

    res["not_established"] = [
        "quadrature is float64 with a stabilised integrand, not a certified "
        "enclosure; the two rules are compared at the H^2 scale, not at rho ~ 1",
        "N_necessary <= N* <= N_sufficient; the ratio is 2.861 at eps=0.05 and "
        "2.431 at eps=0.01, and N_sufficient is one sufficient N, not a threshold",
        "the N-sample Bayes error is not computed for this model; the two bounds "
        "that sandwich it are, and the bracket is validated on a Gaussian pair with "
        "a closed-form N-sample Bayes error",
        "the leakage order comes from Q2's exact rational test on the level sums; "
        "this file checks the resulting rate, it does not re-derive the order",
        "two worlds, one measurement family, one noise level, nothing adaptive",
    ]
    out = REPO / "research/worker_P9_query_20260914/P9_query_transcript_complexity.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
