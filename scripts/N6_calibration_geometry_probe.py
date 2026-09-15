#!/usr/bin/env python3
"""N6 probe -- an UNKNOWN common instrument offset: when does it destroy the
information of a new query, and by how much.  EXACT rational arithmetic.
Every part raises AssertionError on mismatch; nothing here prints-and-exits-0.

MODEL (as handed to this worker).  Query e observed as
    Y_e ~ N( m_theta(e) + b*v_e , sigma_e^2 ),      b in R unknown (nuisance).
Two worlds give mean difference d_e.  Exposure w_e, alpha_e = w_e/sigma_e^2.
Profiled (min-KL-between-composites) information
    I_prof(w) = (1/2) inf_{u in R} sum_e alpha_e (d_e - u v_e)^2 .

PARTS
  A  The completing-the-square identity, as a POLYNOMIAL identity in u, exactly,
     at many random rational configurations; plus the S_vv = 0 branch handled as
     its own case (never by dividing by zero); plus an ADVERSE control showing
     that alpha >= 0 is load-bearing (with a negative alpha the "S_vv = 0 forces
     S_dv = 0" dichotomy is FALSE, and the inf is -infinity).
  B  Immediate negative result: v == 1 and a single sampled query type gives
     I_prof = 0 identically in the exposure; more generally I_prof = 0 whenever
     d is constant on the sampled support.
  C  DESIGN duality.  Budget sum_e kappa_e x_e = 1, x >= 0, alpha_e = x_e/sigma_e^2.
         max_x I_prof(x) = (1/2) * min_{u in R} max_e (d_e - u*v_e)^2/(kappa_e sigma_e^2)
     verified exactly, together with the 1-D Helly consequence that the optimum
     is attained on a support of size <= 2, and a randomized primal falsification
     attempt over higher-support designs.
  D  The two-channel (control d0=0, shifted-reference d1=gamma) closed form and
     the claimed optimal exposures x_i*, exactly.
  E  The balanced +gamma/-gamma contrast: nuisance penalty exactly 0, so the
     unknown offset costs NOTHING there -- factor 4 is NOT universal.
     Plus a witness family where the cost factor is much LARGER than 4, so 4 is
     not an upper bound either.
  F  D6.  The legal query family, meanOffset/meanSlope and Legal transcribed
     literally from
        work/p13_conjectures/LeanD6ThresholdConstructionV1.lean      (others, bit, slope)
        work/p13_conjectures/LeanD6AllocationFiniteBridgeV1.lean     (swapped, actual_query_mean)
        work/p13_conjectures/LeanD6AllocationDualBridgeV1.lean       (Legal, Measurement)
        work/p13_conjectures/LeanD6GaussianQueryDominanceV1.lean     (meanOffset, meanSlope,
                                                                      actual_mean_affine, noise var = 1)
     The transcription is re-derived by BRUTE-FORCE enumeration of the Boolean
     cube against `gate`/`world`, so the affine mean law is checked, not assumed.
     Then: are there genuinely realisable opposite-sign pairs?  What is the exact
     cost factor for swap alternatives, for margin alternatives, and for mixed
     ones?
  G  Adverse controls: the Legal filter must actually reject things; the
     exchangeable-design cancellation must fail where the theory says it fails.

SKIPPED CONFIGURATIONS, stated not silent:
  * D6 enumeration is run at q = 2 (8 coords is m=2q+2=6) and q = 3 (m=8).
    q >= 4 (m >= 10) is SKIPPED: the legal family grows as sum_{c<=q} C(m-1,c)*2
    and the exact pair-sweep in Part F would exceed the ~5 minute budget.
  * Part C's random sweep uses kappa_e*sigma_e^2 forced to be a rational SQUARE
    so that the Chebyshev minimiser is exactly rational.  Irrational-scale
    configurations are SKIPPED (they cannot be certified in exact arithmetic here).
  * The D6 cost model kappa_e == 1 (one sample per legal query) is an ASSUMPTION
    of this probe.  No cost/pricing model for legal queries exists in the D6 Lean
    source; grep for 'kappa' finds only D6DecisionInteractionComplexity.kappaDI,
    an unrelated quantity.

Run:  python3 scripts/N6_calibration_geometry_probe.py
"""
from __future__ import annotations

import itertools
import random
import sys
import time
from fractions import Fraction as F

# ----------------------------------------------------------------- part A ---


def sums(alpha, d, v):
    S_dd = sum(a * x * x for a, x in zip(alpha, d))
    S_dv = sum(a * x * y for a, x, y in zip(alpha, d, v))
    S_vv = sum(a * y * y for a, y in zip(alpha, v))
    return S_dd, S_dv, S_vv


def quad(alpha, d, v, u):
    """sum_e alpha_e (d_e - u v_e)^2, evaluated exactly."""
    return sum(a * (x - u * y) ** 2 for a, x, y in zip(alpha, d, v))


def I_prof(alpha, d, v):
    """(1/2) inf_u sum alpha (d - u v)^2 .  The S_vv = 0 branch is its own case."""
    S_dd, S_dv, S_vv = sums(alpha, d, v)
    if S_vv == 0:
        # With alpha >= 0 this forces S_dv = 0 (Cauchy-Schwarz), so the objective
        # is the constant S_dd and the infimum is S_dd.  Assert, do not assume.
        assert all(a >= 0 for a in alpha), "I_prof's S_vv=0 branch assumes alpha >= 0"
        assert S_dv == 0, ("S_vv=0 but S_dv!=0 with alpha>=0 -- impossible", S_dv)
        return F(1, 2) * S_dd, None
    return F(1, 2) * (S_dd - S_dv * S_dv / S_vv), S_dv / S_vv


def part_A(seed=20260913, trials=400):
    print("=" * 78)
    print("A. profiled-information identity, exact rationals")
    print("=" * 78)
    rng = random.Random(seed)
    nondeg = deg = 0
    for t in range(trials):
        n = rng.randint(1, 6)
        alpha = [F(rng.randint(0, 8), rng.randint(1, 6)) for _ in range(n)]
        d = [F(rng.randint(-9, 9), rng.randint(1, 7)) for _ in range(n)]
        v = [F(rng.randint(-4, 4), rng.randint(1, 5)) for _ in range(n)]
        S_dd, S_dv, S_vv = sums(alpha, d, v)
        val, ustar = I_prof(alpha, d, v)
        if S_vv == 0:
            deg += 1
            assert val == F(1, 2) * S_dd, "degenerate branch value wrong"
            # the objective must be genuinely constant in u
            for u in (F(-3), F(0), F(7, 3)):
                assert quad(alpha, d, v, u) == S_dd, "S_vv=0 but objective moves"
            continue
        nondeg += 1
        # 1. closed form == value at the stationary point
        assert F(1, 2) * quad(alpha, d, v, ustar) == val, "closed form != value at u*"
        # 2. COMPLETED SQUARE as a polynomial identity: a quadratic is pinned by
        #    three points, so equality at 4 distinct u certifies the identity.
        rest = S_dd - S_dv * S_dv / S_vv
        for u in (F(-5, 2), F(0), F(1), F(11, 4)):
            assert quad(alpha, d, v, u) == S_vv * (u - ustar) ** 2 + rest, (
                "completed-square identity failed", t, u)
        # 3. u* is the true minimiser (strict, since S_vv > 0)
        for u in (ustar - F(1, 3), ustar + F(5, 7), ustar - F(9, 2)):
            assert quad(alpha, d, v, u) > quad(alpha, d, v, ustar), "u* not minimal"
        # 4. profiling can only remove information, never add it
        assert val <= F(1, 2) * S_dd, "profiled info exceeds known-offset info"
        assert val >= 0, "profiled info negative"
    print(f"   nondegenerate configs: {nondeg}   S_vv=0 configs: {deg}")
    assert deg > 0, ("the S_vv=0 branch was never exercised -- this sweep is not "
                     "a check of it")

    print("\n   ADVERSE control: is alpha >= 0 load-bearing, or decoration?")
    # alpha with a negative entry: S_vv can vanish with S_dv != 0, and then the
    # quadratic is LINEAR with nonzero slope, so the infimum is -infinity and no
    # 'information' exists at all.  A probe that never tested a negative alpha
    # could not tell the two branches apart.
    alpha = [F(1), F(-1)]
    v = [F(1), F(1)]
    d = [F(1), F(0)]
    S_dd, S_dv, S_vv = sums(alpha, d, v)
    assert S_vv == 0 and S_dv != 0, ("adverse control did not reproduce the "
                                     "forbidden configuration", S_vv, S_dv)
    lo = quad(alpha, d, v, F(10 ** 6))
    hi = quad(alpha, d, v, F(-10 ** 6))
    assert lo < -10 ** 5 or hi < -10 ** 5, "objective did not diverge downward"
    try:
        I_prof(alpha, d, v)
    except AssertionError:
        print("   alpha >= 0 IS load-bearing: with a negative alpha, S_vv=0 and")
        print("   S_dv!=0 coexist, the infimum is -infinity, and I_prof refuses.")
    else:
        raise AssertionError("I_prof accepted a negative alpha -- the guard is dead")


# ----------------------------------------------------------------- part B ---


def part_B():
    print("\n" + "=" * 78)
    print("B. one query type, common offset v == 1: information is exactly 0")
    print("=" * 78)
    for w_num in (1, 7, 10 ** 3, 10 ** 9):
        for sig2 in (F(1), F(1, 9), F(17, 3)):
            for dd in (F(1), F(-5, 3), F(10 ** 4)):
                alpha = [F(w_num) / sig2]
                val, _ = I_prof(alpha, [dd], [F(1)])
                assert val == 0, ("single query gave nonzero information", val)
    print("   exposure up to 1e9, sigma^2 in {1,1/9,17/3}, |d| up to 1e4:")
    print("   I_prof == 0 EXACTLY in every case.  Repeating the query forever")
    print("   does not separate a world change from an offset change.")
    # the world change is genuinely nonzero -- otherwise this is a vacuous check
    assert F(1, 2) * F(1) * F(10 ** 4) ** 2 > 0

    print("\n   generalisation: v == 1 makes I_prof the alpha-weighted VARIANCE of d")
    rng = random.Random(7)
    for _ in range(200):
        n = rng.randint(1, 6)
        alpha = [F(rng.randint(1, 8), rng.randint(1, 4)) for _ in range(n)]
        d = [F(rng.randint(-6, 6), rng.randint(1, 3)) for _ in range(n)]
        v = [F(1)] * n
        val, _ = I_prof(alpha, d, v)
        tot = sum(alpha)
        mean = sum(a * x for a, x in zip(alpha, d)) / tot
        var = sum(a * (x - mean) ** 2 for a, x in zip(alpha, d))
        assert val == F(1, 2) * var, "v==1 profiled info != weighted variance of d"
    # and therefore vanishes exactly when d is constant on the sampled support
    for c in (F(0), F(3), F(-7, 2)):
        val, _ = I_prof([F(1), F(2), F(5, 3)], [c, c, c], [F(1)] * 3)
        assert val == 0, "constant d did not give zero information"
    print("   verified on 200 random configs; d constant on support => 0.")


# ----------------------------------------------------------------- part C ---
# Design problem: x >= 0, sum_e kappa_e x_e = 1, alpha_e = x_e / sigma_e^2.
# Write s_e = sqrt(kappa_e) * sigma_e  (forced rational here), g_e = d_e/s_e,
# h_e = v_e/s_e.  Claim:   max_x I_prof(x) = (1/2) * min_u max_e (g_e - u h_e)^2.


def cheb(g, h):
    """Exact min_u max_e |g_e - u h_e| and a minimiser u.  Rational throughout.

    F(u) = max_e |g_e - u h_e| is convex piecewise linear; its minimum sits at a
    kink, i.e. at a crossing eps*(g_e - u h_e) = eps'*(g_f - u h_f).  All such
    crossings are enumerated (including e == f, which gives the zeros g_e/h_e).
    If every h_e == 0 the function is constant."""
    n = len(g)
    if all(y == 0 for y in h):
        return max((abs(x) for x in g), default=F(0)), F(0)
    cand = {F(0)}
    for e in range(n):
        for f in range(e, n):
            for eps in (1, -1):
                # g_e - u h_e = eps*(g_f - u h_f)  ->  u (eps h_f - h_e) = eps g_f - g_e
                den = eps * h[f] - h[e]
                num = eps * g[f] - g[e]
                if den != 0:
                    cand.add(num / den)
    best = None
    for u in cand:
        val = max(abs(g[e] - u * h[e]) for e in range(n))
        if best is None or val < best[0]:
            best = (val, u)
    return best


def design_max_I_prof_dual(d, v, kappa, sigma2, s):
    """(1/2) min_u max_e (d_e - u v_e)^2/(kappa_e sigma_e^2), exactly.
    `s` must satisfy s_e^2 == kappa_e * sigma_e^2 (rational square scale)."""
    for e in range(len(d)):
        assert s[e] ** 2 == kappa[e] * sigma2[e], "s is not the square root of kappa*sigma^2"
        assert s[e] > 0
    g = [d[e] / s[e] for e in range(len(d))]
    h = [v[e] / s[e] for e in range(len(d))]
    val, u = cheb(g, h)
    return F(1, 2) * val * val, u


def design_optimal_x_from_dual(d, v, kappa, sigma2, s):
    """Reconstruct an EXACT optimal design from the Chebyshev minimiser.

    Writing y_e = kappa_e x_e (so sum y = 1), rho_e = (d_e - u* v_e)/s_e and
    h_e = v_e/s_e, the profiled stationarity  sum_e alpha_e v_e (d_e - u* v_e) = 0
    becomes  sum_e y_e h_e rho_e = 0, and complementary slackness puts y on the
    active set M = argmax_e |rho_e|.  Returns (x, reason) or (None, reason)."""
    n = len(d)
    g = [d[e] / s[e] for e in range(n)]
    h = [v[e] / s[e] for e in range(n)]
    V, u = cheb(g, h)
    if V == 0:
        x = [F(0)] * n
        x[0] = F(1) / kappa[0]
        return x, "V==0"
    rho = [g[e] - u * h[e] for e in range(n)]
    M = [e for e in range(n) if abs(rho[e]) == V]
    if len(M) == 1:
        e = M[0]
        if h[e] != 0:
            return None, "singleton active set with nonzero offset loading"
        x = [F(0)] * n
        x[e] = F(1) / kappa[e]
        return x, "single v=0 channel"
    for e, f in itertools.combinations(M, 2):
        ce, cf = h[e] * rho[e], h[f] * rho[f]
        if ce == cf:
            continue
        ye = -cf / (ce - cf)
        yf = ce / (ce - cf)
        if ye < 0 or yf < 0:
            continue
        assert ye + yf == 1
        x = [F(0)] * n
        x[e] = ye / kappa[e]
        x[f] = yf / kappa[f]
        return x, "two active channels %d,%d" % (e, f)
    for e in M:
        if h[e] == 0:
            x = [F(0)] * n
            x[e] = F(1) / kappa[e]
            return x, "v=0 channel inside active set"
    return None, "no admissible pair inside the active set"


def design_I_prof_at(x, d, v, sigma2):
    alpha = [x[e] / sigma2[e] for e in range(len(d))]
    return I_prof(alpha, d, v)[0]


def design_max_I_prof_primal_small_support(d, v, kappa, sigma2):
    """max over supports of size 1 and 2, each solved exactly.

    size 1 {e}: x_e = 1/kappa_e; I_prof = 0 if v_e != 0 else d_e^2/(2 kappa_e sigma_e^2).
    size 2 {e,f}: maximise the exact 1-parameter concave function on a rational
    grid AND at the exact interior stationary point when v_e,v_f != 0."""
    n = len(d)
    best = F(0)
    arg = None
    for e in range(n):
        x = [F(0)] * n
        x[e] = F(1) / kappa[e]
        val = design_I_prof_at(x, d, v, sigma2)
        if val > best:
            best, arg = val, tuple(x)
    for e, f in itertools.combinations(range(n), 2):
        # parametrise kappa_e x_e = r, kappa_f x_f = 1-r
        cands = [F(k, 96) for k in range(1, 96)]
        # exact interior optimum of  (1/2)(d_e-d_f')^2 / (se^2/xe + sf^2/xf) type
        # for the common-offset case v_e = v_f: r* = a/(a+b), a = s_e, b = s_f
        if v[e] == v[f] and v[e] != 0:
            ae2, bf2 = kappa[e] * sigma2[e], kappa[f] * sigma2[f]
            # r* solves  se^2/r^2 == sf^2/(1-r)^2  ->  r/(1-r) = se/sf ; needs sqrt
            # add a dense rational bracket instead of an irrational point
            cands += [F(k, 4096) for k in range(1, 4096, 7)]
            del ae2, bf2
        for r in cands:
            x = [F(0)] * n
            x[e] = r / kappa[e]
            x[f] = (1 - r) / kappa[f]
            val = design_I_prof_at(x, d, v, sigma2)
            if val > best:
                best, arg = val, tuple(x)
    return best, arg


def part_C(seed=424242, trials=60):
    print("\n" + "=" * 78)
    print("C. design duality  max_x I_prof = (1/2) min_u max_e (d-uv)^2/(kappa sigma^2)")
    print("=" * 78)
    rng = random.Random(seed)
    worst_gap = F(0)
    nexact = 0
    for t in range(trials):
        n = rng.randint(2, 5)
        d = [F(rng.randint(-6, 6), rng.randint(1, 3)) for _ in range(n)]
        v = [F(rng.randint(-3, 3), rng.randint(1, 2)) for _ in range(n)]
        # rational square scale: pick s_e rational, then kappa_e*sigma_e^2 = s_e^2
        s = [F(rng.randint(1, 5), rng.randint(1, 3)) for _ in range(n)]
        kappa = [F(rng.randint(1, 4)) for _ in range(n)]
        sigma2 = [s[e] ** 2 / kappa[e] for e in range(n)]
        dual, ustar = design_max_I_prof_dual(d, v, kappa, sigma2, s)
        primal, _ = design_max_I_prof_primal_small_support(d, v, kappa, sigma2)
        assert primal <= dual, ("PRIMAL EXCEEDED DUAL -- duality claim is false",
                                t, d, v, s, kappa, float(primal), float(dual))
        gap = dual - primal
        if gap > worst_gap:
            worst_gap = gap
        # randomized falsification: can any full-support design beat the dual?
        for _ in range(40):
            raw = [F(rng.randint(0, 20), 1) for _ in range(n)]
            if sum(raw) == 0:
                continue
            tot = sum(kappa[e] * raw[e] for e in range(n))
            x = [raw[e] / tot for e in range(n)]
            val = design_I_prof_at(x, d, v, sigma2)
            assert val <= dual, ("random design BEAT the dual bound", t, val, dual)
        del ustar
        # EXACT equality certificate: rebuild the optimal design from the dual
        # minimiser and check that it attains the dual value in exact rationals.
        xstar, why = design_optimal_x_from_dual(d, v, kappa, sigma2, s)
        assert xstar is not None, ("could not reconstruct an optimal design", t, why)
        assert all(z >= 0 for z in xstar), ("reconstructed design is infeasible", xstar)
        assert sum(kappa[e] * xstar[e] for e in range(n)) == 1, "budget violated"
        attained = design_I_prof_at(xstar, d, v, sigma2)
        assert attained == dual, ("STRONG DUALITY FAILED", t, d, v, s, kappa,
                                  attained, dual, why)
        nexact += 1
    print(f"   {trials} random instances: primal <= dual always, and in all")
    print(f"   {nexact} of them an exactly-rational optimal design attains the dual")
    print("   value -- strong duality certified in exact arithmetic, not by grid.")
    print(f"   worst dual-minus-(2-support rational grid) gap: {float(worst_gap):.3e}")
    print("   (that residual is only the coarse grid's resolution; the exact")
    print("    optimum r* = s_e/(s_e+s_f) is generally irrational.)")
    print("\n   exact-attainment subfamily (s_e chosen so r* is rational):")
    # d = (0,gamma), v = (1,1), s_e rational, r* = s_e/(s_e+s_f) rational.
    for (s0, s1, gam) in [(F(1), F(1), F(3)), (F(1), F(2), F(5, 2)),
                          (F(3), F(1), F(-7, 3)), (F(2), F(5), F(1))]:
        kappa = [F(1), F(1)]
        sigma2 = [s0 ** 2, s1 ** 2]
        d = [F(0), gam]
        v = [F(1), F(1)]
        dual, _ = design_max_I_prof_dual(d, v, kappa, sigma2, [s0, s1])
        rstar = s0 / (s0 + s1)
        x = [rstar, 1 - rstar]
        primal = design_I_prof_at(x, d, v, sigma2)
        assert primal == dual, ("exact attainment failed", primal, dual)
        closed = gam ** 2 / (2 * (s0 + s1) ** 2)
        assert dual == closed, ("closed form mismatch", dual, closed)
    print("   primal == dual == gamma^2/(2(s0+s1)^2) EXACTLY at x* = s_i/(s0+s1).")

    print("\n   1-D Helly: dual over the full family == max over <=2-subfamilies")
    for t in range(40):
        n = rng.randint(3, 7)
        d = [F(rng.randint(-6, 6)) for _ in range(n)]
        v = [F(rng.randint(-3, 3)) for _ in range(n)]
        s = [F(rng.randint(1, 4)) for _ in range(n)]
        kappa = [F(1)] * n
        sigma2 = [s[e] ** 2 for e in range(n)]
        full, _ = design_max_I_prof_dual(d, v, kappa, sigma2, s)
        best = F(0)
        idx = list(range(n))
        for k in (1, 2):
            for S in itertools.combinations(idx, k):
                sub, _ = design_max_I_prof_dual([d[e] for e in S], [v[e] for e in S],
                                                [kappa[e] for e in S],
                                                [sigma2[e] for e in S],
                                                [s[e] for e in S])
                if sub > best:
                    best = sub
        assert best == full, ("Helly (support <= 2) failed", t, best, full)
    print("   verified exactly on 40 random families: the optimal design never")
    print("   needs more than two distinct query types.")


# ----------------------------------------------------------------- part D ---


def part_D():
    print("\n" + "=" * 78)
    print("D. two-channel control/shifted-reference optimum, exactly")
    print("=" * 78)
    print(f"   {'s0':>6} {'s1':>6} {'gamma':>8} {'x0*':>10} {'x1*':>10} "
          f"{'maxI_prof':>12} {'maxI_known':>12} {'factor':>8}")
    for (k0, k1, sg0, sg1, gam) in [
            (F(1), F(1), F(1), F(1), F(1)),
            (F(1), F(1), F(1), F(1), F(3, 2)),
            (F(4), F(1), F(1), F(2), F(1)),
            (F(9), F(4), F(2), F(3), F(5, 7)),
            (F(1), F(4), F(3), F(1), F(2))]:
        # sqrt(kappa) must be rational for an exact certificate
        r0, r1 = F(int(k0 ** F(1, 2) if False else 0)), None
        import math
        rk0 = F(math.isqrt(k0.numerator), math.isqrt(k0.denominator))
        rk1 = F(math.isqrt(k1.numerator), math.isqrt(k1.denominator))
        assert rk0 ** 2 == k0 and rk1 ** 2 == k1, "kappa is not a rational square"
        del r0, r1
        s0, s1 = sg0 * rk0, sg1 * rk1          # s_i = sigma_i * sqrt(kappa_i)
        kappa = [k0, k1]
        sigma2 = [sg0 ** 2, sg1 ** 2]
        d = [F(0), gam]
        v = [F(1), F(1)]
        dual, _ = design_max_I_prof_dual(d, v, kappa, sigma2, [s0, s1])
        closed = gam ** 2 / (2 * (s0 + s1) ** 2)
        assert dual == closed, ("two-channel closed form failed", dual, closed)
        x0 = (sg0 / rk0) / (s0 + s1)
        x1 = (sg1 / rk1) / (s0 + s1)
        assert k0 * x0 + k1 * x1 == 1, ("x* violates the budget", x0, x1)
        at_star = design_I_prof_at([x0, x1], d, v, sigma2)
        assert at_star == closed, ("x* does not attain the optimum", at_star, closed)
        # known-offset one-channel: spend the whole budget on the shifted query
        known = gam ** 2 / (2 * sg1 ** 2 * k1)
        assert known == F(1, 2) * max(F(0), gam ** 2 / (k1 * sg1 ** 2))
        factor = known / closed
        print(f"   {float(s0):>6.3f} {float(s1):>6.3f} {float(gam):>8.4f} "
              f"{float(x0):>10.5f} {float(x1):>10.5f} {float(closed):>12.6f} "
              f"{float(known):>12.6f} {float(factor):>8.4f}")
        if sg0 == sg1 and k0 == k1:
            assert factor == 4, ("equal sigma, equal cost must give exactly 4",
                                 factor)
            assert closed == gam ** 2 / (8 * sg0 ** 2)
    print("   equal sigma and equal cost: exactly gamma^2/(8 sigma^2) against the")
    print("   known-offset gamma^2/(2 sigma^2) -- factor 4 FOR THESE TWO DESIGNS.")
    print("   Unequal (sigma,kappa) already move the factor off 4: it is")
    print("   (sigma0 sqrt(k0)+sigma1 sqrt(k1))^2 / (sigma1^2 k1), not a constant.")


# ----------------------------------------------------------------- part E ---


def cost_factor(d, v, kappa, sigma2, s):
    """max_x I_known / max_x I_prof, exactly (None when I_prof optimum is 0)."""
    known = F(1, 2) * max(d[e] ** 2 / (kappa[e] * sigma2[e]) for e in range(len(d)))
    prof, _ = design_max_I_prof_dual(d, v, kappa, sigma2, s)
    if prof == 0:
        return known, prof, None
    return known, prof, known / prof


def part_E():
    print("\n" + "=" * 78)
    print("E. the factor 4 is neither universal nor an upper bound")
    print("=" * 78)
    one = F(1)
    print(f"   {'family d':>26} {'maxI_known':>11} {'maxI_prof':>11} {'factor':>9}")
    rows = [
        ("control+target  (0, g)", [F(0), F(1)]),
        ("balanced        (+g,-g)", [F(1), F(-1)]),
        ("skewed          (+g,-g/2)", [F(1), F(-1, 2)]),
        ("one-sided       (g, g/2)", [F(1), F(1, 2)]),
        ("one-sided tight (g, 9g/10)", [F(1), F(9, 10)]),
        ("constant        (g, g)", [F(1), F(1)]),
        ("three-point (0,+g,-g)", [F(0), F(1), F(-1)]),
    ]
    for name, d in rows:
        n = len(d)
        v = [one] * n
        kappa = [one] * n
        sigma2 = [one] * n
        s = [one] * n
        known, prof, fac = cost_factor(d, v, kappa, sigma2, s)
        # closed check: with v==1, sigma==kappa==1 the optimum is (range)^2/8
        rng_ = (max(d) - min(d))
        assert prof == rng_ ** 2 / 8, ("range^2/8 law failed", name, prof, rng_)
        assert known == max(x ** 2 for x in d) / 2
        print(f"   {name:>26} {float(known):>11.5f} {float(prof):>11.5f} "
              f"{('%.4f' % float(fac)) if fac is not None else 'INFINITE':>9}")
    # the headline assertions
    d = [F(1), F(-1)]
    _, prof, fac = cost_factor(d, [one] * 2, [one] * 2, [one] * 2, [one] * 2)
    assert fac == 1, ("balanced +-gamma must cost NOTHING", fac)
    x = [F(1, 2), F(1, 2)]
    assert sums([F(1, 2), F(1, 2)], d, [one] * 2)[1] == 0, "sum alpha d v != 0"
    assert design_I_prof_at(x, d, [one] * 2, [one] * 2) == \
        F(1, 2) * sums(x, d, [one] * 2)[0], "nuisance penalty was not zero"
    d = [F(1), F(9, 10)]
    _, _, fac = cost_factor(d, [one] * 2, [one] * 2, [one] * 2, [one] * 2)
    assert fac > 4, ("a one-sided family must cost MORE than 4", fac)
    assert fac == 400, ("expected 4*1/(1/10)^2 = 400", fac)
    d = [F(1), F(1)]
    _, prof, fac = cost_factor(d, [one] * 2, [one] * 2, [one] * 2, [one] * 2)
    assert prof == 0 and fac is None, "constant d must give zero profiled info"
    print("   +g/-g costs EXACTLY 1.  (g, 9g/10) costs EXACTLY 400.  (g,g) costs")
    print("   infinity.  So 4 is a property of the (0,gamma) geometry alone.")


# ----------------------------------------------------------------- part F ---
# D6 legal query family, transcribed from the Lean sources named in the header.


def d6_gate(A, j, x, others_Aj):
    """gate A j x = if x j then 0 else if (exists i in A, x i) or 2 <= count(others,x)
    then 1 else 0    [LeanD6ThresholdConstructionV1.lean:26]"""
    if x[j]:
        return F(0)
    if any(x[i] for i in A):
        return F(1)
    if sum(1 for i in others_Aj if x[i]) >= 2:
        return F(1)
    return F(0)


def d6_coeff(A, j, mu, i):
    """coeff A j mu i = 0 if i in A else (mu-1) if i = j else (1-mu)"""
    if i in A:
        return F(0)
    if i == j:
        return mu - 1
    return 1 - mu


def d6_world(A, j, mu, x, m, others_Aj):
    """world = linear(coeff) + gate   [LeanD6ThresholdConstructionV1.lean:38]"""
    return sum(d6_coeff(A, j, mu, i) * (1 if x[i] else 0)
               for i in range(m)) + d6_gate(A, j, x, others_Aj)


def d6_others(A, j, m):
    return frozenset(i for i in range(m) if i != j and i not in A)


def d6_meanOffset_slope(A, j, e, others_Aj):
    """meanOffset / meanSlope, LeanD6GaussianQueryDominanceV1.lean:20-26."""
    kind, payload = e
    if kind == "s":
        i = payload
        if i in A:
            return F(1), F(0)
        if i == j:
            return F(-1), F(1)
        return F(1), F(-1)
    G, h = payload
    c = F(len(G & others_Aj))
    b = F(1) if h else F(0)
    return (F(1) - b if not h else F(0)) + (c - b), -(c - b)


def d6_actualMean(A, j, mu, e, others_Aj):
    off, sl = d6_meanOffset_slope(A, j, e, others_Aj)
    return off + sl * mu


def d6_legal(j, q, e):
    """Legal, LeanD6AllocationDualBridgeV1.lean:173."""
    kind, payload = e
    if kind == "s":
        return True
    G, h = payload
    return (j not in G) and (len(G) <= q) and ((len(G) >= 2) if not h else True)


def d6_enumerate(m, j, q):
    """all measurements (legal and not), and the legal subset."""
    allm, legal = [], []
    for i in range(m):
        e = ("s", i)
        allm.append(e)
        if d6_legal(j, q, e):
            legal.append(e)
    coords = list(range(m))
    for size in range(0, q + 2):
        for G in itertools.combinations(coords, size):
            for h in (False, True):
                e = ("p", (frozenset(G), h))
                allm.append(e)
                if d6_legal(j, q, e):
                    legal.append(e)
    return allm, legal


def d6_swapped(A, a, b):
    """swapped A a b = insert b (A.erase a)"""
    return frozenset((set(A) - {a}) | {b})


def d6_check_affine_law(m, j, q, A, mus):
    """Brute-force the Boolean cube: does world(.) really realise the affine law?
    This is the step that makes the transcription a CHECK, not an assumption."""
    others_Aj = d6_others(A, j, m)
    # singleton measurement = productResponse corner (world) i true
    #   = world(e_i) - world(0)  under the `corner` weighting (x=0 elsewhere)
    zero = [False] * m
    for mu in mus:
        base = d6_world(A, j, mu, zero, m, others_Aj)
        for i in range(m):
            xi = [False] * m
            xi[i] = True
            resp = d6_world(A, j, mu, xi, m, others_Aj) - base
            claim = d6_actualMean(A, j, mu, ("s", i), others_Aj)
            assert resp == claim, ("singleton mean law FAILED", i, resp, claim)
        # query G j h = jointCorner G j (h=True) / plainCorner G (h=False):
        #   plainCorner G  sets x_i = True exactly on G
        #   jointCorner G j sets x_i = True on G and on j
        for size in range(0, q + 1):
            for G in itertools.combinations([c for c in range(m) if c != j], size):
                Gs = frozenset(G)
                for h in (False, True):
                    if not d6_legal(j, q, ("p", (Gs, h))):
                        continue
                    x = [False] * m
                    for i in Gs:
                        x[i] = True
                    if h:
                        x[j] = True
                    val = d6_world(A, j, mu, x, m, others_Aj)
                    claim = d6_actualMean(A, j, mu, ("p", (Gs, h)), others_Aj)
                    assert val == claim, ("query mean law FAILED", Gs, h, val, claim)
    return True


def part_F():
    print("\n" + "=" * 78)
    print("F. D6: is there a genuinely realisable opposite-sign pair?")
    print("=" * 78)
    one = F(1)
    for q in (2, 3):
        m = 2 * q + 2
        j = 0
        A = frozenset(range(1, q + 2))            # |A| = q+1, j not in A
        others_Aj = d6_others(A, j, m)
        assert len(others_Aj) == q, (len(others_Aj), q)
        mus = [F(1, 4), F(1, 2), F(3, 4), F(1), F(0), F(7, 5)]
        d6_check_affine_law(m, j, q, A, mus[:3])
        allm, legal = d6_enumerate(m, j, q)
        rejected = len(allm) - len(legal)
        assert rejected > 0, ("the Legal filter rejected NOTHING -- it is not a "
                              "filter at this (m,q)")
        print(f"\n   q={q} m={m}  |A|={len(A)} |others|={len(others_Aj)}  "
              f"legal={len(legal)} rejected={rejected}")
        print("   affine mean law re-derived from the Boolean cube: OK")

        p, r = min(A), min(others_Aj)
        Ap = d6_swapped(A, p, r)
        assert Ap != A and len(Ap) == len(A) and j not in Ap
        others_Ap = d6_others(Ap, j, m)

        # ---- (i) SWAP alternative at FIXED margin
        print(f"\n   (i) swap alternative A -> swapped(A,{p},{r}), margin held fixed")
        print(f"      {'mu':>7} {'distinct d':>34} {'I_known':>9} {'I_prof':>9} {'factor':>8}")
        for mu in mus:
            d = [d6_actualMean(A, j, mu, e, others_Aj)
                 - d6_actualMean(Ap, j, mu, e, others_Ap) for e in legal]
            uniq = sorted(set(d))
            # dedupe: sigma == 1 and kappa == 1 for every legal query, so two
            # queries with the same d are interchangeable in the design problem.
            n = len(uniq)
            known, prof, fac = cost_factor(uniq, [one] * n, [one] * n,
                                           [one] * n, [one] * n)
            # dedupe cross-check: recompute on the FULL legal list (no merging)
            nf = len(d)
            kf, pf, ff = cost_factor(d, [one] * nf, [one] * nf,
                                     [one] * nf, [one] * nf)
            assert (kf, pf, ff) == (known, prof, fac), (
                "deduping distinct d values changed the answer -- the merge is "
                "not exact", kf, known, pf, prof)
            # with v==1 and kappa==sigma^2==1 the optimum must be (range d)^2/8
            assert prof == (max(uniq) - min(uniq)) ** 2 / 8, "range^2/8 law failed"
            lab = ",".join("%.3g" % float(z) for z in uniq)
            print(f"      {float(mu):>7.3f} {lab:>34} {float(known):>9.5f} "
                  f"{float(prof):>9.5f} "
                  f"{('%.4f' % float(fac)) if fac is not None else 'INF':>8}")
            # the claim under test: an opposite-sign pair is REALISED
            has_pos = any(z > 0 for z in uniq)
            has_neg = any(z < 0 for z in uniq)
            if mu == 0:
                # singletons all give 0; pair queries give +-1
                assert has_pos and has_neg, "mu=0 lost the opposite-sign pair"
            if mu == 1:
                assert has_pos and has_neg, "mu=1 lost the opposite-sign pair"
            assert has_pos and has_neg, ("no opposite-sign pair at mu=%s" % mu)
            assert fac == 1, ("swap alternative should cost NOTHING", mu, fac)
        print("      every mu tested: an opposite-sign pair EXISTS and the cost")
        print("      factor is EXACTLY 1 -- unknown calibration is free here.")
        # name the witnesses
        mu = F(3, 4)
        wit = [(e, d6_actualMean(A, j, mu, e, others_Aj)
                - d6_actualMean(Ap, j, mu, e, others_Ap)) for e in legal]
        pos = [e for e, z in wit if z > 0][:2]
        neg = [e for e, z in wit if z < 0][:2]
        print(f"      witnesses at mu=3/4:  d>0 at {pos}")
        print(f"                            d<0 at {neg}")

        # ---- (ii) MARGIN alternative at fixed hidden set
        print("\n   (ii) margin alternative (A,mu) vs (A,nu), hidden set fixed")
        print(f"      {'mu':>6} {'nu':>6} {'range d':>9} {'I_known':>9} "
              f"{'I_prof':>9} {'factor':>8} {'claim 4q^2/(1+q)^2':>19}")
        for (mu, nu) in [(F(1, 2), F(1, 4)), (F(3, 4), F(1, 8)), (F(1), F(0))]:
            d = [d6_actualMean(A, j, mu, e, others_Aj)
                 - d6_actualMean(A, j, nu, e, others_Aj) for e in legal]
            uniq = sorted(set(d))
            n = len(uniq)
            known, prof, fac = cost_factor(uniq, [one] * n, [one] * n,
                                           [one] * n, [one] * n)
            claim = F(4 * q * q, (1 + q) ** 2)
            assert fac == claim, ("margin-alternative factor law failed",
                                  mu, nu, fac, claim)
            print(f"      {float(mu):>6.3f} {float(nu):>6.3f} "
                  f"{float(max(uniq)-min(uniq)):>9.4f} {float(known):>9.5f} "
                  f"{float(prof):>9.5f} {float(fac):>8.4f} {float(claim):>19.4f}")
        print(f"      exact law at q={q}: factor = 4q^2/(1+q)^2 = "
              f"{float(F(4*q*q,(1+q)**2)):.4f}, NOT 4.")

        # ---- (iii) MIXED alternative: swap AND margin move together
        print("\n   (iii) mixed alternative (A,mu) vs (swapped,nu) -- the scope bound")
        print(f"      {'mu':>6} {'nu':>6} {'I_known':>9} {'I_prof':>9} {'factor':>8}")
        for (mu, nu) in [(F(1, 2), F(1, 4)), (F(3, 4), F(5, 8))]:
            d = [d6_actualMean(A, j, mu, e, others_Aj)
                 - d6_actualMean(Ap, j, nu, e, others_Ap) for e in legal]
            uniq = sorted(set(d))
            n = len(uniq)
            known, prof, fac = cost_factor(uniq, [one] * n, [one] * n,
                                           [one] * n, [one] * n)
            print(f"      {float(mu):>6.3f} {float(nu):>6.3f} {float(known):>9.5f} "
                  f"{float(prof):>9.5f} "
                  f"{('%.4f' % float(fac)) if fac is not None else 'INF':>8}")
            assert fac is None or fac >= 1
        print("      the swap-alternative cancellation does NOT survive a")
        print("      simultaneous margin move: the transposition (p r) no longer")
        print("      negates d, because coordinates outside A pick up (nu-mu).")

        # ---- (iv) blind design: exchangeable allocation kills the nuisance
        #      for EVERY swap simultaneously, at fixed margin.
        mu = F(3, 4)
        sing = [e for e in legal if e[0] == "s"]
        nsing = len(sing)
        xs = {e: F(1, nsing) for e in sing}
        bad = 0
        for pp in A:
            for rr in others_Aj:
                Aq = d6_swapped(A, pp, rr)
                oq = d6_others(Aq, j, m)
                Sdv = sum(xs[e] * (d6_actualMean(A, j, mu, e, others_Aj)
                                   - d6_actualMean(Aq, j, mu, e, oq)) for e in sing)
                if Sdv != 0:
                    bad += 1
        assert bad == 0, ("exchangeable singleton design failed to cancel the "
                          "nuisance for %d swaps" % bad)
        print(f"\n   (iv) uniform-over-singletons design: sum alpha d v == 0 for")
        print(f"      all {len(A)*len(others_Aj)} swaps at fixed margin -- exact.")
        # adverse control: a NON-exchangeable design must fail for some swap
        xs2 = dict(xs)
        xs2[sing[1]] = xs2[sing[1]] + F(1, 100)
        xs2[sing[2]] = xs2[sing[2]] - F(1, 100)
        bad2 = 0
        for pp in A:
            for rr in others_Aj:
                Aq = d6_swapped(A, pp, rr)
                oq = d6_others(Aq, j, m)
                Sdv = sum(xs2[e] * (d6_actualMean(A, j, mu, e, others_Aj)
                                    - d6_actualMean(Aq, j, mu, e, oq)) for e in sing)
                if Sdv != 0:
                    bad2 += 1
        assert bad2 > 0, ("the cancellation check can never return False -- it is "
                          "not a check")
        print(f"      adverse control: tilting the design by 1/100 breaks the")
        print(f"      cancellation for {bad2} swaps, so the check is discriminating.")


# ----------------------------------------------------------------- part G ---


def part_G():
    print("\n" + "=" * 78)
    print("G. restricted-subfamily witness: D6 can cost MUCH more than 4")
    print("=" * 78)
    one = F(1)
    for q in (2, 3, 5, 8):
        # margin alternative, design restricted to the two largest-|slope| legal
        # queries (G,false) with |G cap others| = q and q-1: slopes -q and -(q-1)
        d = [F(-q), F(-(q - 1))]
        known, prof, fac = cost_factor(d, [one] * 2, [one] * 2, [one] * 2, [one] * 2)
        assert fac == 4 * q * q, ("restricted-subfamily factor law failed", q, fac)
        print(f"   q={q}: design restricted to slopes {{-{q},-{q-1}}} costs "
              f"factor {float(fac):.0f}")
    print("   These are legal D6 queries.  If an acquisition policy happens to")
    print("   use only the two loudest ones, unknown calibration costs 4q^2, not 4.")



# ----------------------------------------------------------------- part H ---
# The SHIFTED-REFERENCE construction the two-channel design is drawn from.
# Independent re-transcription (nothing imported) of the fixed-world model of
# scripts/MASTER_reference_contrast_v2.py PART C, whose own gate is transcribed
# from work/p13_conjectures/LeanD6ThresholdConstructionV1.lean:26.
#     F_{A,t0}(x) = g_A(x) - E_{t0}[g_A] + sum_i (rho*1_T(i) - s_i(t0))(x_i - t0)
#     readout     Delta_i(t1) = E_{t1}[Y | X_i=1] - E_{t1}[Y | X_i=0]
# QUESTION: in the two-point test between F_{A,t0} and F_{A',t0} (A' = A with p
# swapped for r), is the "control query with d0 = 0" really the only companion
# channel available, or does the mirror coordinate r carry -Gamma?


def _slopes_ab(alpha, beta, t):
    c = (1 - t) ** (alpha + beta - 1)
    return c * (1 + (beta - 1) * t), (beta - 1) * t * c, c


class _FixedWorld:
    def __init__(self, alpha, beta, t0, rho, A, T):
        self.alpha, self.beta = alpha, beta
        self.n = alpha + beta + 1
        self.z = self.n - 1
        self.A = frozenset(A)
        self.B = frozenset(range(self.n - 1)) - self.A
        self.T = frozenset(T)
        self.t0 = t0
        assert len(self.A) == alpha and len(self.B) == beta and self.z not in self.T
        self.cube = list(itertools.product((0, 1), repeat=self.n))
        self.g = [self._gate(x) for x in self.cube]
        Eg0 = self._expect(self.g, t0)
        self.s0 = [self._slope(self.g, t0, i) for i in range(self.n)]
        coef = [rho * (1 if i in self.T else 0) - self.s0[i] for i in range(self.n)]
        self.F = [self.g[m] - Eg0
                  + sum(coef[i] * (F(x[i]) - t0) for i in range(self.n))
                  for m, x in enumerate(self.cube)]

    def _gate(self, x):
        if x[self.z] == 1:
            return F(0)
        if any(x[i] for i in self.A):
            return F(1)
        return F(1) if sum(x[j] for j in self.B) >= 2 else F(0)

    def _w(self, x, t, skip=()):
        w = F(1)
        for i, xi in enumerate(x):
            if i in skip:
                continue
            w *= t if xi == 1 else (1 - t)
        return w

    def _expect(self, vals, t):
        return sum(self._w(x, t) * vals[m] for m, x in enumerate(self.cube))

    def _slope(self, vals, t, i):
        hi = sum(self._w(x, t, skip=(i,)) * vals[m]
                 for m, x in enumerate(self.cube) if x[i] == 1)
        lo = sum(self._w(x, t, skip=(i,)) * vals[m]
                 for m, x in enumerate(self.cube) if x[i] == 0)
        return hi - lo


def part_H():
    print("\n" + "=" * 78)
    print("H. the shifted-reference construction: where the +gamma/-gamma pair is")
    print("=" * 78)
    one = F(1)
    print(f"   {'k':>2} {'t0':>7} {'t1':>7} {'Gamma':>11} {'#i: d_i!=0':>11} "
          f"{'ctrl fac':>9} {'pair fac':>9}")
    for k in (3, 4):
        alpha, beta = k, k - 1
        n = alpha + beta + 1
        nonz = list(range(n - 1))
        T = frozenset(range(min(k, n - 1)))
        A = frozenset(nonz[:alpha])
        p = max(A)                              # swapped out of A
        r = min(set(nonz) - A)                  # swapped into A
        A2 = (A - {p}) | {r}
        for (t0, t1) in [(F(1, 4), F(1, 2)), (F(1, 5), F(2, 5)), (F(1, 3), F(1, 3))]:
            rho = F(3, 2)
            WA = _FixedWorld(alpha, beta, t0, rho, A, T)
            WB = _FixedWorld(alpha, beta, t0, rho, A2, T)
            # the two-point mean difference of the readout, coordinate by coordinate
            d = [WA._slope(WA.F, t1, i) - WB._slope(WB.F, t1, i) for i in range(n)]
            a1, b1, c1 = _slopes_ab(alpha, beta, t1)
            a0, b0, c0 = _slopes_ab(alpha, beta, t0)
            gamma = c1 - c0
            # closed form check: c(t) = (1-t)^(2k-2) since alpha+beta-1 = 2k-2
            assert c1 == (1 - t1) ** (2 * k - 2), "c(t) closed form failed"
            assert c0 == (1 - t0) ** (2 * k - 2), "c(t) closed form failed"
            # THE CLAIM UNDER TEST
            assert d[p] == gamma, ("swapped-out coordinate does not carry +gamma",
                                   k, t0, t1, d[p], gamma)
            assert d[r] == -gamma, ("swapped-in coordinate does not carry -gamma",
                                    k, t0, t1, d[r], gamma)
            for i in range(n):
                if i not in (p, r):
                    assert d[i] == 0, ("a third coordinate moved", i, d[i])
            nz = sum(1 for z in d if z != 0)
            if t1 == t0:
                assert gamma == 0 and nz == 0, "the floor at t1=t0 is not a floor"
                print(f"   {k:>2} {float(t0):>7.4f} {float(t1):>7.4f} "
                      f"{float(gamma):>11.6f} {nz:>11} {'n/a':>9} {'n/a':>9}")
                continue
            assert nz == 2, ("exactly two coordinates should move", nz)
            # control design  (d = 0 at any third coordinate, d = gamma at p)
            kn, pr, ctrl = cost_factor([F(0), gamma], [one] * 2, [one] * 2,
                                       [one] * 2, [one] * 2)
            # balanced design (d = +gamma at p, d = -gamma at r)
            kn2, pr2, pair = cost_factor([gamma, -gamma], [one] * 2, [one] * 2,
                                         [one] * 2, [one] * 2)
            assert ctrl == 4, ("control design must cost exactly 4", ctrl)
            assert pair == 1, ("balanced design must cost exactly 1", pair)
            assert pr2 == 4 * pr, ("the balanced design must be 4x the control "
                                   "design's profiled optimum", pr2, pr)
            print(f"   {k:>2} {float(t0):>7.4f} {float(t1):>7.4f} "
                  f"{float(gamma):>11.6f} {nz:>11} {float(ctrl):>9.4f} "
                  f"{float(pair):>9.4f}")
    print("   Gamma = (1-t1)^(2k-2) - (1-t0)^(2k-2), verified against the cube.")
    print("   EXACTLY TWO coordinates move, and they move by +Gamma and -Gamma.")
    print("   So the companion channel of the shifted-reference query is NOT")
    print("   forced to be a d=0 control: the mirror coordinate r is a legal")
    print("   query of the SAME type and cost carrying -Gamma.  Spending the")
    print("   second half of the budget there instead of on a control doubles")
    print("   the contrast to 2*Gamma and recovers the whole factor of 4.")
    print("   CAVEAT (scope): this holds for the offset model v_e == 1 on the")
    print("   readout.  If the SAME additive b enters the raw Y before the")
    print("   Delta_i differencing, it cancels in Delta_i outright (v_e == 0)")
    print("   and there is no nuisance to profile at all.  Which of the two")
    print("   applies is a modelling choice, not a theorem proved here.")


def main():
    t0 = time.time()
    part_A()
    part_B()
    part_C()
    part_D()
    part_E()
    part_F()
    part_G()
    part_H()
    print(f"\nALL N6 CHECKS PASSED.  elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    sys.setrecursionlimit(10000)
    main()
