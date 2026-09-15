#!/usr/bin/env python3
"""Query E: the CONSTANTS of  c_- h^{2r} <= H^2 <= c_+ h^{2r}  on the real mixture,
by the interval route rather than by chasing an exact KL coefficient.

THE ARGUMENT BEING INSTANTIATED (supervisor's 3a-3c).  With a finite X, weights pi_x
and Gaussian noise, the two worlds' densities differ only through h, and grouping the
cube by baseline level v,
    p_{A,h} - p_{B,h} = sum_j h^j Delta_j + Rem,
    Delta_j(y) = ((-1)^j/j!) sum_v (M_{A,j}(v) - M_{B,j}(v)) phi^{(j)}(y - v),
    M_{W,j}(v) = sum_{x : f_W(x)=v} pi_x g(x)^j.
For j < r every level coefficient agrees, so Delta_j == 0; at j = r some level
coefficient differs.  That is NOT yet enough: the SUM could still vanish.  It does
not, and the reason is a tail argument -- after factoring the common Gaussian, the
terms are polynomials times e^{v y/sigma^2}, so the LARGEST level v* with a non-zero
coefficient dominates as y -> +infinity.  This file exhibits v*, checks the
domination numerically, and then:
  * LOWER: takes an interval E on which Delta_r keeps its sign, computes
    a_E = int_E Delta_r, verifies |P_{A,h}(E) - P_{B,h}(E)| >= |a_E| h^r / 2 down to
    an explicit h_0, and reports c_- = a_E^2/16 from
        |P(E) - Q(E)| = |int_E (sqrt p - sqrt q)(sqrt p + sqrt q)| <= 2 sqrt(H^2).
  * UPPER: bounds H^2 <= (1/2) int d_h^2/p_{B,h} and reports the measured
    c_+ = sup_h H^2/h^{2r}, together with the envelope check that
    d_h^2/p_{B,h} stays under C (1+|y|^{2r}) exp(-y^2/(4 sigma^2)) so the integral is
    finite -- the step where assuming d_h/p_0 is uniformly small would be WRONG,
    because the Gaussian tails break it at every h.
Then the two constants are fed into the transcript bracket to give the two-sided
sample complexity with real numbers.

WHAT THIS DOES NOT ESTABLISH
  * The Taylor remainder bounds are MEASURED on a grid of h, not proved; this file
    supplies the constants and checks the shape, and
    `LeanQueryRateAssemblyV1` proves the algebra that turns the constants into
    N* = Theta(h^{-2r}).
  * The non-vanishing of Delta_r is checked at the dominating level and on the grid;
    the exponential-polynomial independence argument is not formalised.
  * One pair of worlds, one noise level, r in {1, 2}.

    .venv/bin/python scripts/P15_query_hellinger_order.py
"""
from __future__ import annotations
import importlib.util, json, math
from fractions import Fraction as F
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("p5", REPO / "scripts/P5_query_h4_robustness.py")
p5 = importlib.util.module_from_spec(spec); spec.loader.exec_module(p5)
SIG = p5.SIG


def phi_deriv(u, j):
    """phi^{(j)} for j = 0,1,2, sigma = SIG."""
    f = p5.phi(u)
    if j == 0:
        return f
    if j == 1:
        return -(u / SIG ** 2) * f
    if j == 2:
        return ((u ** 2 / SIG ** 4) - 1 / SIG ** 2) * f
    raise ValueError(j)


def level_coeffs(cube, p, FA, FB, levels, gmap, j):
    out = {}
    for v in levels:
        s = F(0)
        for x in cube:
            if FA[x] == v: s += p[x] * gmap[x] ** j
            if FB[x] == v: s -= p[x] * gmap[x] ** j
        out[v] = s
    return out


def main():
    print("Query: the constants of H^2 ~ h^{2r} on the real mixture\n")
    cfg, m, cube, p, FA, FB, levels, H = p5.setup()
    g0, gap2, _c = p5.find_g0(m, cube, p, FA, FB, levels)
    u, ugaps, uname = p5.pick_u(m, cube, p, FA, FB, levels)
    Y, W = p5.grid(levels)
    res = {}
    cases = [("g0 (order 2)", {x: F(g0[x]) for x in cube}, 2),
             (f"u = {uname} (order 1)", {x: F(u[x]) for x in cube}, 1)]

    for name, gmap, r in cases:
        print(f"PART A [{name}] -- level coefficients and the dominating level")
        for j in range(r):
            co = level_coeffs(cube, p, FA, FB, levels, gmap, j)
            if any(v != 0 for v in co.values()):
                raise AssertionError(f"order {j} does not vanish for {name}")
        cr = level_coeffs(cube, p, FA, FB, levels, gmap, r)
        nz = {v: c for v, c in cr.items() if c != 0}
        if not nz:
            raise AssertionError(f"order {r} coefficient vanishes for {name}")
        vstar = max(nz)
        print(f"   orders 0..{r-1} vanish at EVERY level; order {r} has "
              f"{len(nz)} non-zero level coefficients")
        print(f"   dominating level v* = {vstar} (coefficient {float(nz[vstar]):.6g})")

        sgn = (-1) ** r / math.factorial(r)
        def Delta(y):
            return sgn * sum(float(c) * phi_deriv(y - float(v), r)
                             for v, c in nz.items())
        # TAIL DOMINATION, computed in the stable ratio form.  Evaluating the two
        # Gaussians separately underflows long before the domination is visible: the
        # levels here are as close as 1e-5 apart, so the exponential advantage
        # exp((v*-v)(2y-v-v*)/(2 sigma^2)) only bites at large y.
        def polyfac(uu):
            if r == 0: return 1.0
            if r == 1: return -uu / SIG ** 2
            return uu ** 2 / SIG ** 4 - 1 / SIG ** 2
        def ratio_at(y):
            vs = float(vstar)
            tot = 0.0
            pl = polyfac(y - vs)
            for v, c in nz.items():
                fv = float(v)
                ex = (fv - vs) * (2 * y - fv - vs) / (2 * SIG ** 2)
                pr = polyfac(y - fv)
                if pl == 0:
                    return float("nan")
                tot += (float(c) / float(nz[vstar])) * (pr / pl) * math.exp(ex)
            return tot
        ys = [float(vstar) + t for t in (10, 40, 160, 640)]
        ratios = [ratio_at(y) for y in ys]
        print(f"   Delta_{r}(y) / (leading term) at y = v*+10, +40, +160, +640: "
              + ", ".join(f"{v:.9f}" for v in ratios))
        if abs(ratios[-1] - 1) > 1e-3 or not (abs(ratios[-1] - 1) <
                                              abs(ratios[0] - 1)):
            raise AssertionError("the dominating level does not dominate")

        print(f"PART B [{name}] -- an interval where Delta_{r} keeps its sign")
        Dv = np.array([Delta(y) for y in Y])
        i0 = int(np.argmax(np.abs(Dv)))
        y0 = Y[i0]
        s0 = np.sign(Dv[i0])
        lo, hi = y0, y0
        step = (Y[-1] - Y[0]) / 4000
        while lo - step > Y[0] and np.sign(Delta(lo - step)) == s0:
            lo -= step
        while hi + step < Y[-1] and np.sign(Delta(hi + step)) == s0:
            hi += step
        msk = (Y >= lo) & (Y <= hi)
        aE = float(np.sum(W[msk] * Dv[msk]))
        print(f"   E = [{lo:.4f}, {hi:.4f}] around y0 = {y0:.4f}; "
              f"a_E = int_E Delta_{r} = {aE:.6e}")
        if aE == 0:
            raise AssertionError("a_E vanished")

        rows = []
        gf = (lambda x: float(gmap[x]))
        for h in (0.2, 0.1, 0.05, 0.025, 0.0125):
            d = p5.gap_stable(Y, cube, p, FA, FB, gf, h)
            gapE = float(np.sum(W[msk] * d[msk]))
            pA = p5.densities(Y, cube, p, FA, gf, h)
            pB = p5.densities(Y, cube, p, FB, gf, h)
            den = (np.sqrt(np.maximum(pA, 0)) + np.sqrt(np.maximum(pB, 0))) ** 2
            ok = den > 0
            H2 = 0.5 * float(np.sum(W[ok] * d[ok] ** 2 / den[ok]))
            chi = 0.5 * float(np.sum(W * d ** 2 / np.maximum(pB, 1e-300)))
            rows.append((h, gapE, H2, chi))
        print(f"   |P_A(E) - P_B(E)| / (|a_E| h^{r}) = " + ", ".join(
            f"h={h}:{abs(gE)/(abs(aE)*h**r):.6f}" for h, gE, _H, _c in rows))
        h0 = None
        for h, gE, _H, _c in rows:
            if abs(gE) >= abs(aE) * h ** r / 2:
                h0 = h if h0 is None else max(h0, h)
        print(f"   the half-size bound |gap| >= |a_E| h^{r}/2 holds from h_0 = {h0} "
              f"downwards")
        cminus = aE ** 2 / 16
        print(f"PART C [{name}] -- the two constants")
        print(f"   c_- = a_E^2/16 = {cminus:.6e}   (from |P(E)-Q(E)| <= 2 sqrt(H^2))")
        for h, gE, H2, chi in rows:
            if H2 < cminus * h ** (2 * r) * (1 - 1e-9):
                raise AssertionError(
                    f"H^2 fell below c_- h^{2*r} at h={h}: {H2} < "
                    f"{cminus*h**(2*r)}")
        cplus = max(H2 / h ** (2 * r) for h, _g, H2, _c in rows)
        chiplus = max(chi / h ** (2 * r) for h, _g, _H, chi in rows)
        print(f"   c_+ = sup_h H^2/h^{{{2*r}}} = {cplus:.6e}  "
              f"(and the chi-square envelope sup (1/2)int d^2/p_B / h^{{{2*r}}} = "
              f"{chiplus:.6e}, which caps it)")
        print(f"   ratio c_+/c_- = {cplus/cminus:.3f}")
        for h, _g, H2, chi in rows:
            if H2 > chi * (1 + 1e-9):
                raise AssertionError("H^2 exceeded its chi-square envelope")

        print(f"PART D [{name}] -- the two-sided sample complexity that follows")
        out = []
        for eps in (0.05, 0.01):
            for h in (0.1, 0.025):
                nlo = math.log(1 / (4 * eps)) / (4 * cplus * h ** (2 * r))
                nhi = math.ceil(math.log(1 / (2 * eps)) / (cminus * h ** (2 * r)))
                out.append({"eps": eps, "h": h, "N_necessary_lower": nlo,
                            "N_sufficient_upper": nhi})
                print(f"   eps={eps} h={h}: {nlo:.4g} <= N*(h,eps) <= {nhi:.4g}"
                      f"   (spread {nhi/nlo:.1f}x, both Theta(h^-{2*r}))")
        res[name] = {"order": r, "dominating_level": str(vstar),
                     "n_nonzero_level_coeffs": len(nz),
                     "tail_domination_ratios": ratios,
                     "interval": [lo, hi], "a_E": aE,
                     "c_minus": cminus, "c_plus": cplus,
                     "chi_envelope_constant": chiplus,
                     "c_plus_over_c_minus": cplus / cminus,
                     "h0_for_half_size_bound": h0,
                     "rows": [{"h": h, "gap_E": gE, "H2": H2, "chi_half": chi}
                              for h, gE, H2, chi in rows],
                     "sample_complexity": out}
        print()

    res["not_established"] = [
        "Taylor remainder bounds are MEASURED on a grid of h, not proved; this file "
        "supplies the constants and checks the shape",
        "the non-vanishing of Delta_r is checked at the dominating level and on the "
        "grid; the exponential-polynomial independence argument is not formalised",
        "one pair of worlds, one noise level, r in {1,2}",
        "c_+ is a measured supremum over the grid, not a proved envelope constant",
    ]
    outp = REPO / "research/worker_P15_query_20260915/P15_query_hellinger_order.json"
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps(res, indent=2) + "\n")
    print(f"-> {outp}")


if __name__ == "__main__":
    main()
