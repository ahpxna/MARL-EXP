#!/usr/bin/env python3
"""P27 -- Functional: an EXACT RATIONAL certificate that `w*` is not optimal.

`P23` found designs beating `w*` with Nelder-Mead.  A search cannot certify an
optimum -- but it does not have to.  To prove `w*` is NOT a maximiser one only needs
ONE feasible design with a strictly larger value, and that can be checked exactly.

This script takes P23's incumbent, rationalises it, renormalises it to sum to exactly
`1`, and evaluates both designs in `Fraction` arithmetic:

    J(w) = min over ORDERED pairs (a,b) of distinct outsider cells of
           pairV(wI0, wI1, w_a/sigma_a, w_b/sigma_b, mean_a - mean_b).

Every input is rational: `n` is a perfect square so `d = c/sqrt(n)` is rational, the
middle means are rational, and so are `g_i = 1/2 - |z_i|`, `S`, `A` and `w*`.  So
`J(w_rat) > J(w*)` is an exact inequality, and it settles the question on its own:
**`w*` is not a maximiser.**  The VALUE of `sup_w J(w)` is still only a search result
and is not claimed.

Lean counterpart: `LeanFunctionalDesignOptimalityV1.optimal_iff_no_better_direction`
(`w` is a maximiser exactly when no design beats it -- so one witness refutes it).
"""
import json, os
from fractions import Fraction as F

OUT = "research/worker_P27_functional_20260915"
SRC = "research/worker_P23_functional_20260915/P23_functional_design_optimum.json"


def pairV(u, v, pa, pb, D):
    den = 2 * (u * v * (pa + pb) + pa * pb * (u + v))
    if den <= 0:
        return None
    return u * v * (pa * pb) * (1 - D) ** 2 / den


def Jvalue(w, mean, sig):
    """exact min over ordered pairs of distinct OUTSIDER cells (indices 2..)."""
    wI0, wI1 = w[0], w[1]
    prec = [w[i] / sig[i] for i in range(2, len(w))]
    m = mean[2:]
    best = None
    for a in range(len(m)):
        for b in range(len(m)):
            if a == b:
                continue
            v = pairV(wI0, wI1, prec[a], prec[b], m[a] - m[b])
            if v is None:
                return None
            if best is None or v < best:
                best = v
    return best


def setup(n, c):
    """exactly the configuration P23 builds, in Fractions.  n must be a perfect square."""
    r = int(round(n ** 0.5))
    assert r * r == n, f"n={n} is not a perfect square"
    d = F(c) / r
    gmin = d / 2 * F(8, 5)                       # the 1.6 factor P23 uses
    hi = F(1, 2) - gmin
    if n == 1:
        mid = [F(0)]
    else:
        mid = [-hi + (2 * hi * F(i, n - 1)) for i in range(n)]
    vr = [F(1)] * n
    mean = [F(-1, 2), F(1, 2), (1 - d) / 2, -((1 - d) / 2)] + mid
    sig = [F(1), F(1), F(1), F(1)] + vr
    g = [F(1, 2) - abs(z) for z in mid]
    S = sum(vr[i] / g[i] ** 2 for i in range(n))
    A = F(1) / (16 + d ** 2 * S)
    w = [4 * A, 4 * A, 4 * A, 4 * A] + [d ** 2 * vr[i] * A / g[i] ** 2 for i in range(n)]
    tot = sum(w)
    w = [x / tot for x in w]
    return mean, sig, w, A, S, d, g


def main():
    os.makedirs(OUT, exist_ok=True)
    src = json.load(open(SRC))
    rows = []
    for r23 in src["rows"]:
        n, c = r23["n"], r23["c"]
        mean, sig, ws, A, S, d, g = setup(n, c)
        # domain check: every middle cell must satisfy g_i >= d/2
        in_domain = all(gi >= d / 2 for gi in g)
        Jstar = Jvalue(ws, mean, sig)
        # rationalise P23's incumbent and renormalise to sum exactly 1
        wf = [F(x).limit_denominator(10 ** 7) for x in r23["w_opt"]]
        wf = [max(x, F(1, 10 ** 9)) for x in wf]
        tot = sum(wf)
        wr = [x / tot for x in wf]
        assert sum(wr) == 1
        Jrat = Jvalue(wr, mean, sig)
        beats = (Jrat > Jstar)
        gap = Jrat - Jstar
        rows.append({
            "n": n, "c": c, "d": str(d), "in_domain_g_ge_d_over_2": in_domain,
            "J_wstar_exact": str(Jstar),
            "J_wstar_float": float(Jstar),
            "J_witness_exact": str(Jrat),
            "J_witness_float": float(Jrat),
            "gap_exact": str(gap), "gap_float": float(gap),
            "ratio": float(Jrat / Jstar),
            "witness_budget_sums_to_one": True,
            "witness_strictly_beats_wstar": bool(beats),
            "witness_weights": [str(x) for x in wr],
        })
        mark = "CERTIFIED" if beats else "   --    "
        print(f"  n={n:3d} c={c}: J(w*)={float(Jstar):.10e}  "
              f"J(witness)={float(Jrat):.10e}  ratio={float(Jrat/Jstar):.8f}  {mark}"
              + ("" if in_domain else "   [OUT OF DOMAIN]"))

    ncert = sum(1 for r in rows if r["witness_strictly_beats_wstar"] and
                r["in_domain_g_ge_d_over_2"])
    nind = sum(1 for r in rows if r["in_domain_g_ge_d_over_2"])
    out = {
        "script": "P27_functional_suboptimal_certificate.py",
        "claim": "w* is NOT a maximiser of J over the budget simplex",
        "method": "one feasible rational design with a strictly larger value, both "
                  "evaluated in exact Fraction arithmetic.  No optimiser is trusted.",
        "certified_cells": ncert, "in_domain_cells": nind, "total_cells": len(rows),
        "rows": rows,
        "not_established": [
            "The VALUE of sup_w J(w) is NOT certified: the witness is a lower bound for "
            "it, nothing more.  P23's numbers for sup_w J remain a search result.",
            "J is taken to be the min over ordered pairs, which equals the infimum over "
            "flipping alternatives by energyU_ge_pairV plus the endpoint witness -- not "
            "by assumption.",
            "The witness is P23's incumbent rationalised at denominator 1e7 and "
            "renormalised; any feasible rational design with a larger value would do.",
        ],
        "consequence": "Gamma* = sup_w J(w) must NOT be written for "
                       "c^2/(n(32 + 2c^2 H_n)); that formula is the value AT w*.",
        "lean": "LeanFunctionalDesignOptimalityV1.optimal_iff_no_better_direction",
    }
    path = os.path.join(OUT, "P27_functional_suboptimal_certificate.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nexact-rational certificates that w* is beaten: {ncert}/{nind} in-domain cells")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
