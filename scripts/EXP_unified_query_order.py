#!/usr/bin/env python3
"""Measurement degree: exact moments and numerical Hellinger quadrature.

Construction (sec 5 of the unified batch).  Latent Z ~ Unif{-1,1}^n, the top
character chi(Z) = prod_i Z_i, and two worlds

    F_pm(Z) = (L/2)(1 +- chi(Z)).

An admissible query picks a polynomial g with deg(g) <= d and ||g||_inf <= 1
and returns only

    Y = F_pm(Z) + h g(Z) + xi,    xi ~ N(0, sigma^2),

with Z latent, a fresh Z each measurement, and no amplification of g by 1/h.

Writing s = ceil(n/d), the claims are

  (1) E[chi g^j] = 0 for every admissible g and every j < s, because
      deg(g^j) <= j d <= (s-1) d < n, and chi is the degree-n character;
  (2) the block query g = (1/s) sum_l prod_{i in B_l} Z_i is admissible and
      achieves E[chi g^s] = s! / s^s != 0;
  (3) the predicted squared-Hellinger order is h^{2s}. Quadrature diagnoses this
      on tested cells; it does not establish uniform bounds or adaptive sample complexity.

(1) and (2) are checked in EXACT integer arithmetic over the whole cube.
(3) is investigated by deterministic floating-point quadrature of finite Gaussian
mixtures. The measured log-log slope is compared against 2s. Tail and grid errors
are not certified, so this is numerical evidence, not an exact Hellinger result.

This is deliberately positioned against the masking literature: the mechanism
"higher algebraic degree pushes the first informative moment up, and the sample
cost with it" is NOT claimed as new.  What is checked here is the exact order
law for this admissible class, which is what the downstream decision cost uses.
"""

import json
import math
import sys
from fractions import Fraction as Fr
from itertools import product

import numpy as np


# ---------------------------------------------------------------- exact part

def cube_pm(n):
    return list(product((-1, 1), repeat=n))


def chi(z):
    p = 1
    for v in z:
        p *= v
    return p


def blocks(n, d):
    """Partition [n] into s = ceil(n/d) blocks of size <= d."""
    s = -(-n // d)
    out, i = [], 0
    for b in range(s):
        take = min(d, n - i)
        # spread the remainder so every block is non-empty and <= d
        out.append(list(range(i, i + take)))
        i += take
    # rebalance so no block is empty
    out = [b for b in out if b]
    return out


def block_query(n, d):
    """g(Z) = (1/s) sum_l prod_{i in B_l} Z_i -- degree <= d, sup-norm <= 1."""
    B = blocks(n, d)
    s = len(B)

    def g(z):
        tot = 0
        for blk in B:
            p = 1
            for i in blk:
                p *= z[i]
            tot += p
        return Fr(tot, s)
    return g, s, B


def exact_moment(n, g, j):
    """E[chi(Z) g(Z)^j] in exact rational arithmetic."""
    tot = Fr(0)
    Zs = cube_pm(n)
    for z in Zs:
        tot += Fr(chi(z)) * (g(z) ** j)
    return tot / len(Zs)


def random_admissible(n, d, rng, scale=1.0):
    """A random polynomial of degree <= d, rescaled to sup-norm <= 1."""
    terms = []
    for r in range(0, d + 1):
        for S in product(range(n), repeat=r):
            if len(set(S)) == r:
                terms.append(tuple(sorted(set(S))))
    terms = sorted(set(terms))
    coef = {S: Fr(int(rng.integers(-4, 5)), 4) for S in terms}

    def raw(z):
        tot = Fr(0)
        for S, c in coef.items():
            p = 1
            for i in S:
                p *= z[i]
            tot += c * p
        return tot
    sup = max(abs(raw(z)) for z in cube_pm(n))
    if sup == 0:
        return None, 0
    return (lambda z: raw(z) / sup), sup


# ------------------------------------------------------------ quadrature part

def mixture_density(ys, n, g, sign, L, h, sigma):
    """Exact finite Gaussian mixture density of Y under world `sign`."""
    Zs = cube_pm(n)
    acc = np.zeros_like(ys)
    for z in Zs:
        mu = L / 2.0 * (1 + sign * chi(z)) + h * float(g(z))
        acc += np.exp(-0.5 * ((ys - mu) / sigma) ** 2)
    return acc / (len(Zs) * sigma * math.sqrt(2 * math.pi))


def hellinger_sq(n, g, L, h, sigma, half_width=14.0, npts=200001):
    ys = np.linspace(-half_width, L + half_width, npts)
    p = mixture_density(ys, n, g, +1, L, h, sigma)
    q = mixture_density(ys, n, g, -1, L, h, sigma)
    # Integrate the squared root difference, not 1 - affinity (catastrophic
    # cancellation when the affinity is near one). This remains numerical.
    denom = np.sqrt(p) + np.sqrt(q)
    root_diff = np.divide(p - q, denom, out=np.zeros_like(p), where=denom > 0)
    return 0.5 * float(np.trapezoid(root_diff * root_diff, ys))


CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def main():
    print("=" * 74)
    print("Query degree: exact moments and numerical Hellinger quadrature")
    print("=" * 74)
    rng = np.random.default_rng(20260919)

    # ---- claim (0): the arithmetic that drives everything
    arith = all((-(-n // d) - 1) * d < n
                for n in range(1, 40) for d in range(1, n + 1))
    check("s = ceil(n/d) satisfies (s-1) d < n for all 1 <= d <= n < 40", arith)

    print("\n  (1) moment vanishing below the order, exact over the cube")
    print("  " + "-" * 68)
    van_rows, van_ok = [], True
    for (n, d) in [(4, 1), (4, 2), (6, 2), (6, 3), (8, 2), (8, 4), (9, 3)]:
        s = -(-n // d)
        worst = Fr(0)
        for _ in range(12):
            g, _ = random_admissible(n, d, rng)
            if g is None:
                continue
            for j in range(1, s):
                m = exact_moment(n, g, j)
                worst = max(worst, abs(m))
                if m != 0:
                    van_ok = False
        van_rows.append({"n": n, "d": d, "s": s, "worst_abs_moment": str(worst)})
        print(f"      n={n} d={d} s={s}:  max_j<s |E[chi g^j]| over 12 random "
              f"admissible g = {worst}")
    check("E[chi g^j] = 0 exactly, for every random admissible g and j < s",
          van_ok)

    print("\n  (2) the block query attains the order")
    print("  " + "-" * 68)
    att_rows, att_ok = [], True
    for (n, d) in [(4, 1), (4, 2), (6, 2), (6, 3), (8, 2), (8, 4), (9, 3),
                   (10, 5), (12, 4)]:
        g, s, B = block_query(n, d)
        sup = max(abs(g(z)) for z in cube_pm(n))
        below = [exact_moment(n, g, j) for j in range(1, s)]
        at = exact_moment(n, g, s)
        want = Fr(math.factorial(s), s ** s)
        ok = (sup <= 1 and all(m == 0 for m in below) and at == want)
        att_ok = att_ok and ok
        att_rows.append({"n": n, "d": d, "s": s, "sup_norm": str(sup),
                         "E_chi_g_s": str(at), "predicted": str(want),
                         "blocks": [len(b) for b in B]})
        print(f"      n={n} d={d} s={s}: ||g||_inf={sup}  "
              f"E[chi g^s]={at}  predicted s!/s^s={want}  {'match' if at==want else 'MISMATCH'}")
    check("block query is admissible (deg <= d, sup-norm <= 1)",
          all(Fr(r["sup_norm"]) <= 1 for r in att_rows))
    check("block query kills every moment below s and hits s!/s^s at s", att_ok)

    print("\n  (3) Hellinger order by deterministic quadrature")
    print("  " + "-" * 68)
    hell_rows, slope_ok = [], True
    for (n, d) in [(4, 2), (4, 1), (6, 3), (6, 2)]:
        g, s, _ = block_query(n, d)
        L, sigma = 1.0, 1.0
        hs = np.array([0.30, 0.24, 0.19, 0.15, 0.12, 0.095, 0.075])
        h2 = np.array([hellinger_sq(n, g, L, float(h), sigma) for h in hs])
        good = h2 > 1e-15
        slope = np.polyfit(np.log(hs[good]), np.log(h2[good]), 1)[0]
        ok = abs(slope - 2 * s) < 0.16
        slope_ok = slope_ok and ok
        hell_rows.append({"n": n, "d": d, "s": s, "slope": float(slope),
                          "predicted_slope": 2 * s,
                          "h": hs.tolist(), "H2": h2.tolist()})
        print(f"      n={n} d={d} s={s}: measured log-log slope of H^2 vs h = "
              f"{slope:6.3f}   predicted 2s = {2*s}")
    check("tested numerical Hellinger slopes are within tolerance of 2s", slope_ok)

    # A control: a degree-n query (d = n, s = 1) is informative at first order.
    g1, s1, _ = block_query(4, 4)
    m1 = exact_moment(4, g1, 1)
    check("control: at d = n the very first moment is already non-zero",
          s1 == 1 and m1 != 0, f"s={s1}, E[chi g]={m1}")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 74)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 74)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_unified_query_order.py").read_bytes()).hexdigest(),"moment_evidence": "EXACT_RATIONAL_FINITE_CELLS",
           "hellinger_evidence": "NUMERICAL_QUADRATURE_UNCERTIFIED_ERROR",
           "adaptive_complexity_proved": False,
           "vanishing": van_rows, "attainment": att_rows,
           "hellinger": hell_rows, "checks": CHECKS, "all_passed": nfail == 0}
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    with open("research/unified_20260919/query_order_corrected_v2.json", "w") as f:
        json.dump(out, f, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())
