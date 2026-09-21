#!/usr/bin/env python3
"""Paper B: the Hellinger orders on the REAL construction, not a stand-in.

An earlier run measured Hellinger distances for a different family -- the top character on
`{-1,1}^n` probed by block queries.  The paper's construction is

    F_{u,v}(z) = 3u z1 - 2 z2 - 2 z3 + v * prod_{l=4}^{r+3} z_l,
    Y = F_{u,v}(Z) + h g(Z) + xi,   xi ~ N(0, sigma^2),   Z latent,

and the two orders the paper claims are about THAT law.  This script computes them there.

Both observation laws are finite Gaussian mixtures with `2^(r+3)` components, so the squared
Hellinger distance is obtained by deterministic quadrature of the exact densities -- no
sampling.  To avoid the catastrophic cancellation of `1 - affinity` when the two laws are
close, the integrand is written as the squared difference of square roots divided by their
sum.

Two pairs are measured, and they are the two the paper distinguishes:

  DECISION pair   (u = +1 vs u = -1), probe `g = z1`      -- predicted order `h^2`;
  IDENTIFICATION  (v = +1 vs v = -1), tail query          -- predicted order `h^(2r)`.

The reported evidence is the fitted log-log slope against the orders proved in
`LeanUnifiedQueryOrderV1` (vanishing) and `LeanPaperBAttainmentV1` (attainment).
"""

import json
import math
import sys
from itertools import product

import numpy as np

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def cube(n):
    return np.array(list(product((-1.0, 1.0), repeat=n)))


def means(Z, u, v, r, h, mode):
    tail = Z[:, 3:3 + r].prod(axis=1)
    F = 3 * u * Z[:, 0] - 2 * Z[:, 1] - 2 * Z[:, 2] + v * tail
    g = Z[:, 0] if mode == "decision" else Z[:, 3:3 + r].sum(axis=1) / r
    return F + h * g


def density(ys, mu, sigma):
    d = (ys[None, :] - mu[:, None]) / sigma
    return np.exp(-0.5 * d * d).sum(axis=0) / (len(mu) * sigma * math.sqrt(2 * math.pi))


def hellinger_sq(r, h, sigma, pair, mode, half=16.0, npts=400001):
    Z = cube(r + 3)
    if pair == "decision":
        mu1 = means(Z, +1, +1, r, h, mode)
        mu2 = means(Z, -1, +1, r, h, mode)
    else:
        mu1 = means(Z, +1, +1, r, h, mode)
        mu2 = means(Z, +1, -1, r, h, mode)
    lo = min(mu1.min(), mu2.min()) - half
    hi = max(mu1.max(), mu2.max()) + half
    ys = np.linspace(lo, hi, npts)
    p = density(ys, mu1, sigma)
    q = density(ys, mu2, sigma)
    den = np.sqrt(p) + np.sqrt(q)
    rt = np.divide(p - q, den, out=np.zeros_like(p), where=den > 0)
    return 0.5 * float(np.trapezoid(rt * rt, ys))


def main():
    print("=" * 78)
    print("Paper B: Hellinger orders on the construction the paper actually uses")
    print("=" * 78)
    sigma = 1.0
    rows, ok_all = [], True

    for r in (2, 3):
        print(f"\n  r = {r}, worlds on {{-1,1}}^{r+3}")
        print("  " + "-" * 70)
        hs = np.array([0.30, 0.24, 0.19, 0.15, 0.12])
        h2d = np.array([hellinger_sq(r, float(h), sigma, "decision", "decision")
                        for h in hs])
        h2i = np.array([hellinger_sq(r, float(h), sigma, "ident", "ident") for h in hs])
        gd = h2d > 1e-16
        gi = h2i > 1e-16
        sd = np.polyfit(np.log(hs[gd]), np.log(h2d[gd]), 1)[0]
        si = np.polyfit(np.log(hs[gi]), np.log(h2i[gi]), 1)[0]
        print(f"      decision pair  (u=+1 vs u=-1), probe z1 : slope {sd:6.3f}"
              f"   predicted 2")
        print(f"      identification (v=+1 vs v=-1), tail     : slope {si:6.3f}"
              f"   predicted {2*r}")
        rows.append({"r": r, "h": hs.tolist(), "H2_decision": h2d.tolist(),
                     "H2_ident": h2i.tolist(), "slope_decision": float(sd),
                     "slope_ident": float(si)})
        ok_d = abs(sd - 2) < 0.25
        ok_i = abs(si - 2 * r) < 0.35 * r
        ok_all = ok_all and ok_d and ok_i
        check(f"r={r}: the decision pair separates at order h^2", ok_d,
              f"slope {sd:.3f}")
        check(f"r={r}: the identification pair separates at order h^{2*r}", ok_i,
              f"slope {si:.3f}")

    check("on the real family the two orders are different, and in the right direction",
          all(row["slope_ident"] > row["slope_decision"] + 1.0 for row in rows))

    # The separation is a property of the QUERY, not only of the worlds: probing with
    # z1 leaves the identification pair not merely higher-order but EXACTLY
    # indistinguishable, because flipping v is a measure-preserving relabelling of the
    # tail coordinates and z1 is independent of them.
    print("\n  the orders are query-specific, not world-specific")
    print("  " + "-" * 70)
    cross = []
    for r in (2, 3):
        hs = [0.30, 0.20, 0.14]
        vals = [hellinger_sq(r, float(h), sigma, "ident", "decision") for h in hs]
        worst = max(abs(v) for v in vals)
        cross.append({"r": r, "max_H2_ident_under_z1": worst,
                      "slope_ident_under_tail": rows[r - 2]["slope_ident"]})
        print(f"      r={r}: identification pair under probe z1 : max H^2 = {worst:.2e}"
              f"   (tail query gives slope {rows[r-2]['slope_ident']:.3f})")
    check("probing with z1 leaves v EXACTLY invisible, not merely higher order",
          all(c["max_H2_ident_under_z1"] < 1e-12 for c in cross),
          "so the order is a property of the query class, not only of the worlds")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperB_hellinger_real.py").read_bytes()).hexdigest(),"rows": rows, "cross": cross, "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperB_hellinger_real.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
