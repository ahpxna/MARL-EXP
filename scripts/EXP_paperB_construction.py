#!/usr/bin/env python3
"""Paper B, steps B1/B3/B4: the family, its safe sets, and the two moment scales.

The construction is, for r >= 2 and u, v in {-1, +1},

    X = {-1,1}^{r+3},
    F_{u,v}(z) = 3u z1 - 2 z2 - 2 z3 + v * prod_{l=4}^{r+3} z_l,

with the uniform product reference, and the deployment support

    K = { (t, t, t, 1, ..., 1) : t = +-1 }.

Everything below is DERIVED from those definitions in exact rational arithmetic: the
product responses are computed as conditional expectations under the reference, the losses
are computed as half the oscillation of the retained residual on K, and the safe sets are
read off the losses.  No loss table is declared.

  B1  the loss table, and that `v` does not move the safe decision;
  B3  E[Y^2] = 18 + sigma^2 + 6 u h + h^2, so the two values of `u` sit 12h apart,
      which is the h^{-2} scale of the DECISION;
  B4  the moment contrast at order r+1 between v = +1 and v = -1, which is the
      h^{-2r} scale of IDENTIFICATION, together with the combinatorial identities
      E[chi_r g^j] = 0 (j < r) and E[chi_r g^r] = r!/r^r.

The Gaussian noise is integrated exactly through its moments, so every number here is a
fraction; nothing is sampled.
"""

import json
import math
import sys
from fractions import Fraction as Fr
from itertools import product

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def cube(n):
    return list(product((-1, 1), repeat=n))


def chi_tail(z, r):
    """prod_{l=4}^{r+3} z_l, with 0-based indices 3 .. r+2."""
    p = 1
    for l in range(3, 3 + r):
        p *= z[l]
    return p


def F(z, u, v, r):
    return Fr(3 * u * z[0] - 2 * z[1] - 2 * z[2] + v * chi_tail(z, r))


def response(j, val, u, v, r):
    """Q_j(val) = E[F | z_j = val] under the uniform product reference."""
    n = r + 3
    tot = Fr(0)
    cnt = 0
    for z in cube(n):
        if z[j] != val:
            continue
        tot += F(z, u, v, r)
        cnt += 1
    return tot / cnt


def support(r):
    n = r + 3
    out = []
    for t in (-1, 1):
        z = [t, t, t] + [1] * (n - 3)
        out.append(tuple(z))
    return out


def loss_on_K(T, u, v, r):
    """Half the oscillation on K of the residual after retaining T."""
    K = support(r)
    vals = []
    for z in K:
        res = F(z, u, v, r) - sum(response(j, z[j], u, v, r) for j in T)
        vals.append(res)
    return (max(vals) - min(vals)) / 2


def safe_set(u, v, r, eps):
    n = r + 3
    losses = {j: loss_on_K([j], u, v, r) for j in range(n)}
    best = min(losses.values())
    return frozenset(j for j in range(n) if losses[j] - best <= eps), losses


# ---------------------------------------------------------------- moments

def gauss_moment(k, sigma2):
    """E[xi^k] for xi ~ N(0, sigma2), exactly."""
    if k % 2 == 1:
        return Fr(0)
    i = k // 2
    dbl = 1
    for a in range(1, 2 * i, 2):
        dbl *= a
    return Fr(dbl) * sigma2 ** i


def moment_Y(k, u, v, r, h, sigma2, gfun):
    """E[Y^k] with Y = F + h g(Z) + xi, exactly."""
    n = r + 3
    Zs = cube(n)
    tot = Fr(0)
    for z in Zs:
        A = F(z, u, v, r) + h * gfun(z, r)
        s = Fr(0)
        for j in range(k + 1):
            s += Fr(math.comb(k, j)) * (A ** j) * gauss_moment(k - j, sigma2)
        tot += s
    return tot / len(Zs)


def g_decision(z, r):
    return Fr(z[0])


def g_ident(z, r):
    return Fr(sum(z[l] for l in range(3, 3 + r)), r)


def exact_moment_chi(r, j):
    """E[chi_r * g_ident^j] over the tail coordinates, exactly."""
    Zs = cube(r)
    tot = Fr(0)
    for z in Zs:
        c = 1
        for a in z:
            c *= a
        g = Fr(sum(z), r)
        tot += Fr(c) * g ** j
    return tot / len(Zs)


def main():
    print("=" * 76)
    print("Paper B: the family, its safe sets, and the two moment scales")
    print("=" * 76)

    # ---------------- B1
    print("\n  B1  losses on K, derived from the reference and the support")
    print("  " + "-" * 68)
    tab_ok, v_ok = True, True
    for r in [2, 3, 4]:
        for u in (-1, 1):
            for v in (-1, 1):
                l1 = loss_on_K([0], u, v, r)
                l2 = loss_on_K([1], u, v, r)
                l3 = loss_on_K([2], u, v, r)
                lj = loss_on_K([3], u, v, r)
                if not (l1 == 4 and l2 == abs(3 * u - 2) and l3 == abs(3 * u - 2)
                        and lj == abs(3 * u - 4)):
                    tab_ok = False
        for u in (-1, 1):
            s_plus, _ = safe_set(u, 1, r, Fr(1, 2))
            s_minus, _ = safe_set(u, -1, r, Fr(1, 2))
            if s_plus != s_minus:
                v_ok = False
        _, losses = safe_set(1, 1, r, Fr(1, 2))
        print(f"      r={r}, u=+1:  L({{1}})={losses[0]}  L({{2}})={losses[1]}  "
              f"L({{j>=4}})={losses[3]}")
        _, losses = safe_set(-1, 1, r, Fr(1, 2))
        print(f"      r={r}, u=-1:  L({{1}})={losses[0]}  L({{2}})={losses[1]}  "
              f"L({{j>=4}})={losses[3]}")
    check("L({1})=4, L({2})=L({3})=|3u-2|, L({j>=4})=|3u-4|, from the definitions",
          tab_ok)
    check("the interaction sign v does not move the safe set", v_ok)

    sep_ok = True
    for r in [2, 3, 4]:
        for eps in [Fr(0), Fr(1, 4), Fr(1, 2)]:
            sp, _ = safe_set(1, 1, r, eps)
            sm, _ = safe_set(-1, 1, r, eps)
            if 0 in sp or sm != frozenset({0}):
                sep_ok = False
            if len(sp & sm) != 0:
                sep_ok = False
    check("for eps < 1 the two values of u have DISJOINT safe sets", sep_ok,
          "so a safe compression rule also decides u")

    # ---------------- B3
    print("\n  B3  the decision scale: E[Y^2] under g = z1")
    print("  " + "-" * 68)
    b3_ok = True
    sigma2 = Fr(1)
    for r in [2, 3]:
        for h in [Fr(1, 4), Fr(1, 8)]:
            for u in (-1, 1):
                for v in (-1, 1):
                    got = moment_Y(2, u, v, r, h, sigma2, g_decision)
                    want = 18 + sigma2 + 6 * u * h + h * h
                    if got != want:
                        b3_ok = False
                        print(f"      MISMATCH r={r} h={h} u={u} v={v}: {got} vs {want}")
    check("E[Y^2] = 18 + sigma^2 + 6 u h + h^2, exactly", b3_ok)
    h = Fr(1, 8)
    gap = (moment_Y(2, 1, 1, 2, h, sigma2, g_decision)
           - moment_Y(2, -1, 1, 2, h, sigma2, g_decision))
    check("the two values of u are 12h apart in the second moment", gap == 12 * h,
          f"gap = {gap} = 12*{h}")

    # ---------------- B4 combinatorics
    print("\n  B4  the identification scale: moments of the tail character")
    print("  " + "-" * 68)
    comb_ok = True
    rows = []
    for r in [2, 3, 4, 5, 6]:
        below = [exact_moment_chi(r, j) for j in range(1, r)]
        at = exact_moment_chi(r, r)
        want = Fr(math.factorial(r), r ** r)
        ok = all(b == 0 for b in below) and at == want
        comb_ok = comb_ok and ok
        rows.append({"r": r, "E_chi_g_r": str(at), "predicted": str(want), "match": ok})
        print(f"      r={r}: E[chi g^j]=0 for j<r  and  E[chi g^r]={at} "
              f"= r!/r^r={want}   {'match' if ok else 'MISMATCH'}")
    check("E[chi_r g^j] = 0 for j < r, and E[chi_r g^r] = r!/r^r", comb_ok)

    # ---------------- B4 moment contrast in Y
    print("\n  B4  the moment contrast at order r+1, and its leading coefficient")
    print("  " + "-" * 68)
    lead_ok = True
    contrast_rows = []
    for r in [2, 3]:
        coefs = []
        for h in [Fr(1, 8), Fr(1, 16), Fr(1, 32)]:
            d = (moment_Y(r + 1, 1, 1, r, h, sigma2, g_ident)
                 - moment_Y(r + 1, 1, -1, r, h, sigma2, g_ident))
            coefs.append((h, d, d / h ** r))
        pred = 2 * (r + 1) * Fr(math.factorial(r), r ** r)
        # the ratio must tend to the predicted leading coefficient
        closest = coefs[-1][2]
        ok = abs(float(closest) - float(pred)) < 0.02 * float(pred)
        lead_ok = lead_ok and ok
        contrast_rows.append({"r": r, "predicted_leading": str(pred),
                              "ratios": [str(c[2]) for c in coefs]})
        print(f"      r={r}: contrast/h^r at h=1/8,1/16,1/32 = "
              f"{', '.join(str(float(c[2]))[:8] for c in coefs)}"
              f"   -> predicted {float(pred):.6f}")
    check("the order-(r+1) moment contrast has leading term 2(r+1) r!/r^r h^r",
          lead_ok, "ratio converges to the predicted coefficient as h decreases")

    # the contrast is genuinely of order h^r, not lower
    ord_ok = True
    for r in [2, 3]:
        d1 = (moment_Y(r + 1, 1, 1, r, Fr(1, 8), sigma2, g_ident)
              - moment_Y(r + 1, 1, -1, r, Fr(1, 8), sigma2, g_ident))
        d2 = (moment_Y(r + 1, 1, 1, r, Fr(1, 16), sigma2, g_ident)
              - moment_Y(r + 1, 1, -1, r, Fr(1, 16), sigma2, g_ident))
        ratio = float(d1 / d2)
        if abs(ratio - 2 ** r) > 0.08 * 2 ** r:
            ord_ok = False
        print(f"      r={r}: halving h divides the contrast by {ratio:.3f} "
              f"(2^r = {2**r})")
    check("halving h divides the contrast by 2^r, so the order is exactly r", ord_ok)

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 76)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 76)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperB_construction.py").read_bytes()).hexdigest(),"moment_identity": rows, "contrast": contrast_rows,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperB_construction.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
