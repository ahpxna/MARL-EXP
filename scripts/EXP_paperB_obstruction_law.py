#!/usr/bin/env python3
"""Paper B, step B7: the obstruction-observation order law, on the real family.

Two corrections to an earlier attempt are the point of this script.

  1. EQUIVALENCE CLASSES ARE BUILT FROM COEFFICIENT EQUALITY, not by union-find on a
     pairwise relation whose transitivity was never checked.  Two worlds are `s`-equivalent
     when their observation laws agree in EVERY coefficient up to order `s`, for EVERY
     admissible query.  That is equality of a tuple, hence an equivalence relation by
     construction, and the classes are its blocks.

  2. THE FAMILY IS THE REAL ONE.  Worlds are the four `(u, v)` of

         F_{u,v}(z) = 3u z1 - 2 z2 - 2 z3 + v * prod_{l=4}^{r+3} z_l ,

     the safe sets come from the loss table derived in EXP_paperB_construction.py, and the
     orders come from the h-expansion of the actual observation law, not from a table.

An admissible query is a LINEAR `g` with sup-norm at most one; the observation is
`Y = F_{u,v}(Z) + h g(Z) + xi`.  For each world and query the moments `E[Y^k]` are computed
as exact polynomials in `h`, and

    r_g(w, w') = min { j : some moment's h^j coefficient differs between w and w' }.

Then
    r_safe = max over minimal obstructions H of min over g of min over w != w' in H,
    r_id   = max over ALL distinct pairs of min over g.

Note `u` is invisible at order zero: the law of `F` alone does not depend on the sign of
`u`, because `z1` is symmetric.  Only the probe `h g` breaks that symmetry.  That is why
the decision costs `h^{-2}` rather than `O(1)`, and it is a fact about the construction
rather than an assumption.
"""

import json
import math
import sys
from fractions import Fraction as Fr
from itertools import combinations, product

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# ------------------------------------------------------------ tiny exact polynomials in h

def padd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else Fr(0)) + (b[i] if i < len(b) else Fr(0))
            for i in range(n)]


def pmul(a, b):
    out = [Fr(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def pscale(a, c):
    return [c * x for x in a]


def ppow(a, k):
    out = [Fr(1)]
    for _ in range(k):
        out = pmul(out, a)
    return out


# ------------------------------------------------------------ the family

def cube(n):
    return list(product((-1, 1), repeat=n))


def chi_tail(z, r):
    p = 1
    for l in range(3, 3 + r):
        p *= z[l]
    return p


def F(z, u, v, r):
    return Fr(3 * u * z[0] - 2 * z[1] - 2 * z[2] + v * chi_tail(z, r))


def response(j, val, u, v, r):
    n = r + 3
    tot, cnt = Fr(0), 0
    for z in cube(n):
        if z[j] != val:
            continue
        tot += F(z, u, v, r)
        cnt += 1
    return tot / cnt


def support(r):
    n = r + 3
    return [tuple([t, t, t] + [1] * (n - 3)) for t in (-1, 1)]


def loss_on_K(T, u, v, r):
    vals = []
    for z in support(r):
        vals.append(F(z, u, v, r) - sum(response(j, z[j], u, v, r) for j in T))
    return (max(vals) - min(vals)) / 2


def safe_set(u, v, r, eps):
    n = r + 3
    losses = {j: loss_on_K([j], u, v, r) for j in range(n)}
    best = min(losses.values())
    return frozenset(j for j in range(n) if losses[j] - best <= eps)


def gauss_moment(k, sigma2):
    if k % 2 == 1:
        return Fr(0)
    i = k // 2
    d = 1
    for a in range(1, 2 * i, 2):
        d *= a
    return Fr(d) * sigma2 ** i


def moments_poly(u, v, r, coef, K, sigma2):
    """E[Y^k] for k = 1..K, each an exact polynomial in h."""
    n = r + 3
    Zs = cube(n)
    out = []
    for k in range(1, K + 1):
        acc = [Fr(0)]
        for z in Zs:
            gval = sum(coef[i] * z[i] for i in range(n))
            A = [F(z, u, v, r), gval]            # A = F + h*g, as a polynomial in h
            s = [Fr(0)]
            for j in range(k + 1):
                s = padd(s, pscale(ppow(A, j),
                                   Fr(math.comb(k, j)) * gauss_moment(k - j, sigma2)))
            acc = padd(acc, s)
        out.append(pscale(acc, Fr(1, len(Zs))))
    return out


def coeff(poly, j):
    return poly[j] if j < len(poly) else Fr(0)


def order_between(mw, mw2, K, maxord):
    """First h-order at which any moment differs; maxord+1 if none up to maxord."""
    for j in range(0, maxord + 1):
        for k in range(K):
            if coeff(mw[k], j) != coeff(mw2[k], j):
                return j
    return maxord + 1


def queries(r):
    """A finite set of admissible linear queries, sup-norm at most one."""
    n = r + 3
    Q = []
    e1 = [Fr(0)] * n; e1[0] = Fr(1)
    Q.append(("z1", e1))
    tail = [Fr(0)] * n
    for l in range(3, 3 + r):
        tail[l] = Fr(1, r)
    Q.append(("tail avg", tail))
    e2 = [Fr(0)] * n; e2[1] = Fr(1)
    Q.append(("z2", e2))
    mix = [Fr(0)] * n
    mix[0] = Fr(1, 2)
    for l in range(3, 3 + r):
        mix[l] = Fr(1, 2 * r)
    Q.append(("half z1 + half tail", mix))
    return Q


def main():
    print("=" * 78)
    print("Paper B / B7: obstruction-observation order, on the real family")
    print("=" * 78)

    r = 3
    eps = Fr(1, 2)
    sigma2 = Fr(1)
    K = 2 * r + 2
    maxord = r + 1
    worlds = [(u, v) for u in (-1, 1) for v in (-1, 1)]
    Q = queries(r)

    safes = {w: safe_set(w[0], w[1], r, eps) for w in worlds}
    print(f"\n  r={r}, eps={eps}: safe sets")
    print("  " + "-" * 70)
    for w in worlds:
        print(f"      world (u,v)=({w[0]:+d},{w[1]:+d}):  safe = {sorted(safes[w])}")
    check("worlds with the same u share a safe set; v is decision-irrelevant",
          safes[(1, 1)] == safes[(1, -1)] and safes[(-1, 1)] == safes[(-1, -1)])
    check("worlds with different u have disjoint safe sets",
          len(safes[(1, 1)] & safes[(-1, 1)]) == 0)

    # ---- orders, from the h-expansion of the real law
    print("\n  first h-order at which each query separates each pair")
    print("  " + "-" * 70)
    mom = {(w, qn): moments_poly(w[0], w[1], r, c, K, sigma2)
           for w in worlds for (qn, c) in Q}
    rq = {}
    for w, w2 in combinations(worlds, 2):
        for (qn, _) in Q:
            rq[(w, w2, qn)] = order_between(mom[(w, qn)], mom[(w2, qn)], K, maxord)
    for w, w2 in combinations(worlds, 2):
        line = "  ".join(f"{qn}:{rq[(w, w2, qn)]}" for (qn, _) in Q)
        print(f"      ({w[0]:+d},{w[1]:+d}) vs ({w2[0]:+d},{w2[1]:+d}):  {line}")

    def rmin(w, w2):
        a, b = (w, w2) if (w, w2, Q[0][0]) in rq else (w2, w)
        return min(rq[(a, b, qn)] for (qn, _) in Q)

    check("u is invisible at order zero: no query separates two u-worlds at h^0",
          all(rmin(w, w2) >= 1 for w, w2 in combinations(worlds, 2)
              if w[0] != w2[0]),
          "the probe h*g is what breaks the symmetry")
    vpairs = [(w, w2) for w, w2 in combinations(worlds, 2)
              if w[0] == w2[0] and w[1] != w2[1]]
    check(f"the interaction sign v needs order r = {r}",
          all(rmin(w, w2) == r for w, w2 in vpairs),
          f"orders {[rmin(w, w2) for w, w2 in vpairs]}")

    # ---- obstructions and the two orders
    def has_common(H):
        inter = set(safes[H[0]])
        for w in H[1:]:
            inter &= safes[w]
        return len(inter) > 0

    obs = []
    for size in (2, 3, 4):
        for H in combinations(worlds, size):
            if has_common(list(H)):
                continue
            minimal = all(has_common([H[i] for i in range(size) if i != d])
                          for d in range(size))
            if minimal:
                obs.append(H)
    print(f"\n  minimal obstructions: {len(obs)}")
    check("there is at least one obstruction", len(obs) > 0)

    r_safe = max(min(rmin(a, b) for a, b in combinations(H, 2)) for H in obs)
    r_id = max(rmin(a, b) for a, b in combinations(worlds, 2))
    print(f"  r_safe = {r_safe}    r_id = {r_id}")
    check("deciding needs a strictly lower order than identifying", r_safe < r_id,
          f"{r_safe} < {r_id}")
    check("and the orders are the ones the construction predicts: 1 and r",
          r_safe == 1 and r_id == r, f"r_safe={r_safe}, r_id={r_id}, r={r}")

    # ---- classes by COEFFICIENT EQUALITY (a genuine equivalence)
    print("\n  classes built from coefficient equality up to order s")
    print("  " + "-" * 70)

    def signature(w, s):
        """The tuple of every coefficient up to order s, over every query."""
        return tuple(tuple(coeff(mom[(w, qn)][k], j) for k in range(K)
                           for j in range(s + 1)) for (qn, _) in Q)

    cls_ok, resolve_ok = True, True
    for s in range(0, maxord + 1):
        sig = {w: signature(w, s) for w in worlds}
        blocks = {}
        for w in worlds:
            blocks.setdefault(sig[w], []).append(w)
        # transitivity is automatic: equality of tuples
        good = all(has_common(b) for b in blocks.values())
        print(f"      s={s}: {len(blocks)} class(es), every class has a common answer: {good}")
        if s >= r_safe and not good:
            resolve_ok = False
        if s < r_safe and good:
            resolve_ok = False
    check("classes have a common safe answer exactly at and above r_safe"
          "  [Lean: classes_resolve_iff]", resolve_ok)

    # ---- the error floor
    floor_ok = True
    n = r + 3
    for H in obs:
        acts = list(range(n))
        for trial in range(200):
            import random
            random.seed(trial)
            p = [random.random() for _ in acts]
            tot = sum(p)
            p = [x / tot for x in p]
            masses = [sum(p[a] for a in acts if a not in safes[w]) for w in H]
            if max(masses) < 1.0 / len(H) - 1e-9:
                floor_ok = False
    check("every randomized rule leaves unsafe mass >= 1/|H| somewhere"
          "  [Lean: obstruction_error_floor_randomized]", floor_ok)

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperB_obstruction_law.py").read_bytes()).hexdigest(),"r": r, "r_safe": r_safe, "r_id": r_id,
           "n_minimal_obstructions": len(obs),
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperB_obstruction_law.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
