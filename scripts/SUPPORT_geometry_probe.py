#!/usr/bin/env python3
"""SUPPORT probe 1/2 -- exact geometry verification.

Replicates, in exact rational arithmetic, the *literal* Lean definitions of

    CIGAMF.V4.SupportGeometry.maxVal / minVal / osc / sumComponent
                             / supportOsc / selectedRadius
    CIGAMF.P13.SupportMultiTipGeometry.support / point / components
    CIGAMF.P13.SupportUnboundedObstruction.tip

(see work/p13_conjectures/LeanSupportGeometryV4.lean L18-24, L309-319, L489-490
and work/p13_conjectures/LeanSupportMultiTipGeometryV1.lean L14-22)

and then checks three things:

  (G0) REGRESSION.  The heterogeneous correlated family defined below contains
       the *existing* multi-tip family as the exact special case
       (Dirac kernel rho=0, height h_w = m-1).  The point vectors must be
       LITERALLY EQUAL to `tip w`, not merely produce the same radius.

  (G1) RADIUS LAW.  For the new family,
           selectedRadius (components W) {j}  ==  (max_{w in W} phi(j,w)) / 2
       exactly, for every W and j on an exhaustive small grid.
       (phi(j,w) = h_w * f(d_m(j,w)) is the correlation kernel.)

  (G2) PHYSICAL QUERY.  The membership query is unchanged:
           gtip a  in  support W   <->   a in W
       i.e. the points are pairwise distinct and none of them is 0.
       This is a CHECK, not an assumption: it is reported per-instance and
       the script prints the instances where it FAILS (there are some --
       see the degenerate-kernel report at the bottom).

Everything is fractions.Fraction; there is no floating point anywhere, so
no residual to report.

Run:  python3 scripts/SUPPORT_geometry_probe.py
"""
from fractions import Fraction as Fr
from itertools import combinations, product
import sys

# ---------------------------------------------------------------- Lean mirror

def maxVal(vals):
    return max(vals)

def minVal(vals):
    return min(vals)

def osc(vals):
    return maxVal(vals) - minVal(vals)

def sumComponent(T, pt):
    """T : set of coordinate indices; pt : list of coordinate values."""
    return sum((pt[j] for j in T), Fr(0))

def selectedRadius(points, m, selected):
    """selectedRadius f S = supportOsc S^c f / 2 = osc (sumComponent S^c f) / 2.

    `points` is the image of `components W`, i.e. the finite family of support
    points (including the zero point).  Lean takes osc over the index type
    `Points W`; ranging over the list of points is the same multiset."""
    T = [j for j in range(m) if j not in selected]
    return osc([sumComponent(T, p) for p in points]) / 2

# -------------------------------------------------------- the existing family

def tip(m, w):
    """CIGAMF.P13.SupportUnboundedObstruction.tip :  1 - if j=w then m-1 else 0"""
    return [Fr(1) - (Fr(m - 1) if j == w else Fr(0)) for j in range(m)]

def support_existing(m, W):
    """insert 0 (W.image tip)  -- the existing multi-tip support."""
    pts = [[Fr(0)] * m]
    for w in sorted(W):
        pts.append(tip(m, w))
    return pts

# ------------------------------------------------- the new correlated family

def cyc(m, a, b):
    d = abs(a - b) % m
    return min(d, m - d)

def tent(rho):
    """f(d) = max(0, rho+1-d).  rho=0 is the Dirac kernel of the old family."""
    return lambda d: Fr(max(0, rho + 1 - d))

def phi(m, ker, h, j, w):
    return h[w] * ker(cyc(m, j, w))

def gtip(m, ker, h, w):
    """P_w j = c_w - phi(j,w)  with  c_w = (sum_i phi(i,w)) / (m-1).

    The constant c_w is forced, not chosen: it is exactly the value that makes
    the residual   sum_{i != j} P_w i   equal to phi(j,w)."""
    Phi = sum((phi(m, ker, h, i, w) for i in range(m)), Fr(0))
    c = Fr(Phi, 1) / Fr(m - 1)
    return [c - phi(m, ker, h, j, w) for j in range(m)]

def support_new(m, ker, h, W):
    pts = [[Fr(0)] * m]
    for w in sorted(W):
        pts.append(gtip(m, ker, h, w))
    return pts

def predicted_radius(m, ker, h, W, j):
    if not W:
        return Fr(0)
    return max(phi(m, ker, h, j, w) for w in W) / 2

# ------------------------------------------------------------------- checks

def check_G0(ms):
    """The new family with rho=0, h_w = m-1 IS the old family, vector-wise."""
    bad = []
    for m in ms:
        ker = tent(0)
        h = [Fr(m - 1)] * m
        for w in range(m):
            if gtip(m, ker, h, w) != tip(m, w):
                bad.append((m, w, gtip(m, ker, h, w), tip(m, w)))
    return bad

def check_G1(m, ker, h, max_s=None):
    """Exhaustive over all W (up to max_s) and all j."""
    mism = 0
    total = 0
    sizes = range(0, m + 1) if max_s is None else range(0, max_s + 1)
    for s in sizes:
        for W in combinations(range(m), s):
            pts = support_new(m, ker, h, set(W))
            for j in range(m):
                got = selectedRadius(pts, m, {j})
                want = predicted_radius(m, ker, h, set(W), j)
                total += 1
                if got != want:
                    mism += 1
                    if mism <= 3:
                        print(f"    MISMATCH m={m} W={W} j={j} got={got} want={want}")
    return total, mism

def check_G2(m, ker, h):
    """gtip injective and never 0  => physical membership query is unchanged."""
    vecs = [tuple(gtip(m, ker, h, w)) for w in range(m)]
    zero = tuple([Fr(0)] * m)
    inj = len(set(vecs)) == m
    nonzero = all(v != zero for v in vecs)
    return inj, nonzero

# --------------------------------------------------------------------- main

def main():
    print("=" * 74)
    print("SUPPORT geometry probe -- exact rational arithmetic (no floats)")
    print("=" * 74)

    print("\n[G0] regression: new family (rho=0, h=m-1) == existing `tip` family")
    bad = check_G0(range(2, 13))
    if bad:
        print("    FAIL", bad[:3])
        sys.exit(1)
    print("    PASS for m = 2..12 : point vectors are literally equal")

    print("\n[G0b] regression: existing family's own radius law reproduced")
    # LeanSupportMultiTipGeometryV1.radius_formula :
    #   selectedRadius (components W) {j} = if j in W then (m-1)/2 else 0
    bad2 = 0
    for m in range(2, 9):
        for s in range(0, m + 1):
            for W in combinations(range(m), s):
                pts = support_existing(m, W)
                for j in range(m):
                    got = selectedRadius(pts, m, {j})
                    want = Fr(m - 1, 2) if j in W else Fr(0)
                    if got != want:
                        bad2 += 1
    print(f"    radius_formula mismatches over m=2..8, all W, all j : {bad2}")
    if bad2:
        sys.exit(1)

    print("\n[G1] new correlated family: selectedRadius == max_w phi(j,w) / 2")
    for m, rho in [(7, 1), (8, 1), (9, 2), (10, 2), (11, 3)]:
        ker = tent(rho)
        h = [Fr(1)] * m
        max_s = 3 if m >= 10 else None
        total, mism = check_G1(m, ker, h, max_s)
        tag = "all W" if max_s is None else f"|W|<={max_s} (grid SHRUNK for time)"
        print(f"    m={m:2d} rho={rho} homogeneous h=1 : {total:6d} cases, "
              f"{mism} mismatches   [{tag}]")
        if mism:
            sys.exit(1)

    print("\n[G1-het] HETEROGENEOUS heights (this is the family of record)")
    for m, rho in [(9, 2), (10, 2), (11, 3), (12, 3)]:
        ker = tent(rho)
        # alternating heights: even positions tall, odd positions short
        h = [Fr(1) if w % 2 == 0 else Fr(1, 2) for w in range(m)]
        total, mism = check_G1(m, ker, h, max_s=3)
        print(f"    m={m:2d} rho={rho} h=[1,1/2,...] : {total:6d} cases, "
              f"{mism} mismatches   [|W|<=3, grid SHRUNK for time]")
        if mism:
            sys.exit(1)

    print("\n[G2] physical membership query unchanged (gtip injective, nonzero)")
    print("     -- this check CAN fail; degenerate cases are printed.")
    fails = []
    for m in range(3, 13):
        for rho in range(0, 6):
            for hname, h in [("hom", [Fr(1)] * m),
                             ("het", [Fr(1) if w % 2 == 0 else Fr(1, 2)
                                      for w in range(m)])]:
                ker = tent(rho)
                inj, nz = check_G2(m, ker, h)
                if not (inj and nz):
                    fails.append((m, rho, hname, inj, nz))
    print(f"    instances tested: {10*6*2};  failures: {len(fails)}")
    for f in fails:
        print(f"      DEGENERATE m={f[0]} rho={f[1]} h={f[2]} "
              f"injective={f[3]} nonzero={f[4]}")
    print("    (rho >= floor(m/2) makes the kernel saturate the cycle; the")
    print("     family is only claimed for 2*rho+1 < m, see the findings file.)")

    print("\n[G3] the epsilon-safe set really MOVES with epsilon")
    m, rho = 11, 3
    ker = tent(rho)
    h = [Fr(1)] * m
    W = {0, 5}
    pts = support_new(m, ker, h, W)
    rad = [selectedRadius(pts, m, {j}) for j in range(m)]
    print(f"    m={m} rho={rho} W={sorted(W)}")
    print(f"    radius by coordinate j: {[str(r) for r in rad]}")
    for k in range(0, 2 * (rho + 1) + 1):
        eps = Fr(k, 2)
        safe = [j for j in range(m) if rad[j] <= eps]
        print(f"      eps={str(eps):>4} -> safe set {safe}  (|safe|={len(safe)})")
    print("    Distinct safe sets across epsilon:",
          len({tuple(j for j in range(m) if rad[j] <= Fr(k, 2))
               for k in range(0, 2 * (rho + 1) + 1)}))

    print("\nALL GEOMETRY CHECKS COMPLETE")

if __name__ == "__main__":
    main()
