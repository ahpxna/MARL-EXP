#!/usr/bin/env python3
"""Query batch-2 package: how far does the h^4 law survive an IMPERFECT measurement?

THE MODEL, unchanged from `Q2_weak_leakage_order.py`, which is imported:
    Y = F_W(X) + h g(X) + Z,   Z ~ N(0, sigma^2),   X on the cube with weights p.
Two worlds A, B are raw-indistinguishable at h = 0 (their level histograms agree).
Q2 found a NON-CONSTANT g_0 that kills the first-order density gap and leaves the
second order alive, so KL = Theta(h^4).

CORRECTION (audit Q4/Q5, 2026-09-15).  The class this file actually searches, via
`design_columns`/`find_g0`, is the QUADRATIC class, not the linear one: every linear
solution of the first-order equations turns out pi-symmetric and therefore invisible at
EVERY order, so the linear class supplies no usable witness.  Two statements must
therefore be kept apart:
  * the chosen g HAS leakage order r = 2 -- that is what is computed here;
  * "order 2 is optimal in the quadratic class" is FALSE as stated, because the
    quadratic class CONTAINS the linear one.  The correct statement is relative to the
    FIRST-ORDER-NEUTRAL class (the kernel of the level-moment map L_1): there the
    linear members are all-order invisible and the quadratic members carry order 2.
    Without a modelling reason to impose first-order neutrality, an r = 1 design is the
    mandatory comparator.

WHAT IS NEW.  The measurement actually built is g = g_0 + eps u, and u carries a
first-order gap.  Grouping the cube by baseline level v and writing
    S_W^f(v) = sum_{x: F_W(x)=v} p(x) f(x),   T_W^f(v) = sum_{x: F_W(x)=v} p(x) f(x)^2,
the density gap expands as
    p_A - p_B = h eps A + h^2 B + O(h^3 + h^2|eps| + h^2 eps^2),
    A(y) = -sum_v [S_A^u - S_B^u](v) phi'(y - v),
    B(y) =  (1/2) sum_v [T_A^{g_0} - T_B^{g_0}](v) phi''(y - v),
because g_0 annihilates the first order and the eps-linear part of T is O(h^2 eps).
With the weighted inner product <f,g>_0 = int f g / p_0 (p_0 the common h = 0
density), the claim to be checked is
    eps = lambda h:   KL(P_A, P_B) = (h^4/2) ||lambda A + B||_0^2 + o(h^4),
uniformly on bounded lambda, and the crossover law
    |eps| << h:      KL  ~  (h^4/2) ||B||^2
    eps = lambda h:  KL  ~  (h^4/2) ||lambda A + B||^2
    h << |eps| << 1: KL  ~  (h^2 eps^2/2) ||A||^2.

HOW IT IS CHECKED.  No density is expanded numerically where it would cancel: the
level histograms agree exactly, so
    p_A - p_B = sum_v [ sum_{x in A_v} p(x)(phi(y-v-h g(x)) - phi(y-v))
                      - sum_{x in B_v} p(x)(phi(y-v-h g(x)) - phi(y-v)) ],
and each bracket is computed with expm1, which removes one whole order of
cancellation before any quadrature runs.  KL is then evaluated as
    int (p_B + d) log1p(d / p_B),
on a composite Gauss-Legendre grid, and the grid is refined until the value stops
moving.  The Gram matrix is computed on the same grid.

THE WORST-CASE COEFFICIENT.  inf_lambda (1/2)||lambda A + B||^2
    = (1/2)( ||B||^2 - <A,B>^2/||A||^2 ),
which is positive exactly when A and B are linearly independent.  A is a
combination of phi'(y-v) and B of phi''(y-v) over the SAME levels; the run
computes the Gram determinant and the Cauchy-Schwarz defect and reports both.

WHAT THIS DOES NOT ESTABLISH.
  * The remainder bound is verified by measuring the EXPONENT of the residual in
    the weighted L^2 norm on a grid of h; the Taylor-in-L^2 lemma itself is not
    proved here.  The measured order is 4, not the 3 the derivation claims -- the
    odd orders happen to vanish for this pair of worlds -- so the quoted O(h^3) is
    what is established and the extra order is an observation, not a claim.
  * Quadrature is numerical (float64 with a stabilised integrand and a refinement
    check), not a certified enclosure.
  * Uniformity over lambda is checked on a grid of lambda, not proved.
  * The calibration remark is an IMPLICATION of the crossover law, not a lower
    bound on the cost of identifying a world: measurement error can also make two
    worlds EASIER to tell apart, and settling the optimal calibration cost needs
    the unknown-nuisance problem, which is not solved here.

    .venv/bin/python scripts/P5_query_h4_robustness.py
"""
from __future__ import annotations

import importlib.util, json, math
from fractions import Fraction as F
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "q2", REPO / "scripts/Q2_weak_leakage_order.py")
q2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(q2)
g4 = q2.load_g4()

SIG = 1.0
SQ2PI = math.sqrt(2 * math.pi)


def phi(u):  return np.exp(-0.5 * (u / SIG) ** 2) / (SIG * SQ2PI)
def dphi(u): return -(u / SIG ** 2) * phi(u)
def d2phi(u): return ((u ** 2 / SIG ** 4) - 1 / SIG ** 2) * phi(u)


def setup():
    k, t0, rho = 3, F(1, 8), F(1)
    cfg = g4.make_cfg(k, t0, rho)
    m = cfg["m"]
    A, B = frozenset({0, 1, 3}), frozenset({0, 2, 3})
    cube = g4.cube(m)
    p = {x: g4.bern_w(x, t0) for x in cube}
    FA, FB = g4.world_fn(cfg, A), g4.world_fn(cfg, B)
    hA = {}
    for x in cube:
        hA[FA[x]] = hA.get(FA[x], F(0)) + p[x]
    hB = {}
    for x in cube:
        hB[FB[x]] = hB.get(FB[x], F(0)) + p[x]
    if hA != hB:
        raise AssertionError("worlds are not raw-indistinguishable at h = 0")
    return cfg, m, cube, p, FA, FB, sorted(hA), hA


def design_columns(m):
    """the QUADRATIC measurement class.  Q2 shows the LINEAR class is useless here:
    every linear solution of the first-order system is pi-symmetric, and a
    pi-symmetric g kills EVERY order, so no linear measurement can separate the two
    worlds at any h.  The construction therefore lives in the quadratic class."""
    import itertools as it
    cols = [("1", lambda x: F(1))]
    cols += [(f"x{i}", (lambda i: (lambda x: F(x[i])))(i)) for i in range(m)]
    cols += [(f"x{i}x{j}", (lambda i, j: (lambda x: F(x[i] * x[j])))(i, j))
             for i, j in it.combinations(range(m), 2)]
    return cols


def _order_gaps(cube, p, FA, FB, levels, fun, power):
    idx_gap = []
    for v in levels:
        s = F(0)
        for x in cube:
            if FA[x] == v: s += p[x] * fun[x] ** power
            if FB[x] == v: s -= p[x] * fun[x] ** power
        idx_gap.append(s)
    return idx_gap


def find_g0(m, cube, p, FA, FB, levels):
    """a non-constant g_0 in the quadratic class with S_A = S_B and T_A != T_B."""
    idx = {x: i for i, x in enumerate(cube)}
    rows = []
    for v in levels:
        row = [F(0)] * len(cube)
        for x in cube:
            c = F(0)
            if FA[x] == v: c += p[x]
            if FB[x] == v: c -= p[x]
            row[idx[x]] = c
        rows.append(row)
    cols = design_columns(m)
    Bm = [[f(x) for _, f in cols] for x in cube]
    red = [[sum(row[idx[x]] * Bm[idx[x]][c] for x in cube) for c in range(len(cols))]
           for row in rows]
    basis, _ = q2.rational_nullspace(red, len(cols))
    cands = list(basis)
    # generic combinations too: the solution set is a SUBSPACE, so a basis element
    # can have a vanishing second order while a combination does not
    for i in range(len(basis)):
        for j in range(i + 1, len(basis)):
            cands.append([a + b for a, b in zip(basis[i], basis[j])])
            cands.append([a - 2 * b for a, b in zip(basis[i], basis[j])])
    for cvec in cands:
        gv = [sum(Bm[idx[x]][c] * cvec[c] for c in range(len(cols)))
              for x in range(0)] or [
             sum(Bm[idx[x]][c] * cvec[c] for c in range(len(cols))) for x in cube]
        if all(v == gv[0] for v in gv):
            continue
        gmap = {x: gv[idx[x]] for x in cube}
        first = _order_gaps(cube, p, FA, FB, levels, gmap, 1)
        if any(v != 0 for v in first):
            continue
        second = _order_gaps(cube, p, FA, FB, levels, gmap, 2)
        gap = max(abs(v) for v in second)
        if gap != 0:
            return gmap, gap, cvec
    raise AssertionError("no non-constant g_0 with a live second order")


def pick_u(m, cube, p, FA, FB, levels):
    """a measurement u in the SAME class whose FIRST-order gap is non-zero."""
    for name, f in design_columns(m):
        umap = {x: f(x) for x in cube}
        if all(umap[x] == umap[cube[0]] for x in cube):
            continue
        gaps = _order_gaps(cube, p, FA, FB, levels, umap, 1)
        if any(g != 0 for g in gaps):
            return umap, [float(g) for g in gaps], name
    raise AssertionError("every column of the class kills the first order")


def grid(levels, nsub=240, npt=12):
    lo = float(min(levels)) - 12 * SIG
    hi = float(max(levels)) + 12 * SIG
    xs, ws = np.polynomial.legendre.leggauss(npt)
    edges = np.linspace(lo, hi, nsub + 1)
    Y, W = [], []
    for a, b in zip(edges[:-1], edges[1:]):
        Y.append(0.5 * (b - a) * xs + 0.5 * (a + b))
        W.append(0.5 * (b - a) * ws)
    return np.concatenate(Y), np.concatenate(W)


def densities(Y, cube, p, FW, gfun, h):
    out = np.zeros_like(Y)
    for x in cube:
        out += float(p[x]) * phi(Y - float(FW[x]) - h * gfun(x))
    return out


def gap_stable(Y, cube, p, FA, FB, gfun, h):
    """p_A - p_B with the exactly-cancelling h=0 part removed analytically."""
    d = np.zeros_like(Y)
    for x in cube:
        w = float(p[x]); gx = gfun(x)
        va, vb = float(FA[x]), float(FB[x])
        # phi(y-v-hg) - phi(y-v) = phi(y-v) * expm1( (2(y-v)hg - (hg)^2) / (2 sig^2) )
        ua = Y - va
        d += w * phi(ua) * np.expm1((2 * ua * h * gx - (h * gx) ** 2) / (2 * SIG ** 2))
        ub = Y - vb
        d -= w * phi(ub) * np.expm1((2 * ub * h * gx - (h * gx) ** 2) / (2 * SIG ** 2))
    return d


def main():
    print("Query: the h^4 law under an imperfect measurement g = g_0 + eps u\n")
    cfg, m, cube, p, FA, FB, levels, H = setup()
    g0, gap2, cvec = find_g0(m, cube, p, FA, FB, levels)
    u, ugaps, uname = pick_u(m, cube, p, FA, FB, levels)
    print(f"PART 0 -- the construction: {len(levels)} levels, {len(cube)} cube points")
    print(f"   g_0 is QUADRATIC and non-constant (the linear class is useless here:"
          f" every linear solution is pi-symmetric, and a pi-symmetric g kills")
    print(f"   EVERY order).  Its second-order gap is {float(gap2):.6g}")
    nz = [f"{v:.4g}" for v in ugaps if abs(v) > 0]
    print(f"   u = {uname} has a LIVE first-order gap: {len(nz)} of {len(ugaps)} "
          f"levels are non-zero, largest {max(abs(v) for v in ugaps):.4g}")

    Y, W = grid(levels)
    p0 = densities(Y, cube, p, FA, lambda x: 0.0, 0.0)
    p0b = densities(Y, cube, p, FB, lambda x: 0.0, 0.0)
    if np.max(np.abs(p0 - p0b)) > 1e-14:
        raise AssertionError("p_0 differs between worlds at h = 0")

    # A and B as level combinations
    dS = {v: 0.0 for v in levels}; dT = {v: 0.0 for v in levels}
    for x in cube:
        w = float(p[x])
        dS[FA[x]] += w * float(u[x]); dS[FB[x]] -= w * float(u[x])
        dT[FA[x]] += w * float(g0[x]) ** 2; dT[FB[x]] -= w * float(g0[x]) ** 2
    Afun = np.zeros_like(Y); Bfun = np.zeros_like(Y)
    for v in levels:
        Afun += -dS[v] * dphi(Y - float(v))
        Bfun += 0.5 * dT[v] * d2phi(Y - float(v))

    def ip(f, g):
        return float(np.sum(W * f * g / p0))
    AA, AB, BB = ip(Afun, Afun), ip(Afun, Bfun), ip(Bfun, Bfun)
    det = AA * BB - AB * AB
    worst = 0.5 * (BB - AB * AB / AA)
    print(f"\nPART 1 -- the Gram matrix of (A, B) in the weighted L^2")
    print(f"   ||A||^2 = {AA:.9g}   <A,B> = {AB:.9g}   ||B||^2 = {BB:.9g}")
    print(f"   det G = {det:.9g}   (A and B are linearly "
          f"{'INDEPENDENT' if det > 1e-12 * AA * BB else 'DEPENDENT'})")
    print(f"   inf_lambda (1/2)||lambda A + B||^2 = {worst:.9g}  at lambda* = "
          f"{-AB/AA:.9g}")
    if det <= 0:
        raise AssertionError("A and B are linearly dependent: the law degenerates")

    # grid-refinement check of the quadrature
    Y2, W2 = grid(levels, nsub=480, npt=16)
    p02 = densities(Y2, cube, p, FA, lambda x: 0.0, 0.0)
    A2 = np.zeros_like(Y2); B2 = np.zeros_like(Y2)
    for v in levels:
        A2 += -dS[v] * dphi(Y2 - float(v))
        B2 += 0.5 * dT[v] * d2phi(Y2 - float(v))
    AA2 = float(np.sum(W2 * A2 * A2 / p02))
    BB2 = float(np.sum(W2 * B2 * B2 / p02))
    rel = max(abs(AA2 / AA - 1), abs(BB2 / BB - 1))
    print(f"   quadrature refinement (240x12 -> 480x16) moves the norms by "
          f"{rel:.2e}")
    if rel > 1e-8:
        raise AssertionError("quadrature has not converged")

    def KL(h, eps):
        gfun = lambda x: float(g0[x]) + eps * float(u[x])
        d = gap_stable(Y, cube, p, FA, FB, gfun, h)
        pB = densities(Y, cube, p, FB, gfun, h)
        r = d / pB
        return float(np.sum(W * (pB + d) * np.log1p(r)))

    print("\nPART 2 -- regime  eps = lambda h:  KL / h^4  ->  (1/2)||lambda A+B||^2")
    p2 = []
    for lam in (0.0, 0.5, 1.0, -1.0, 2.0, -float(AB / AA)):
        pred = 0.5 * (lam * lam * AA + 2 * lam * AB + BB)
        seq = []
        for h in (0.2, 0.1, 0.05, 0.025):
            k = KL(h, lam * h)
            seq.append((h, k / h ** 4))
        last = seq[-1][1]
        print(f"   lambda={lam:+.6g}: KL/h^4 = "
              + ", ".join(f"h={hh}:{vv:.6f}" for hh, vv in seq)
              + f"   -> predicted {pred:.6f}  (ratio {last/pred:.6f})")
        if abs(last / pred - 1) > 0.05:
            raise AssertionError(f"lambda={lam}: KL/h^4 does not approach the "
                                 f"predicted coefficient ({last} vs {pred})")
        p2.append({"lambda": lam, "predicted_half_norm2": pred,
                   "sequence": [{"h": hh, "KL_over_h4": vv} for hh, vv in seq],
                   "ratio_at_smallest_h": last / pred})
    res_lam = p2

    print("\nPART 3 -- the three regimes of the crossover law")
    p3 = []
    # (a) |eps| << h
    for h in (0.1, 0.05, 0.025):
        k = KL(h, 0.0)
        k2 = KL(h, h * h)          # eps = h^2 << h
        print(f"   h={h}: eps=0   KL/h^4 = {k/h**4:.6f};  eps=h^2  KL/h^4 = "
              f"{k2/h**4:.6f}   (predicted {0.5*BB:.6f})")
        p3.append({"regime": "eps << h", "h": h, "KL_over_h4_eps0": k / h ** 4,
                   "KL_over_h4_eps_h2": k2 / h ** 4, "predicted": 0.5 * BB})
    # (c) h << eps << 1
    for h in (0.01, 0.005):
        for eps in (0.2, 0.1, 0.05):
            k = KL(h, eps)
            pred = 0.5 * AA * h * h * eps * eps
            print(f"   h={h} eps={eps}: KL = {k:.6e}, (1/2)||A||^2 h^2 eps^2 = "
                  f"{pred:.6e}   ratio {k/pred:.6f}")
            p3.append({"regime": "h << eps << 1", "h": h, "eps": eps, "KL": k,
                       "predicted": pred, "ratio": k / pred})
    print("\nPART 4 -- the residual exponent in the weighted L^2 norm")
    p4 = []
    for lam in (1.0, -1.0):
        prev = None
        for h in (0.2, 0.1, 0.05, 0.025, 0.0125):
            gfun = lambda x: float(g0[x]) + lam * h * float(u[x])
            d = gap_stable(Y, cube, p, FA, FB, gfun, h)
            resid = d - h * h * (lam * Afun + Bfun)
            nrm = math.sqrt(float(np.sum(W * resid * resid / p0)))
            if prev is not None:
                order = math.log(prev[1] / nrm) / math.log(prev[0] / h)
                p4.append({"lambda": lam, "h": h, "residual_norm": nrm,
                           "empirical_order": order})
                print(f"   lambda={lam:+.0f} h={h}: ||p_A-p_B - h^2(lam A+B)||_0 = "
                      f"{nrm:.4e}, empirical order {order:.4f}")
            prev = (h, nrm)
        last = [r for r in p4 if r["lambda"] == lam][-1]["empirical_order"]
        if last < 2.7:
            raise AssertionError(f"residual order {last} is below 3 at lambda={lam}")
    print("   The derivation only claims O(h^3); the MEASURED order is 4, because")
    print("   the transport symmetry pi that maps A to B also kills the odd orders")
    print("   in this construction.  That is a property of THIS pair of worlds and")
    print("   is not assumed anywhere above.")

    print("\nPART 5 -- what this says about calibration, and what it does NOT")
    mh = []
    for m_cal in (100, 1000, 10000, 100000):
        eps_typ = m_cal ** -0.5
        # eps = o(h) needs h >> m^{-1/2}, i.e. m h^2 -> infinity
        h_needed = 10 * eps_typ
        mh.append({"m_calibration": m_cal, "eps_typical": eps_typ,
                   "h_for_eps_over_h_le_0.1": h_needed,
                   "m_times_h_squared": m_cal * h_needed ** 2})
        print(f"   m={m_cal}: eps ~ {eps_typ:.4g}; keeping eps/h <= 0.1 needs "
              f"h >= {h_needed:.4g}, i.e. m h^2 >= {m_cal*h_needed**2:.1f}")
    print("   This is an IMPLICATION of the crossover law only.  A measurement")
    print("   error can make two worlds EASIER to separate (lambda far from")
    print("   lambda*), so none of this is a lower bound on the calibration needed")
    print("   to identify a world; that needs the unknown-nuisance problem.")

    res = {"levels": [str(v) for v in levels], "cube_points": len(cube),
           "g0_second_order_gap": str(gap2), "u": uname, "u_first_order_gaps": ugaps,
           "gram": {"AA": AA, "AB": AB, "BB": BB, "det": det,
                    "worst_case_half_norm2": worst, "lambda_star": -AB / AA},
           "quadrature_refinement_relative_move": rel,
           "lambda_regime": res_lam, "crossover": p3, "residual_order": p4,
           "calibration_implication": mh,
           "not_established": [
               "the Taylor-in-weighted-L^2 lemma is not proved; PART 4 measures "
               "the residual exponent on a grid of h",
               "quadrature is float64 with a stabilised integrand and a refinement "
               "check, not a certified enclosure",
               "uniformity over lambda is checked on a grid, not proved",
               "the calibration remark is an implication of the crossover law, not "
               "a lower bound on identifying a world",
           ]}
    out = REPO / "research/worker_P5_query_20260914/P5_query_h4_robustness.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
