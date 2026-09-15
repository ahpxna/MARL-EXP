#!/usr/bin/env python3
"""Q-weak-leakage: the order at which a perturbed raw measurement starts to
separate two worlds that are raw-indistinguishable at h = 0.

Measurement:  Y_h = F_A(X) + h g(X) + Z,  Z ~ N(0, sigma^2),  g PUBLIC and the
same in every world.  Density

    p_{A,h}(y) = sum_x p(x) phi_sigma(y - F_A(x) - h g(x)).

Differentiating at h = 0 and grouping the cube by the baseline level:

    d/dh  [p_A - p_B](y)        = -sum_v (S_A(v) - S_B(v)) phi'(y - v)
    d2/dh2[p_A - p_B](y)/2      =  (1/2) sum_v (T_A(v) - T_B(v)) phi''(y - v)

with  S_W(v) = sum_{x : F_W(x) = v} p(x) g(x)  and  T_W(v) = sum_{...} p(x) g(x)^2.
The shifted Gaussian derivatives at distinct levels are linearly independent, so

    order r >= 2  <=>  S_A == S_B on every level,
    order r  = 2  <=>  additionally T_A != T_B on some level,

and `KL(P_{A,h}, P_{B,h}) = Theta(h^{2r})`.  Both conditions are exact rational
computations on the cube -- no density is ever integrated numerically.

The first condition is a LINEAR system in g.  Constants always solve it and are
useless (a constant `h g` shifts both worlds identically, so every order
vanishes), so the question is whether a NON-CONSTANT g solves it, and within
which measurement class.

Raises on any inconsistency.   .venv/bin/python scripts/Q2_weak_leakage_order.py
"""
from __future__ import annotations

import importlib.util
import itertools
import json
from fractions import Fraction as F
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
G4 = REPO / "scripts" / "G4_fixed_world_observation_classes.py"


def load_g4():
    spec = importlib.util.spec_from_file_location("g4", G4)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def rational_nullspace(rows, ncols):
    """Exact nullspace basis of a rational matrix given as a list of rows."""
    M = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(ncols):
        pr = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        inv = F(1) / M[r][c]
        M[r] = [v * inv for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
        if r == len(M):
            break
    free = [c for c in range(ncols) if c not in piv]
    basis = []
    for fc in free:
        v = [F(0)] * ncols
        v[fc] = F(1)
        for i, pc in enumerate(piv):
            v[pc] = -M[i][fc]
        basis.append(v)
    return basis, len(piv)


def main():
    g4 = load_g4()
    k, t0, rho = 3, F(1, 8), F(1)
    cfg = g4.make_cfg(k, t0, rho)
    m = cfg["m"]
    A = frozenset({0, 1, 3})
    B = frozenset({0, 2, 3})
    cube = g4.cube(m)
    p = {x: g4.bern_w(x, t0) for x in cube}
    FA = g4.world_fn(cfg, A)
    FB = g4.world_fn(cfg, B)

    # the two worlds must be raw-indistinguishable at h = 0
    def hist(Fw):
        h = {}
        for x in cube:
            h[Fw[x]] = h.get(Fw[x], F(0)) + p[x]
        return h
    hA, hB = hist(FA), hist(FB)
    if hA != hB:
        raise AssertionError("the two worlds are NOT raw-indistinguishable at h=0")
    levels = sorted(hA)
    print(f"raw laws agree at h=0: {len(levels)} levels over {len(cube)} cube points")

    idx = {x: i for i, x in enumerate(cube)}

    def first_order_rows():
        """M[v, x] = p(x) ([F_A(x)=v] - [F_B(x)=v]); kernel = first order vanishes."""
        rows = []
        for v in levels:
            row = [F(0)] * len(cube)
            for x in cube:
                c = F(0)
                if FA[x] == v:
                    c += p[x]
                if FB[x] == v:
                    c -= p[x]
                row[idx[x]] = c
            rows.append(row)
        return rows

    Mrows = first_order_rows()

    def second_order_gap(gvec):
        """max over levels of |T_A(v) - T_B(v)|; zero means order >= 3."""
        best = F(0)
        for v in levels:
            s = F(0)
            for x in cube:
                if FA[x] == v:
                    s += p[x] * gvec[idx[x]] ** 2
                if FB[x] == v:
                    s -= p[x] * gvec[idx[x]] ** 2
            if abs(s) > best:
                best = abs(s)
        return best

    def is_constant(gvec):
        return all(v == gvec[0] for v in gvec)

    # ---- measurement classes -------------------------------------------------
    def design_linear():
        cols = [("1", lambda x: F(1))]
        cols += [(f"x{i}", (lambda i: (lambda x: F(x[i])))(i)) for i in range(m)]
        return cols

    def design_quadratic():
        cols = design_linear()
        cols += [(f"x{i}x{j}", (lambda i, j: (lambda x: F(x[i] * x[j])))(i, j))
                 for i, j in itertools.combinations(range(m), 2)]
        return cols

    # ---- the transport permutation, and why some g are useless at EVERY order --
    # pi = (1 2) maps A to B, fixes the product reference and the target set, so
    # F_B(x) = F_A(pi x) and p(pi x) = p(x). Hence
    #     S_B^g(v) = S_A^{g o pi}(v)   and   T_B^g(v) = T_A^{g^2 o pi}(v),
    # so a pi-SYMMETRIC g has S_A = S_B and T_A = T_B -- and the same argument
    # applies to every power of g, so EVERY order vanishes. Such a g can never
    # separate the worlds, however large h is. Those are the useless solutions.
    pi = {1: 2, 2: 1}
    def act(x):
        return tuple(x[pi.get(i, i)] for i in range(m))
    # verify the transport identity exactly, on the whole cube
    for x in cube:
        if FB[x] != FA[act(x)]:
            raise AssertionError(f"transport identity fails at {x}")
        if p[act(x)] != p[x]:
            raise AssertionError("the reference is not pi-invariant")
    print("transport identity F_B(x) = F_A(pi x) verified on all "
          f"{len(cube)} cube points; pi = (1 2)")

    def sym_dim_on_cube():
        fixed = sum(1 for x in cube if act(x) == x)
        return (len(cube) + fixed) // 2

    results = {}
    for cname, cols in (("linear", design_linear()),
                        ("quadratic", design_quadratic()),
                        ("all functions on the cube", None)):
        if cols is None:
            rows, ncol = Mrows, len(cube)
            tocube = lambda v: v
        else:
            Bm = [[f(x) for _, f in cols] for x in cube]           # 64 x d
            rows = [[sum(row[idx[x]] * Bm[idx[x]][c] for x in cube)
                     for c in range(len(cols))] for row in Mrows]
            ncol = len(cols)
            tocube = lambda cvec: [sum(Bm[idx[x]][c] * cvec[c] for c in range(len(cols)))
                                   for x in cube]
        basis, rank = rational_nullspace(rows, ncol)
        nonconst = []
        for v in basis:
            gv = tocube(v)
            if not is_constant(gv):
                nonconst.append(gv)
        # a non-constant solution with a non-zero second order?
        witness = None
        for gv in nonconst:
            gap = second_order_gap(gv)
            if gap != 0:
                witness = (gv, gap)
                break
        if witness is None and len(nonconst) >= 2:
            for a, b in itertools.combinations(nonconst[:6], 2):
                gv = [x + y for x, y in zip(a, b)]
                gap = second_order_gap(gv)
                if gap != 0:
                    witness = (gv, gap)
                    break
        # how much of the kernel is the useless pi-symmetric part?
        sym_in_kernel = 0
        asym_surviving = []
        for v in basis:
            gv = tocube(v)
            if all(gv[idx[x]] == gv[idx[act(x)]] for x in cube):
                sym_in_kernel += 1
            else:
                asym_surviving.append(gv)
        # every pi-symmetric g must be in the kernel; check that directly
        for v in basis:
            gv = tocube(v)
            if all(gv[idx[x]] == gv[idx[act(x)]] for x in cube):
                if second_order_gap(gv) != 0:
                    raise AssertionError(
                        "a pi-symmetric g separated at second order, contradicting "
                        "the transport identity")
        results[cname] = {
            "dimension": ncol, "rank_of_first_order_system": rank,
            "kernel_dimension": len(basis),
            "pi_symmetric_kernel_basis_elements": sym_in_kernel,
            "kernel_elements_breaking_pi_symmetry": len(asym_surviving),
            "non_constant_kernel_elements": len(nonconst),
            "order_two_witness_found": witness is not None,
            "max_second_order_gap": str(witness[1]) if witness else None,
        }
        print(f"  kernel splits: {sym_in_kernel} pi-symmetric (useless at every "
              f"order) + {len(asym_surviving)} breaking pi-symmetry")
        print(f"\n[{cname}]  dim={ncol}  rank={rank}  kernel dim={len(basis)}  "
              f"non-constant kernel elements={len(nonconst)}")
        if witness:
            print(f"  ORDER 2: a non-constant g kills the first order and leaves "
                  f"second-order gap {witness[1]} = {float(witness[1]):.6e}")
        elif len(asym_surviving) == 0:
            print("  every solution is pi-symmetric, hence useless at EVERY order "
                  "-> r = 1 for every g in this class that can separate at all")
        else:
            print("  solutions breaking pi-symmetry exist but the ones tried also "
                  "kill the second order -> order >= 3 there")
        results[cname]["verdict"] = (
            "r=2 attainable" if witness else
            "the first-order condition is exactly pi-symmetry in this class, and a "
            "pi-symmetric g separates at NO order: r=1 for every usable g"
            if len(asym_surviving) == 0 else "order >= 3 on the elements tried")

    out = REPO / "research/worker_Q_leakage_20260914/Q2_weak_leakage_order.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "config": {"k": k, "t0": str(t0), "rho": str(rho),
                   "A": sorted(A), "B": sorted(B), "cube_points": len(cube),
                   "distinct_levels": len(levels)},
        "criterion": "order r>=2 iff sum_{F_A=v} p g = sum_{F_B=v} p g for every "
                     "level v; r=2 iff additionally the g^2 sums differ somewhere",
        "arithmetic": "exact Fraction; nullspace by rational Gaussian elimination",
        "classes": results,
        "scope": "one pair of worlds at k=3, t0=1/8. Nothing is claimed for other "
                 "pairs, other k, or other measurement classes. KL = Theta(h^{2r}) "
                 "is the reading of the expansion, NOT verified here: no density is "
                 "integrated and no remainder is bounded.",
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
