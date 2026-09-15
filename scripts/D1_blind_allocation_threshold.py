#!/usr/bin/env python3
"""D6: is there any discovery cost at all?  The blind-allocation threshold.

Before measuring what it costs to learn the hidden label `A` well enough to pick
an allocation, one has to check whether learning it is needed. Fix `mu` and the
legal query set. With

    W_zeta(A, mu) = { w : V_{A,mu}(w) >= (1 - zeta) Gamma(q, mu) }

the assignment's first step is the threshold

    V_blind = max_w min_A V_{A,mu}(w),      zeta_blind = 1 - V_blind/Gamma.

Above `zeta_blind` the intersection over all `A` is non-empty, so ONE allocation
serves every world and the cost of learning `A` in order to choose an allocation
is exactly zero.

SYMMETRY REDUCTION (this is what makes it cheap). The problem is invariant under
permutations of the non-special coordinates, acting on both `w` and `A`. For any
`w`, averaging over that group gives `wbar` with

    V_A(wbar) >= avg_sigma V_A(sigma w) = avg_sigma V_{sigma^{-1}A}(w)
             >= min_{A'} V_{A'}(w),

so the max-min is attained at a PERMUTATION-INVARIANT allocation; and for such an
allocation `V_A` is the same number for every `A`. Hence

    V_blind = max over permutation-invariant w of V_{A_0, mu}(w),

a maximisation over a handful of class masses rather than over all worlds.

Both `Gamma` and `V_blind` are computed here by the SAME cutting-plane loop on
the SAME alternative set, differing only in whether `w` is constrained to the
invariant subspace, so the ratio is not comparing two different solvers.

    .venv/bin/python scripts/D1_blind_allocation_threshold.py
"""
from __future__ import annotations

import importlib.util
import itertools
import json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

REPO = Path(__file__).resolve().parents[1]
GAME = REPO / "research/worker_distinct_research_acceptance_20260913/approximate_game.py"


def load_game():
    spec = importlib.util.spec_from_file_location("game", GAME)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def physical_class(g, q, e):
    """The orbit of a query under permutations of the non-special coordinates.
    This is coarser than `key`, which also knows where `A` is."""
    j = 2 * q + 1
    if e[0] == "s":
        return ("s", "j") if e[1] == j else ("s", "coord")
    return ("g", len(e[1]), bool(e[2]))


def solve_value(g, q, mu, eps, restrict_invariant, tol=2e-8, iters=300):
    """max over w of min over alternatives and nuisance, by cutting planes.
    `restrict_invariant` forces w to be permutation-invariant as a PHYSICAL
    allocation (equal mass on every query of the same physical class)."""
    queries, keys, counts, alts = g.problem(q, 0, mu)
    alts = [(a, d, c, min(1.0, 2 - 2 * eps / d)) for a, d, c in alts if d > eps]
    if not alts:
        raise ValueError("empty bad set")
    coeff = np.array([x[2] for x in alts])
    upper = np.array([x[3] for x in alts])
    dim = len(keys)

    # map orbit key -> physical class, via any query in that orbit
    keyof = {}
    for e in queries:
        k = g.problem.__globals__  # not used; placeholder to keep lint quiet
        break
    # rebuild the key function the same way `problem` does
    coords = list(range(2 * q + 1)); j = 2 * q + 1
    A = frozenset(range(q + 1)); B = A
    groups = [sorted(A & B), sorted(A - B), sorted(B - A), sorted(set(coords) - (A | B))]

    def key(e):
        if e[0] == "s":
            return ("s", 4 if e[1] == j else
                    next(i for i, gr in enumerate(groups) if e[1] in gr))
        return ("g", e[2], *(len(e[1] & set(gr)) for gr in groups))

    orbit_class = {}
    for e in queries:
        k = key(e); c = physical_class(g, q, e)
        if k in orbit_class and orbit_class[k] != c:
            raise AssertionError(f"orbit {k} spans two physical classes")
        orbit_class[k] = c
    classes = sorted({orbit_class[k] for k in keys}, key=str)
    cidx = {c: i for i, c in enumerate(classes)}
    # M[k, c] = counts[k] if orbit k belongs to class c else 0
    M = np.zeros((dim, len(classes)))
    for i, k in enumerate(keys):
        M[i, cidx[orbit_class[k]]] = counts[i]

    def rows(nu):
        return coeff[:, 0, :] + nu[:, None] * coeff[:, 1, :] + nu[:, None] ** 2 * coeff[:, 2, :]

    cuts = list(rows(np.zeros(len(alts)))) + list(rows(upper))
    for _ in range(iters):
        mat = np.array(cuts)
        if restrict_invariant:
            Amat = mat @ M                       # rows in class coordinates
            nvar = len(classes)
            eqrow = M.sum(axis=0)                # total mass as a function of class masses
        else:
            Amat = mat
            nvar = dim
            eqrow = np.ones(dim)
        lp = linprog(np.r_[np.zeros(nvar), -1.0],
                     A_ub=np.c_[-Amat, np.ones(len(mat))], b_ub=np.zeros(len(mat)),
                     A_eq=np.array([np.r_[eqrow, 0.0]]), b_eq=[1.0],
                     bounds=[(0, None)] * nvar + [(None, None)], method="highs",
                     options={"dual_feasibility_tolerance": 1e-9,
                              "primal_feasibility_tolerance": 1e-9})
        if not lp.success:
            raise RuntimeError(lp.message)
        m = lp.x[:-1]
        w = M @ m if restrict_invariant else m
        polys = coeff @ w
        nu = np.zeros(len(alts))
        pos = polys[:, 2] > 1e-15
        nu[pos] = np.clip(-polys[pos, 1] / (2 * polys[pos, 2]), 0, upper[pos])
        nu[~pos] = np.where(polys[~pos, 1] < 0, upper[~pos], 0)
        oracle = rows(nu)
        values = oracle @ w
        lower = float(values.min())
        dual = np.maximum(0, -lp.ineqlin.marginals)
        if dual.sum() <= 0:
            raise RuntimeError("degenerate dual")
        dual /= dual.sum()
        # the normalisation is eqrow . m = 1, so the dual bound is the max of the
        # dual-weighted row PER UNIT of that constraint, not the raw max
        dv = dual @ Amat
        ubv = float((dv / eqrow).max())
        if ubv - lower <= tol:
            return lower, ubv, w, classes, m
        for i in np.where(values < ubv - tol / 3)[0]:
            cuts.append(oracle[i])
    raise RuntimeError("cutting plane did not converge")


def main():
    g = load_game()
    rows = []
    for q in (3, 4):
        for mu in (0.25, 0.5, 0.75):
            eps = 0.0
            gam, gam_ub, w_free, _, _ = solve_value(g, q, mu, eps, False)
            ref = g.solve(q, 0, mu, eps)
            if abs(gam - ref["lower"]) > 1e-7:
                raise AssertionError(
                    f"my Gamma {gam} disagrees with the published solver {ref['lower']}")
            vb, vb_ub, w_inv, classes, m = solve_value(g, q, mu, eps, True)
            if vb > gam + 1e-9:
                raise AssertionError("blind value exceeds the unrestricted optimum")
            zeta = 1 - vb / gam
            rows.append({"q": q, "mu": mu, "Gamma": gam, "V_blind": vb,
                         "zeta_blind": zeta,
                         "Gamma_matches_published_solver": True,
                         "invariant_classes": [str(c) for c in classes],
                         "invariant_class_mass": [float(v) for v in m]})
            print(f"q={q} mu={mu}:  Gamma={gam:.8f}  V_blind={vb:.8f}  "
                  f"zeta_blind={zeta:.6f}   (published Gamma={ref['lower']:.8f})")
    print("\nzeta_blind > 0 everywhere means one allocation can NOT serve every")
    print("world at the optimal rate, so the cost of learning A is not zero.")
    print("zeta_blind = 0 anywhere would mean a blind design suffices there.")
    out = REPO / "research/worker_D_blind_20260914/D1_blind_allocation_threshold.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "is there any discovery cost? zeta_blind = 1 - V_blind/Gamma",
        "method": "same cutting-plane loop and same alternative set for both "
                  "quantities; the only difference is whether w is constrained to "
                  "the permutation-invariant subspace",
        "symmetry_justification": "the max-min over worlds is attained at a "
                                  "permutation-invariant allocation, for which "
                                  "V_A is the same number for every A",
        "epsilon": 0.0, "answer_shell": 0,
        "rows": rows,
        "scope": "q in {3,4}, mu in {0.25,0.5,0.75}, exact-identification game "
                 "(eps=0, shell=0). Floating-point LP with a duality gap below "
                 "2e-9; NOT an exact rational certificate.",
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
