#!/usr/bin/env python3
"""D6, the supervisor's high-risk probe F2: can ONE pair query already create a gain?

If a single width-2 joint query, with the scalar weights free to shift and absorb the
information it does not supply, already beats the best scalar-only design, then any
lower bound of the form "a design must open Omega(q) pairs" is FALSE.

METHOD, and the one thing that matters about it: the corpus's D6 solver works on the
ORBIT-REDUCED problem, where every width-2 query with the same intersection pattern
collapses into one variable. That solver therefore CANNOT distinguish one pair from a
clique of pairs, so it cannot answer this question -- and using it here would be
assuming the symmetry the question is about. This script rebuilds the per-query
coefficients from `approximate_game`'s own `affine` means, keeping every query as its
own variable, and optimises weights over a CHOSEN SUPPORT.

  I_e(alt, nu) = (mean_true(mu) - mean_alt(nu))^2 / 2,  from the module's affine map
  V(support)   = max over w >= 0 supported there, sum w = 1,
                   of  min over alternatives and nu in [0,1] of sum_e w_e I_e(alt,nu)

The weights are SEARCHED by an LP on a nu grid and then the value is RE-EVALUATED
exactly: for fixed w the map nu |-> sum_e w_e I_e(alt,nu) is a quadratic, so its
minimum on [0,1] is at an endpoint or the vertex, all three of which are checked.
The reported V is the verified one, never the LP's objective.

WHAT THIS DOES NOT ESTABLISH
 - This is the `approximate_game` model at eps = 0, shell = 0, which is the model the
   D6 solver uses. It is NOT the local phase-boundary parametrisation of
   `B1_d6_width_transition_local.py`; a pair that helps here need not help there.
 - Floating point in the LP search; the re-evaluation is closed-form but still float.
 - Only the (q, mu) cells listed.
 - A gain from one pair refutes an Omega(q) lower bound only for THIS model.

    .venv/bin/python scripts/F2_single_pair_breaks_balanced.py
"""
from __future__ import annotations

import importlib.util, itertools, json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

REPO = Path(__file__).resolve().parents[1]
GAME = REPO / "research/worker_distinct_research_acceptance_20260913/approximate_game.py"


def load_game():
    spec = importlib.util.spec_from_file_location("game", GAME)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
    return m


def per_query_coeffs(g, q, mu):
    """Returns (queries, C) with C[alt][t][e] the quadratic coefficients of
    I_e(alt, nu) = C0 + C1 nu + C2 nu^2, per INDIVIDUAL query e."""
    coords = list(range(2 * q + 1)); j = 2 * q + 1
    A = frozenset(range(q + 1))
    queries = [('s', i) for i in coords + [j]]
    queries += [('g', G, h) for r in range(q + 1)
                for G in (frozenset(x) for x in itertools.combinations(coords, r))
                for h in (False, True) if h or r >= 2]

    def affine(label, e):
        if e[0] == 's':
            i = e[1]
            return (1., 0.) if i in label else ((-1., 1.) if i == j else (1., -1.))
        k = len(e[1] - label); hh = int(e[2])
        return 1 - hh + k - hh, -(k - hh)

    true = np.array([a + b * mu for a, b in [affine(A, e) for e in queries]])
    alts = []
    # ALL alternatives of the right size, not one representative per symmetry orbit.
    # The module keeps only representatives, which is valid ONLY for a symmetric
    # allocation. Since this script deliberately breaks symmetry, using the module's
    # list would silently drop the alternatives that an asymmetric design is weak
    # against, and report a value that is too high.
    for S in itertools.combinations(coords, q + 1):
        alt = frozenset(S)
        d = len(alt - A)
        if d == 0:
            continue                       # excluded from the bad set at eps = 0
        off, slope = np.array([affine(alt, e) for e in queries]).T
        diff = true - off
        C = np.array([diff ** 2 / 2, -diff * slope, slope ** 2 / 2])
        alts.append((alt, d, C))
    return queries, alts


def quad_min_on_unit(C, B, A):
    cands = [C, C + B + A]
    if A > 0:
        v = -B / (2 * A)
        if 0.0 < v < 1.0:
            cands.append(C + B * v + A * v * v)
    return min(cands)


def verified_value(alts, idx, w):
    """min over alternatives and over ALL nu in [0,1], in closed form. No grid,
    no optimizer. This is the number that is ever reported."""
    val = None
    for (_alt, _d, C) in alts:
        c0 = float(C[0][idx] @ w); c1 = float(C[1][idx] @ w); c2 = float(C[2][idx] @ w)
        v = quad_min_on_unit(c0, c1, c2)
        if val is None or v < val:
            val = v
    return val


def value_on_support(queries, alts, support, iters=40):
    """CUTTING PLANE. A fixed nu grid is not enough: the LP optimises against the
    grid, and the off-grid re-evaluation of its w can be lower, so a larger support
    could appear WORSE than a subset -- which is impossible for a true maximum and
    was exactly the symptom the first version of this script produced. Each round
    therefore adds the EXACT worst nu of every alternative as a new cut, and the best
    VERIFIED value seen is kept."""
    idx = sorted(support)
    n = len(idx)
    cuts, rhs = [], []
    for nu in np.linspace(0.0, 1.0, 5):
        for (_alt, _d, C) in alts:
            v = C[0][idx] + nu * C[1][idx] + nu * nu * C[2][idx]
            cuts.append(list(-v) + [1.0]); rhs.append(0.0)
    best_val, best_w = None, None
    for _ in range(iters):
        res = linprog(c=[0.0] * n + [-1.0], A_ub=cuts, b_ub=rhs,
                      A_eq=[[1.0] * n + [0.0]], b_eq=[1.0],
                      bounds=[(0.0, None)] * n + [(None, None)], method="highs")
        if not res.success:
            break
        w = np.clip(np.asarray(res.x[:n], dtype=float), 0.0, None)
        tot = w.sum()
        if tot <= 0:
            break
        w = w / tot
        val = verified_value(alts, idx, w)
        if best_val is None or val > best_val:
            best_val, best_w = val, w
        # add the exact worst nu of every alternative at this w
        added = 0
        for (_alt, _d, C) in alts:
            c0 = float(C[0][idx] @ w); c1 = float(C[1][idx] @ w); c2 = float(C[2][idx] @ w)
            nus = [0.0, 1.0]
            if c2 > 0:
                vtx = -c1 / (2 * c2)
                if 0.0 < vtx < 1.0:
                    nus.append(vtx)
            nu = min(nus, key=lambda t: c0 + c1 * t + c2 * t * t)
            v = C[0][idx] + nu * C[1][idx] + nu * nu * C[2][idx]
            cuts.append(list(-v) + [1.0]); rhs.append(0.0)
            added += 1
        if added == 0:
            break
    return best_val, best_w


def main():
    g = load_game()
    rows = []
    print("F2: does a single width-2 query already beat the best scalar-only design?\n")
    for q in (3, 4):
        for mu in (0.25, 0.5):
            queries, alts = per_query_coeffs(g, q, mu)
            scal = [i for i, e in enumerate(queries) if e[0] == 's']
            pairs = [i for i, e in enumerate(queries)
                     if e[0] == 'g' and len(e[1]) == 2 and e[2] is False]
            pairs_h = [i for i, e in enumerate(queries)
                       if e[0] == 'g' and len(e[1]) == 2]
            print(f"   ({len(alts)} alternatives, all subsets of size q+1 with "
                  f"d >= 1 -- NOT one representative per orbit)")
            v0, _ = value_on_support(queries, alts, scal)
            best1, arg1 = None, None
            for p in pairs_h:
                v, _ = value_on_support(queries, alts, scal + [p])
                if best1 is None or v > best1:
                    best1, arg1 = v, queries[p]
            vall, _ = value_on_support(queries, alts, scal + pairs_h)
            vfull, _ = value_on_support(queries, alts, list(range(len(queries))))
            # self-checks a maximum over a larger support must satisfy
            if best1 < v0 - 1e-9 or vall < best1 - 1e-9 or vfull < vall - 1e-9:
                raise AssertionError(
                    f"monotonicity violated at q={q} mu={mu}: "
                    f"{v0} -> {best1} -> {vall} -> {vfull}; the search is not "
                    f"finding the optimum on the larger supports")
            gain1 = best1 - v0
            gainall = vall - v0
            frac = (gain1 / gainall) if gainall > 1e-12 else float('nan')
            print(f"q={q} mu={mu}:  scalars only {v0:.9f}")
            print(f"   + ONE best pair          {best1:.9f}   gain {gain1:+.3e}"
                  f"   ({arg1[0]}, G={sorted(arg1[1])}, h={arg1[2]})")
            print(f"   + ALL {len(pairs_h):3d} pairs           {vall:.9f}"
                  f"   gain {gainall:+.3e}")
            print(f"   + every query            {vfull:.9f}")
            print(f"   one pair captures {100*frac:.2f}% of the all-pairs gain")
            rows.append({"q": q, "mu": mu, "scalars_only": v0,
                         "one_best_pair": best1, "one_pair_gain": gain1,
                         "all_pairs": vall, "all_pairs_gain": gainall,
                         "full_game": vfull,
                         "one_pair_share_of_all_pairs_gain": frac,
                         "best_single_pair": [str(arg1[0]), sorted(arg1[1]),
                                              bool(arg1[2])],
                         "num_pair_queries": len(pairs_h)})
            print()

    helps = [r for r in rows if r["one_pair_gain"] > 1e-9]
    print("VERDICT")
    print(f"   a single width-2 query strictly improves on the scalar-only optimum in "
          f"{len(helps)}/{len(rows)} cells")
    if helps:
        print("   => in THIS model, no lower bound of the form 'a design must open")
        print("      Omega(q) pairs to gain anything' can hold: one pair already gains.")
        print("      What an Omega(q) bound could still say is that one pair captures")
        print("      only a fixed fraction of the achievable gain -- the percentages")
        print("      above are the quantity such a bound would have to be about.")
    else:
        print("   => one pair never helps here, which is consistent with (but does not")
        print("      prove) a lower bound requiring many pairs.")
    print("\n   Model: approximate_game at eps = 0, shell = 0, per-query variables, NOT")
    print("   the orbit-reduced solver and NOT the local phase-boundary parametrisation.")

    out = REPO / "research/worker_F_pairs_20260914/F2_single_pair_breaks_balanced.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "can one width-2 query already create a gain over the best "
                    "scalar-only design, with scalar weights free?",
        "method": "per-query coefficients rebuilt from approximate_game's affine "
                  "means, so individual pairs are distinguishable; weights SEARCHED "
                  "by LP on a nu grid and the value RE-EVALUATED in closed form on "
                  "[0,1] with no grid and no optimizer",
        "rows": rows,
        "not_established": [
            "approximate_game at eps=0, shell=0 only; not the local phase-boundary "
            "parametrisation of B1",
            "float arithmetic throughout",
            "only the listed (q, mu) cells",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
