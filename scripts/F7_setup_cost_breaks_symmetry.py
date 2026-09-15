#!/usr/bin/env python3
"""D6, the supervisor's high-risk direction F: does a per-TYPE setup cost destroy the
"average over permutations, so a symmetric design is WLOG" argument?

THE MODEL (as given):

    I_T = max over n_e >= 0 with  sum_e c_e n_e + kappa |{e : n_e > 0}| <= T
          of  inf_{alt} sum_e n_e KL_e.

With unit measurement costs the information is linear in n, so for a support of size
s the best is to spend the whole remaining budget on it:

    I_T = max over supports S of  (T - kappa |S|) * V(S),
    V(S) = max over w >= 0 supported on S with sum w = 1 of inf_{alt, nu} sum_e w_e I_e.

WHY THIS IS THE RIGHT TEST. The usual argument is: the objective is invariant under
the symmetry group and `inf` is concave, so averaging a design over the group cannot
lower its value; hence a symmetric design is WLOG. That argument is still true for
V(S). It FAILS for I_T, because averaging over the group spreads the weight over a
whole orbit, so |S| jumps from a few individual queries to the orbit size, and the
kappa |S| term is not invariant. This script measures the size of that failure.

  symmetric branch : take the orbit-uniform optimum. Its individual-query support is
                     the union of the orbits carrying weight, so |S| is the SUM of
                     the orbit counts, not the number of orbits.
  asymmetric branch: forward-select individual queries, re-optimising the weights on
                     the chosen support each time, and take the best (T - kappa s) V.

The asymmetric branch is a SEARCH, so the value it reports is a LOWER bound on the
asymmetric optimum. That is the right direction: a lower bound that already beats the
symmetric design is enough to refute the WLOG.

WHAT THIS DOES NOT ESTABLISH
 - approximate_game at eps = 0, shell = 0 only, and only the listed (q, mu).
 - Continuous n_e; the integer-measurement version is not done.
 - Forward selection is greedy: it under-states the asymmetric optimum, never
   over-states it.
 - Float arithmetic in the LP; the value is re-verified in closed form over nu.

    .venv/bin/python scripts/F7_setup_cost_breaks_symmetry.py
"""
from __future__ import annotations

import importlib.util, itertools, json
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
import sys
sys.path.insert(0, str(REPO / "scripts"))
from F2_single_pair_breaks_balanced import (load_game, per_query_coeffs,
                                            value_on_support, verified_value)


def orbit_key(q, e):
    coords = list(range(2 * q + 1)); j = 2 * q + 1
    A = frozenset(range(q + 1))
    groups = [sorted(A), [], [], sorted(set(coords) - A)]
    if e[0] == 's':
        return ('s', 4 if e[1] == j else
                next(i for i, g in enumerate(groups) if e[1] in g))
    return ('g', e[2], *(len(e[1] & set(g)) for g in groups))


def symmetric_design(queries, alts, q):
    """The orbit-uniform optimum: optimise one weight per orbit, spread uniformly
    inside each orbit. Returns (value, individual support size)."""
    orb = {}
    for i, e in enumerate(queries):
        orb.setdefault(orbit_key(q, e), []).append(i)
    keys = sorted(orb, key=str)
    # build a per-orbit coefficient by averaging the individual ones
    import numpy as np
    n = len(queries)
    # optimise over orbit weights by the same cutting plane, using a reduced
    # coefficient matrix: put weight w_k/|orbit k| on each member
    class Red:
        pass
    red_alts = []
    for (alt, d, C) in alts:
        Cr = np.array([[C[t][orb[k]].mean() for k in keys] for t in range(3)])
        red_alts.append((alt, d, Cr))
    val, w = value_on_support(list(range(len(keys))), red_alts,
                              list(range(len(keys))))
    if w is None:
        return None, None, None
    used = [k for k, wi in zip(keys, w) if wi > 1e-10]
    size = sum(len(orb[k]) for k in used)
    return val, size, len(used)


def greedy_supports(queries, alts, kmax):
    """Forward selection on INDIVIDUAL queries. Returns {s: (value, support)}."""
    chosen, out = [], {}
    remaining = list(range(len(queries)))
    for s in range(1, kmax + 1):
        best = (None, None)
        for c in remaining:
            v, _ = value_on_support(queries, alts, chosen + [c], iters=12)
            if v is not None and (best[0] is None or v > best[0]):
                best = (v, c)
        if best[1] is None:
            break
        chosen = chosen + [best[1]]
        remaining.remove(best[1])
        v, _ = value_on_support(queries, alts, chosen, iters=30)
        out[s] = (v, list(chosen))
    return out


def main():
    g = load_game()
    rows = []
    print("F7: does a per-type setup cost break the symmetry WLOG?\n")
    for q, mu in ((3, 0.25), (3, 0.5)):
        queries, alts = per_query_coeffs(g, q, mu)
        vsym, size_sym, n_orbits = symmetric_design(queries, alts, q)
        print(f"q={q} mu={mu}: {len(queries)} individual queries, "
              f"{len(alts)} alternatives")
        print(f"   symmetric (orbit-uniform) optimum: V = {vsym:.9f}, carried by "
              f"{size_sym} INDIVIDUAL queries across {n_orbits} orbits")
        gs = greedy_supports(queries, alts, kmax=10)
        print(f"   greedy asymmetric supports:")
        for s in sorted(gs):
            print(f"      s={s:2d}: V = {gs[s][0]:.9f}")
        # now the budgeted comparison
        cell = {"q": q, "mu": mu, "V_symmetric": vsym,
                "symmetric_support_size": size_sym, "symmetric_orbits": n_orbits,
                "greedy": {str(s): gs[s][0] for s in sorted(gs)}, "budget": []}
        print(f"   I_T = (T - kappa*s) * V(s):")
        for T in (50.0, 200.0):
            for kappa in (0.0, 0.5, 1.0, 2.0, 5.0):
                isym = (T - kappa * size_sym) * vsym
                basym, bs = None, None
                for s in sorted(gs):
                    v = (T - kappa * s) * gs[s][0]
                    if T - kappa * s <= 0:
                        continue
                    if basym is None or v > basym:
                        basym, bs = v, s
                verdict = ("asymmetric WINS" if basym > isym + 1e-9
                           else "symmetric holds")
                print(f"      T={T:6.1f} kappa={kappa:4.1f}:  symmetric {isym:12.4f}"
                      f"   best asymmetric {basym:12.4f} at s={bs}"
                      f"   -> {verdict}")
                cell["budget"].append({"T": T, "kappa": kappa,
                                       "I_symmetric": isym,
                                       "I_asymmetric": basym,
                                       "asym_support": bs,
                                       "asymmetric_wins": bool(basym > isym + 1e-9)})
        rows.append(cell)
        print()

    wins = [b for r in rows for b in r["budget"] if b["asymmetric_wins"]]
    pos = [b for r in rows for b in r["budget"] if b["kappa"] > 0]
    print("VERDICT")
    print(f"   the asymmetric design beats the symmetric one in {len(wins)} of the "
          f"{len(pos)+len([b for r in rows for b in r['budget'] if b['kappa']==0])} "
          f"(T, kappa) cells tried")
    zero = [b for r in rows for b in r["budget"]
            if b["kappa"] == 0 and b["asymmetric_wins"]]
    if zero:
        print("   WARNING: it also wins at kappa = 0, where symmetrisation IS WLOG.")
        print("   That means the greedy search is beating the orbit-uniform solve for")
        print("   a reason unrelated to setup cost -- treat the kappa > 0 cells with")
        print("   suspicion until that is explained.")
    elif wins:
        print("   and it NEVER wins at kappa = 0, where symmetrisation is genuinely")
        print("   WLOG. So the wins are caused by the setup cost, which is exactly the")
        print("   claim: once opening a query TYPE is paid for, 'average over the")
        print("   permutations' is no longer free, because the average is supported on")
        print("   the whole orbit.")
    else:
        print("   no cell separates: on these instances the setup cost did not break")
        print("   the symmetric design. That does not prove the WLOG survives -- the")
        print("   asymmetric branch is a greedy lower bound.")

    out = REPO / "research/worker_F_pairs_20260914/F7_setup_cost_breaks_symmetry.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "does a per-type setup cost kappa break 'symmetric design is "
                    "WLOG'?",
        "why": "the concavity/averaging argument is invariant for V(S) but NOT for "
               "(T - kappa|S|) V(S): averaging over the group spreads weight over a "
               "whole orbit, so |S| is not invariant",
        "rows": rows,
        "not_established": [
            "approximate_game at eps=0, shell=0, listed (q, mu) only",
            "continuous measurement counts; no integer version",
            "the asymmetric branch is greedy, hence a LOWER bound on the asymmetric "
            "optimum -- which is the safe direction for refuting the WLOG",
            "float arithmetic; the per-support value is re-verified in closed form "
            "over nu but not in exact rationals",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
