#!/usr/bin/env python3
"""Structural, the supervisor's high-risk direction: the sharp nesting constant.

    eps_nest(F) = min_pi max_k [ L_F(S_k^pi) - min_{|T|=k} L_F(T) ],
    eps_nest* = sup_F eps_nest(F).

Known in the corpus: a lower witness of 1/2 (the earlier conjecture eps* = 1/4 was
REFUTED by an exact enumeration of all 24 rankings) and a universal upper bound of
2/3 by top-span. The gap [1/2, 2/3] is what is open.

This script runs the supervisor's branch (b): build a family forcing EVERY ranking
above 1/2, and if none exists, say what the obstruction looks like.

THE TWO-ACTION CASE IS A SUBSET-SUM PROBLEM, and that is what makes an exhaustive
search possible. With h = 2 actions, write g_i = F[i][1] - F[i][0]. Adding a constant
to a row across all actions shifts every partial sum equally and changes nothing, so
the instance is exactly the vector g, and

    L_F(S) = |sum_{i not in S} g_i| / sum_i |g_i|.

So the search below is EXHAUSTIVE over all integer g up to the stated entry bound and
size, not a sample: every two-action instance with those entries is visited (a
rational instance scales to an integer one, and only the ratio matters).

For h = 3 the objective is a genuine max-minus-min of a 3-vector and is NOT a
subset-sum; that part of the search is a bounded scan, not exhaustive, and is
labelled as such.

WHAT THIS DOES NOT ESTABLISH
 - No improvement of the 2/3 upper bound is attempted here. That is the supervisor's
   branch (a) and needs analysis, not search.
 - Exhaustive only within the stated entry range and size. A larger alphabet or more
   components could still exceed the best value found.
 - The h = 3 scan is a scan.

    .venv/bin/python scripts/G5_nesting_constant_search.py
"""
from __future__ import annotations

from fractions import Fraction as F
import itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


# --------------------------------------------------------- two actions: exact
def eps_nest_two(g):
    """g: tuple of ints. Returns eps_nest as a Fraction, and an optimal ranking."""
    m = len(g)
    D = sum(abs(v) for v in g)
    if D == 0:
        return F(0), tuple(range(m))
    idx = range(m)
    # L(S) * D = |sum_{i not in S} g_i|
    tot = sum(g)
    best_k = [None] * (m + 1)
    for k in range(m + 1):
        best = None
        for T in itertools.combinations(idx, k):
            v = abs(tot - sum(g[i] for i in T))
            if best is None or v < best:
                best = v
        best_k[k] = best
    best_pi, best_val = None, None
    for pi in itertools.permutations(idx):
        run = tot
        worst = 0
        ok = True
        for k in range(m + 1):
            if k > 0:
                run -= g[pi[k - 1]]
            r = abs(run) - best_k[k]
            if r > worst:
                worst = r
                if best_val is not None and worst >= best_val * D:
                    ok = False
                    break
        if not ok:
            continue
        val = F(worst, D)
        if best_val is None or val < best_val:
            best_val, best_pi = val, pi
    return best_val, best_pi


def canonical_vectors(m, lo, hi):
    """Every integer vector of length m with entries in [lo,hi], up to the two
    symmetries that leave eps_nest unchanged: permuting components, and negating
    the whole vector. Sorted multisets, first nonzero entry non-negative in sum."""
    seen = set()
    for g in itertools.combinations_with_replacement(range(lo, hi + 1), m):
        if all(v == 0 for v in g):
            continue
        neg = tuple(sorted(-v for v in g))
        key = min(g, neg)
        if key in seen:
            continue
        seen.add(key)
        yield key


# ------------------------------------------------------- three actions: a scan
def eps_nest_general(rows):
    """rows: list of tuples of ints, one per component, one entry per action."""
    m = len(rows); h = len(rows[0])
    D = sum(max(r) - min(r) for r in rows)
    if D == 0:
        return F(0), tuple(range(m))

    def Lnum(S):
        vals = [sum(rows[i][a] for i in range(m) if i not in S) for a in range(h)]
        return max(vals) - min(vals)

    best_k = {}
    for k in range(m + 1):
        best_k[k] = min(Lnum(set(T)) for T in itertools.combinations(range(m), k))
    best_val, best_pi = None, None
    for pi in itertools.permutations(range(m)):
        worst = max(Lnum(set(pi[:k])) - best_k[k] for k in range(m + 1))
        val = F(worst, D)
        if best_val is None or val < best_val:
            best_val, best_pi = val, pi
    return best_val, best_pi


def main():
    results = {}
    print("Structural: how large can eps_nest(F) be?\n")
    print("two actions -- EXHAUSTIVE over integer g up to the stated bound")
    champ = (F(0), None, None)
    for m, lo, hi in ((3, -3, 3), (4, -3, 3), (5, -3, 3), (6, -2, 2), (6, -3, 3)):
        best = (F(0), None)
        count = 0
        for g in canonical_vectors(m, lo, hi):
            count += 1
            v, pi = eps_nest_two(g)
            if v > best[0]:
                best = (v, g)
        print(f"   m={m} entries in [{lo},{hi}]: {count:5d} instances up to "
              f"symmetry -> max eps_nest = {best[0]} = {float(best[0]):.6f}"
              f"   at g = {best[1]}")
        results[f"two_m{m}_{lo}_{hi}"] = {"instances": count,
                                          "max_eps_nest": str(best[0]),
                                          "argmax_g": list(best[1]) if best[1] else None}
        if best[0] > champ[0]:
            champ = (best[0], best[1], f"m={m} entries [{lo},{hi}]")

    print(f"\n   best two-action value found: {champ[0]} = {float(champ[0]):.6f} "
          f"at g = {champ[1]}  ({champ[2]})")

    print("\n three actions -- a bounded SCAN, not exhaustive")
    best3 = (F(0), None)
    alphabet = (-2, -1, 0, 1, 2)
    n3 = 0
    for m in (3, 4):
        for rows in itertools.combinations_with_replacement(
                list(itertools.product(alphabet, repeat=3)), m):
            n3 += 1
            v, pi = eps_nest_general(list(rows))
            if v > best3[0]:
                best3 = (v, rows)
    print(f"   {n3} instances scanned (m in {{3,4}}, entries in {alphabet}) -> "
          f"max eps_nest = {best3[0]} = {float(best3[0]):.6f}")
    print(f"   at rows = {best3[1]}")
    results["three_action_scan"] = {"instances": n3,
                                    "max_eps_nest": str(best3[0]),
                                    "argmax_rows": [list(r) for r in best3[1]]}

    overall = max(champ[0], best3[0])
    print("\nVERDICT")
    print(f"   best eps_nest found anywhere in this search: {overall} = "
          f"{float(overall):.6f}")
    if overall > F(1, 2):
        print("   this EXCEEDS the known lower witness 1/2, so the lower end of the")
        print("   open interval [1/2, 2/3] moves up.")
    elif overall == F(1, 2):
        print("   this MATCHES the known lower witness 1/2 and does not beat it.")
        print("   Within the ranges searched, nothing forces every ranking above 1/2.")
        print("   The obstruction is visible in the two-action case: L_F(S) there is")
        print("   |sum of the omitted g_i| / sum|g_i|, and a ranking that removes the")
        print("   large-|g| components first keeps every prefix within 1/2 of the")
        print("   per-budget optimum. Beating 1/2 therefore needs either many")
        print("   incompatible budgets at once (more components, which the m=6 sweep")
        print("   did not deliver) or an action count above 2, where the objective is")
        print("   no longer a subset sum.")
    else:
        print("   BELOW the known witness 1/2 -- which would mean the search or the")
        print("   witness is wrong; investigate before trusting either.")
    print("\n   No improvement of the 2/3 upper bound is claimed: that is the other")
    print("   branch and needs analysis, not search.")

    out = REPO / "research/worker_G_nesting_20260914/G5_nesting_constant_search.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "eps_nest* = sup_F eps_nest(F); known to lie in [1/2, 2/3]",
        "two_action_reduction": "with h = 2, L_F(S) = |sum_{i not in S} g_i| / "
                                "sum_i |g_i| with g_i = F[i][1] - F[i][0]; the search "
                                "over integer g is therefore EXHAUSTIVE within the "
                                "stated entry bound and length",
        "results": results,
        "best_found": str(overall),
        "beats_known_lower_witness_half": overall > F(1, 2),
        "not_established": [
            "no improvement of the 2/3 upper bound is attempted",
            "exhaustive only within the stated entry range and length",
            "the three-action part is a bounded scan, not exhaustive",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
