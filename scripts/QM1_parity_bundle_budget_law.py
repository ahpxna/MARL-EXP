#!/usr/bin/env python3
"""Query + MASTER, the supervisor's high-risk bundle: the parity budget law.

CONSTRUCTION, on the corpus's REAL multi-tip geometry (`tip w j = 1 - (m-1)[j=w]`,
`selectedRadius f S = osc(a |-> sum_{l not in S} a_l)/2` over the support
`{0} u {tip w : w in W}`):

    x in {0,1}^d,   b(x) = x_1 xor ... xor x_d,
    W_x = {1 - b(x)} u {i+2 : x_i = 1}          (so m = d+2 tips)

with only j = 0, 1 retained as feasible decisions. The normalised loss is claimed to be

    l(x,j) = (2/(m-1)) selectedRadius(W_x, {j}) = 1{j != b(x)},

physical membership at auxiliary tip i+2 reads bit x_i at cost 1, and membership at
tip 0 or 1 reads the parity directly at cost M. Uniform prior, HARD PATHWISE budget B:

    R*(B) = 1/2  if B < min(d, M),      0  if B >= min(d, M).

WHAT IS CHECKED, exactly
 1. the loss identity, from `selectedRadius` recomputed from the tip vectors -- not
    assumed -- for every x and both retained decisions;
 2. membership at tip i+2 equals bit i, and membership at tip 0/1 equals the parity;
 3. the boxed law, by enumerating ALL deterministic adaptive query trees under the
    hard pathwise budget, for a grid of (d, M, B);
 4. a NEGATIVE CONTROL: replace the parity by the FIRST BIT (same geometry, same
    costs, only the labelling function changes). Then one cheap query already
    decides, the threshold must collapse to B >= 1, and the law above must FAIL --
    otherwise the enumeration is not sensitive to what it claims to measure.

WHAT THIS DOES NOT ESTABLISH
 - The value computed is the BAYES risk under the uniform prior. It lower-bounds the
   minimax risk; the two coincide here by the bit-flip symmetry, but that symmetry
   argument is NOT enumerated.
 - Deterministic adaptive trees only. Randomisation cannot beat the Bayes value, so
   the number is right, but no randomised tree is enumerated.
 - Exact per (d, M, B) listed; no asymptotics, no Lean.
 - `min(d, M)` is a threshold in the BUDGET, not a sample-complexity law: nothing
   here says anything about noise, estimation, or repeated queries.

    .venv/bin/python scripts/QM1_parity_bundle_budget_law.py
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
import itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def tip_vec(m: int, w: int):
    """tip w, as a vector in R^m: 1 - (m-1) e_w."""
    return tuple(F(1) - (F(m - 1) if j == w else F(0)) for j in range(m))


def selected_radius(points, j: int, m: int) -> F:
    vals = [sum(a[l] for l in range(m) if l != j) for a in points]
    return (max(vals) - min(vals)) / 2


def world_support(m: int, W):
    return [tuple(F(0) for _ in range(m))] + [tip_vec(m, w) for w in sorted(W)]


def parity(x):
    p = 0
    for b in x:
        p ^= b
    return p


def W_of(x, d, label):
    m = d + 2
    return frozenset({1 - label(x)} | {i + 2 for i in range(d) if x[i] == 1})


def optimal_risk(d: int, M: int, B: int, label):
    """Bayes risk over ALL deterministic adaptive trees under a hard pathwise
    budget. Queries: membership at auxiliary tip i+2 (cost 1) or at tip 0/1
    (cost M). Decisions: j in {0,1}; error iff j != label(x)."""
    Xs = list(itertools.product((0, 1), repeat=d))
    W = {x: W_of(x, d, label) for x in Xs}
    # the permitted catalog, read through the geometry
    probes = [(lambda x, i=i: (i + 2) in W[x], 1) for i in range(d)]
    probes += [(lambda x, t=t: t in W[x], M) for t in (0, 1)]

    @lru_cache(maxsize=None)
    def best(C, budget):
        if not C:
            return 0
        val = min(sum(1 for x in C if j != label(x)) for j in (0, 1))
        for (ask, c) in probes:
            if c > budget:
                continue
            yes = frozenset(x for x in C if ask(x))
            no = frozenset(x for x in C if not ask(x))
            v = best(yes, budget - c) + best(no, budget - c)
            if v < val:
                val = v
        return val

    return F(best(frozenset(Xs), B), len(Xs))


def main():
    print("Query + MASTER parity bundle: the min(d, M) budget law\n")
    rows = []

    print("1. the loss identity, from selectedRadius recomputed on the tip vectors")
    bad = 0
    for d in (2, 3, 4):
        m = d + 2
        for x in itertools.product((0, 1), repeat=d):
            W = W_of(x, d, parity)
            S = world_support(m, W)
            for j in (0, 1):
                got = F(2, m - 1) * selected_radius(S, j, m)
                want = F(1) if j != parity(x) else F(0)
                if got != want:
                    bad += 1
                    print(f"   MISMATCH d={d} x={x} j={j}: {got} vs {want}")
        print(f"   d={d}: exact on all {2**d}x2 (world, retained decision) pairs")
    if bad:
        raise AssertionError(f"{bad} loss mismatches")

    print("\n2. what each permitted query reads")
    for d in (3,):
        for x in itertools.product((0, 1), repeat=d):
            W = W_of(x, d, parity)
            for i in range(d):
                assert ((i + 2) in W) == (x[i] == 1), "auxiliary tip is not bit i"
            assert (0 in W) == (parity(x) == 1), "tip 0 does not read the parity"
            assert (1 in W) == (parity(x) == 0), "tip 1 does not read the parity"
    print("   auxiliary tip i+2 in W_x  <->  x_i = 1;  tip 0 in W_x <-> b(x) = 1;"
          "  tip 1 in W_x <-> b(x) = 0")

    print("\n3. the boxed law  R*(B) = 1/2 for B < min(d,M), 0 for B >= min(d,M)")
    fails = 0
    for d in (2, 3, 4):
        for M in (1, 2, 3, 5):
            thr = min(d, M)
            got = []
            for B in range(0, d + M + 2):
                r = optimal_risk(d, M, B, parity)
                want = F(1, 2) if B < thr else F(0)
                got.append((B, r, want))
                if r != want:
                    fails += 1
            line = " ".join(f"{B}:{r}" for B, r, _ in got)
            mark = "OK " if all(r == w for _, r, w in got) else "FAIL"
            print(f"   d={d} M={M} threshold min(d,M)={thr}  [{mark}]  {line}")
            rows.append({"d": d, "M": M, "threshold": thr,
                         "risk_by_budget": {str(B): str(r) for B, r, _ in got},
                         "law_holds": all(r == w for _, r, w in got)})
    if fails:
        raise AssertionError(f"{fails} budgets violate the claimed law")

    print("\n4. negative control: same geometry and costs, label = FIRST BIT")
    ctrl = []
    for d in (3,):
        for M in (2, 5):
            got = [(B, optimal_risk(d, M, B, lambda x: x[0]))
                   for B in range(0, d + M + 2)]
            thr = min(d, M)
            matches_parity_law = all(
                r == (F(1, 2) if B < thr else F(0)) for B, r in got)
            print(f"   d={d} M={M}: "
                  + " ".join(f"{B}:{r}" for B, r in got)
                  + f"   -> parity law {'STILL HOLDS (control failed)' if matches_parity_law else 'BROKEN, as it must be'}")
            ctrl.append({"d": d, "M": M,
                         "risk_by_budget": {str(B): str(r) for B, r in got},
                         "parity_law_still_holds": matches_parity_law})
            if matches_parity_law:
                raise AssertionError("the control did not separate; the enumeration "
                                     "is not sensitive to the labelling function")
    print("   one cheap bit query already decides the first bit, so the threshold "
          "collapses to B >= 1 and the min(d,M) law fails -- the enumeration does "
          "measure what it claims.")

    print("\nCONCLUSION: on the corpus's own multi-tip geometry the parity bundle has")
    print("R*(B) = 1/2 below the budget min(d, M) and 0 at or above it, exactly, for")
    print("every (d, M) listed. The value is the uniform-prior BAYES risk over all")
    print("deterministic adaptive trees; the step to minimax uses a bit-flip symmetry")
    print("that is NOT enumerated here.")

    out = REPO / "research/worker_QM_bundle_20260914/QM1_parity_bundle_budget_law.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "claim": "R*(B) = 1/2 if B < min(d,M), else 0",
        "geometry": "tip w j = 1 - (m-1)[j=w]; selectedRadius f S = "
                    "osc(a |-> sum_{l not in S} a_l)/2; m = d+2",
        "loss_identity": "(2/(m-1)) selectedRadius(W_x,{j}) = 1{j != b(x)}, "
                         "recomputed from the tip vectors, exact for d in {2,3,4}",
        "law": rows,
        "negative_control": ctrl,
        "not_established": [
            "the value is the uniform-prior Bayes risk; the Bayes-to-minimax step "
            "uses a bit-flip symmetry that is not enumerated",
            "deterministic adaptive trees only",
            "a budget threshold, not a sample-complexity law: no noise, no repeats",
            "no Lean module",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
