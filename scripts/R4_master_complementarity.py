#!/usr/bin/env python3
"""MASTER, high-risk direction R4: how strong is complementarity in acquisition?

The instruction: BEFORE designing a greedy evidence-buying rule, find actual examples
with gain({e1}) = gain({e2}) = 0 but gain({e1,e2}) > 0, ported into the real
support/query model with the real costs -- XOR being the familiar abstract example.
Then look for a restriction under which complementarity is bounded, because without
one the value of evidence must NOT be assumed submodular.

MODEL, the corpus's own. Worlds carry a multi-tip support; a query is physical
membership at a declared tip; a decision j is safe in world h exactly when
selectedRadius(W_h, {j}) = 0, recomputed here from the tip vectors
`tip w j = 1 - (m-1)[j=w]` rather than assumed. With a catalog E the learner sees all
the answers in E, so

    R(E) = sum over fibres of E of  min over decisions j of (error mass on that fibre)
    gain(E) = R(empty) - R(E).

PART 1. The parity family x in {0,1}^d, W_x = {1-b(x)} u {i+2 : x_i = 1} gives
gain = 0 for every strict subset of the bit queries and gain = 1/2 for the whole set.
Reported with the exact numbers and the costs.

PART 2. The submodularity defect

    def(E; e1, e2) = gain(E u {e1,e2}) - gain(E u {e1}) - gain(E u {e2}) + gain(E),

maximised over ALL E and all pairs. def <= 0 everywhere is submodularity. This is
computed for four instance classes, one of which is the proposed RESTRICTION:

   parity(d)        the XOR family -- expected to be maximally complementary
   junta1(...)      every decision's safe set is a fibre of a SINGLE test
   needle(n)        safe sets are singletons, tests identify one world at a time
   product(...)     safe sets are intersections of two tests' fibres

WHAT THIS DOES NOT ESTABLISH
 - A maximal defect of 0 on a class is evidence that the class is submodular, not a
   proof. The classes are enumerated instances, not all instances of the shape.
 - Uniform prior, unit costs, no budget: the learner buys a catalog and then sees all
   of it. Sequential purchase under a budget is a different problem.
 - No approximation guarantee is derived from the restriction; showing the defect is
   zero is the precondition for one, not the guarantee.

    .venv/bin/python scripts/R4_master_complementarity.py
"""
from __future__ import annotations

from fractions import Fraction as F
import itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def tip_vec(m, w):
    return tuple(F(1) - (F(m - 1) if j == w else F(0)) for j in range(m))


def selected_radius(points, j, m):
    vals = [sum(a[l] for l in range(m) if l != j) for a in points]
    return (max(vals) - min(vals)) / 2


def safe_from_geometry(m, W, decisions):
    """decision j is safe iff selectedRadius = 0, recomputed from the tip vectors."""
    pts = [tuple(F(0) for _ in range(m))] + [tip_vec(m, w) for w in sorted(W)]
    return {j: (selected_radius(pts, j, m) == 0) for j in decisions}


def risk(worlds, safe, answers, E):
    """R(E): partition the worlds by the answers in E, take the best decision per
    fibre, sum the error mass under the uniform prior."""
    fib = {}
    for h in worlds:
        key = tuple(answers[e][h] for e in sorted(E))
        fib.setdefault(key, []).append(h)
    tot = 0
    decisions = list(next(iter(safe.values())).keys())
    for _, C in fib.items():
        tot += min(sum(1 for h in C if not safe[h][j]) for j in decisions)
    return F(tot, len(worlds))


def defect_scan(worlds, safe, answers, queries):
    """max over E and pairs of the submodularity defect."""
    g = {}

    def gain(E):
        key = frozenset(E)
        if key not in g:
            g[key] = risk(worlds, safe, answers, frozenset()) - \
                     risk(worlds, safe, answers, key)
        return g[key]

    worst = (F(0), None)
    rest = list(queries)
    for k in range(0, len(rest) + 1):
        for E in itertools.combinations(rest, k):
            Es = set(E)
            for e1, e2 in itertools.combinations([q for q in rest if q not in Es], 2):
                d = (gain(Es | {e1, e2}) - gain(Es | {e1}) - gain(Es | {e2})
                     + gain(Es))
                if d > worst[0]:
                    worst = (d, (sorted(Es), e1, e2))
    return worst, gain


# --------------------------------------------------------------- the families
def parity_family(d):
    m = d + 2
    worlds = list(itertools.product((0, 1), repeat=d))
    W = {}
    for x in worlds:
        p = 0
        for b in x:
            p ^= b
        W[x] = frozenset({1 - p} | {i + 2 for i in range(d) if x[i] == 1})
    decisions = [0, 1]
    safe = {h: safe_from_geometry(m, W[h], decisions) for h in worlds}
    queries = [f"bit{i}" for i in range(d)]
    answers = {f"bit{i}": {h: ((i + 2) in W[h]) for h in worlds} for i in range(d)}
    return f"parity(d={d})", worlds, safe, answers, queries


def junta1_family(n):
    """every decision's safe set is a fibre of ONE test -- the proposed restriction."""
    worlds = list(range(2 ** n))
    m = n + 1
    # decision j (j < n) is safe exactly when bit j is 0; decision n is never safe
    decisions = list(range(n + 1))
    safe = {}
    for h in worlds:
        Wh = frozenset({j for j in range(n) if (h >> j) & 1} | {n})
        safe[h] = safe_from_geometry(m, Wh, decisions)
    queries = [f"bit{i}" for i in range(n)]
    answers = {f"bit{i}": {h: bool((h >> i) & 1) for h in worlds} for i in range(n)}
    return f"junta1(n={n})", worlds, safe, answers, queries


def needle_family(n):
    worlds = list(range(n))
    m = n
    decisions = list(range(n))
    safe = {h: safe_from_geometry(m, frozenset({h}), decisions) for h in worlds}
    queries = [f"is{i}" for i in range(n)]
    answers = {f"is{i}": {h: (h == i) for h in worlds} for i in range(n)}
    return f"needle(n={n})", worlds, safe, answers, queries


def product_family(n):
    """safe sets are intersections of TWO tests' fibres -- one step outside junta1."""
    worlds = list(range(2 ** n))
    m = n + 1
    decisions = list(range(n + 1))
    safe = {}
    for h in worlds:
        unsafe = {n}
        for j in range(n):
            if ((h >> j) & 1) or ((h >> ((j + 1) % n)) & 1):
                unsafe.add(j)
        safe[h] = safe_from_geometry(m, frozenset(unsafe), decisions)
    queries = [f"bit{i}" for i in range(n)]
    answers = {f"bit{i}": {h: bool((h >> i) & 1) for h in worlds} for i in range(n)}
    return f"product(n={n})", worlds, safe, answers, queries


def main():
    print("R4: how strong is complementarity in acquisition?\n")
    print("PART 1 -- the XOR example, in the actual support/query model")
    rows = []
    for d in (2, 3):
        name, worlds, safe, answers, queries = parity_family(d)
        R0 = risk(worlds, safe, answers, frozenset())
        singles = {q: R0 - risk(worlds, safe, answers, frozenset({q}))
                   for q in queries}
        full = R0 - risk(worlds, safe, answers, frozenset(queries))
        subs = {}
        for k in range(1, len(queries)):
            for E in itertools.combinations(queries, k):
                subs[E] = R0 - risk(worlds, safe, answers, frozenset(E))
        print(f"   {name}: R(empty) = {R0}")
        print(f"      gain of each single query : "
              + ", ".join(f"{q}={v}" for q, v in singles.items()))
        print(f"      gain of every PROPER subset: "
              + ", ".join(str(v) for v in sorted(set(subs.values()))))
        print(f"      gain of the FULL set      : {full}   (cost {len(queries)})")
        assert all(v == 0 for v in subs.values()), "a proper subset already gains"
        assert full > 0, "the full set gains nothing"
        rows.append({"family": name, "R_empty": str(R0),
                     "gain_singletons": {q: str(v) for q, v in singles.items()},
                     "gain_proper_subsets": sorted({str(v) for v in subs.values()}),
                     "gain_full": str(full), "cost_full": len(queries)})
    print("   => gain(e1) = gain(e2) = 0 but gain({e1,e2}) > 0, in the real model,")
    print("      with the safety predicate read off selectedRadius. Value of evidence")
    print("      is NOT submodular here, so a greedy purchase rule has no guarantee.\n")

    print("PART 2 -- the submodularity defect, by instance class")
    fams = ([parity_family(d) for d in (2, 3)]
            + [junta1_family(n) for n in (2, 3, 4)]
            + [needle_family(n) for n in (3, 4, 5)]
            + [product_family(n) for n in (3, 4)])
    scan = []
    for name, worlds, safe, answers, queries in fams:
        (d, wit), _ = defect_scan(worlds, safe, answers, queries)
        verdict = "SUBMODULAR (defect 0)" if d == 0 else f"defect {d} > 0"
        print(f"   {name:16s} {len(worlds):3d} worlds, {len(queries)} queries -> "
              f"{verdict}"
              + (f"   at E={wit[0]}, pair ({wit[1]}, {wit[2]})" if d > 0 else ""))
        scan.append({"family": name, "worlds": len(worlds),
                     "queries": len(queries), "max_defect": str(d),
                     "submodular": d == 0,
                     "witness": None if d == 0 else
                               {"E": wit[0], "pair": [wit[1], wit[2]]}})

    j1 = [s for s in scan if s["family"].startswith("junta1")]
    pf = [s for s in scan if s["family"].startswith("parity")]
    print("\nVERDICT")
    if all(s["submodular"] for s in j1) and not any(s["submodular"] for s in pf):
        print("   the RESTRICTION 'every decision's safe set is a fibre of a single")
        print("   test' has zero defect on every instance tried, while the parity")
        print("   family has a strictly positive one. So there IS a restriction under")
        print("   which complementarity vanishes, and it is not vacuous.")
        print("   This is the precondition for a greedy guarantee -- not the guarantee.")
    else:
        print("   the proposed restriction does not separate cleanly on these")
        print("   instances; report as inconclusive rather than claiming a class.")
    others = [s for s in scan if not s["family"].startswith(("junta1", "parity"))]
    print("   the other classes: "
          + ", ".join(f"{s['family']} {'submodular' if s['submodular'] else 'defect ' + s['max_defect']}"
                      for s in others))

    out = REPO / "research/worker_R4_master_20260914/R4_master_complementarity.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "how strong is complementarity in acquisition, and is there a "
                    "restriction that bounds it?",
        "model": "corpus multi-tip geometry; safety read off selectedRadius "
                 "recomputed from tip vectors; R(E) = sum over fibres of the best "
                 "decision's error mass; uniform prior, unit costs, no budget",
        "xor_examples": rows,
        "submodularity_scan": scan,
        "not_established": [
            "zero maximal defect on a class is evidence, not a proof, of "
            "submodularity for that class",
            "uniform prior, unit costs, catalog bought up front",
            "no approximation guarantee is derived",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
