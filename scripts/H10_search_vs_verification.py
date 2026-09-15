#!/usr/bin/env python3
"""Support, high-risk direction 10: separate the cost of FINDING a safe decision from
the cost of CERTIFYING one.

The supervisor's point: "a decision having a short certificate does not mean the
learner knows which certificate to choose". The instruction is to build a two-part
parameter (search + verification), start from exact small decision trees, and look
for two instances with the SAME proposed parameter but decision-tree depth differing
by an ORDER, so that the parameter can be refuted early rather than after a thousand
lines of Lean.

DEFINITIONS, all exact and all computed by enumeration.
  verif(h, j)  = the least number of tests whose ANSWERS AT h already force j to be
                 safe: least |C| with {h' : q_e(h') = q_e(h) for all e in C} subset D_j.
  verif(I)     = max over h of  min over j safe at h  of verif(h, j).
                 This is the certificate cost of an ORACLE that is told which j and
                 which tests to use.
  depth(I)     = the least d such that some deterministic adaptive tree of depth d
                 always ends in a leaf where one decision is safe in EVERY world still
                 consistent. This is what a learner actually has to pay.

THREE CANDIDATE PARAMETERS ARE TESTED, in increasing strength:
  P1 = verif                                (certificate cost alone)
  P2 = verif + log2 (number of worlds)      (certificate + a counting term)
  P3 = verif * (number of minimal obstructions)   (certificate x an obstruction count)
A parameter is REFUTED as soon as two instances share its value while their depths
differ by more than a constant -- and the script exhibits the pair.

THE FAMILY. needle(n): worlds 1..n, decisions 1..n, D_j = {j}, tests "is h = i?".
Verifying takes ONE test; finding takes n-1. If that is right, P1 is dead at n = 3
already and the gap grows without bound, so no function of verif alone can bound
depth. A CONTRAST family is also run, where search and verification coincide, so the
separation is not an artefact of the definitions.

WHAT THIS DOES NOT ESTABLISH
 - Refuting a parameter is not proposing one. P2 and P3 are tested because they are
   the two obvious repairs, not because they are the supervisor's parameter.
 - Deterministic zero-error trees, worst case, uniform test costs. Randomised trees,
   error tolerance and weighted costs are not covered.
 - Exact on the listed instance sizes only.

    .venv/bin/python scripts/H10_search_vs_verification.py
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
import itertools, json, math
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def verif_cost(H, Dsets, tests, h, j):
    """least |C| with {h' : agrees with h on C} subset D_j."""
    if h not in Dsets[j]:
        return None
    E = list(range(len(tests)))
    for k in range(0, len(E) + 1):
        for C in itertools.combinations(E, k):
            ok = True
            for hp in H:
                if all(tests[e][hp] == tests[e][h] for e in C) and hp not in Dsets[j]:
                    ok = False
                    break
            if ok:
                return k
    return None


def verif(H, Dsets, tests):
    worst = 0
    for h in H:
        cands = [verif_cost(H, Dsets, tests, h, j) for j in range(len(Dsets))
                 if h in Dsets[j]]
        cands = [c for c in cands if c is not None]
        if not cands:
            return None            # no safe decision anywhere: instance is degenerate
        worst = max(worst, min(cands))
    return worst


def depth(H, Dsets, tests):
    """least worst-case depth of a deterministic tree ending in a commonly-safe leaf."""
    allH = frozenset(H)

    @lru_cache(maxsize=None)
    def d(C):
        if not C:
            return 0
        if any(all(h in Dsets[j] for h in C) for j in range(len(Dsets))):
            return 0
        best = None
        for e in range(len(tests)):
            yes = frozenset(h for h in C if tests[e][h])
            no = frozenset(h for h in C if not tests[e][h])
            if not yes or not no:
                continue           # a test that splits nothing cannot help
            v = 1 + max(d(yes), d(no))
            if best is None or v < best:
                best = v
        return best if best is not None else 10 ** 6

    return d(allH)


def minimal_obstructions(H, Dsets):
    """minimal (by inclusion) subsets of worlds with no commonly safe decision."""
    obs = []
    for k in range(2, len(H) + 1):
        for S in itertools.combinations(H, k):
            if any(all(h in Dsets[j] for h in S) for j in range(len(Dsets))):
                continue
            if any(set(o) <= set(S) for o in obs):
                continue
            obs.append(S)
    return obs


def needle(n):
    H = list(range(n))
    Dsets = [frozenset({j}) for j in range(n)]
    tests = [{h: (h == i) for h in H} for i in range(n)]
    return f"needle({n})", H, Dsets, tests


def bits(n):
    """contrast: worlds are n-bit strings, decisions read the whole string, tests are
    the bits. Here search and verification are both n."""
    H = list(range(2 ** n))
    Dsets = [frozenset({j}) for j in range(2 ** n)]
    tests = [{h: bool(h >> i & 1) for h in H} for i in range(n)]
    return f"bits({n})", H, Dsets, tests


def halfspace(n):
    """contrast: one decision is safe on a majority, so both costs are small."""
    H = list(range(n))
    Dsets = [frozenset(range(n)), frozenset({0})]
    tests = [{h: (h == i) for h in H} for i in range(n)]
    return f"halfspace({n})", H, Dsets, tests


def main():
    fams = ([needle(n) for n in (2, 3, 4, 5, 6, 7)]
            + [bits(n) for n in (1, 2, 3)]
            + [halfspace(n) for n in (3, 5, 7)])
    rows = []
    print("Direction 10: does certificate cost bound the cost of FINDING a decision?\n")
    print(f"{'instance':16s} {'|H|':>4s} {'|D|':>4s} {'tests':>6s} "
          f"{'verif':>6s} {'depth':>6s} {'obstr':>6s}   P1    P2      P3")
    for name, H, Dsets, tests in fams:
        v = verif(H, Dsets, tests)
        dp = depth(H, Dsets, tests)
        ob = len(minimal_obstructions(H, Dsets))
        P1 = v
        P2 = None if v is None else v + math.ceil(math.log2(max(1, len(H))))
        P3 = None if v is None else v * max(1, ob)
        print(f"{name:16s} {len(H):4d} {len(Dsets):4d} {len(tests):6d} "
              f"{v:6d} {dp:6d} {ob:6d} {P1:5d} {P2:5d} {P3:7d}")
        rows.append({"instance": name, "worlds": len(H), "decisions": len(Dsets),
                     "tests": len(tests), "verif": v, "depth": dp,
                     "min_obstructions": ob, "P1": P1, "P2": P2, "P3": P3})

    print("\nREFUTATIONS -- pairs sharing a parameter value but not a depth")
    verdict = {}
    for key in ("P1", "P2", "P3"):
        worst = None
        for a, b in itertools.combinations(rows, 2):
            if a[key] != b[key]:
                continue
            gap = abs(a["depth"] - b["depth"])
            if worst is None or gap > worst[0]:
                worst = (gap, a, b)
        if worst and worst[0] >= 2:
            g, a, b = worst
            print(f"   {key}: REFUTED. {a['instance']} and {b['instance']} both have "
                  f"{key} = {a[key]}, but depth {a['depth']} vs {b['depth']} "
                  f"(gap {g}).")
            verdict[key] = {"refuted": True, "gap": g,
                            "pair": [a["instance"], b["instance"]],
                            "value": a[key],
                            "depths": [a["depth"], b["depth"]]}
        else:
            print(f"   {key}: not refuted by these instances "
                  f"(largest same-value depth gap {worst[0] if worst else 0}).")
            verdict[key] = {"refuted": False,
                            "largest_gap": worst[0] if worst else 0}

    nd = [r for r in rows if r["instance"].startswith("needle")]
    print("\n   the needle family alone already settles P1: verification is "
          + ", ".join(str(r["verif"]) for r in nd)
          + " while depth is " + ", ".join(str(r["depth"]) for r in nd) + ".")
    if all(r["verif"] == nd[0]["verif"] for r in nd) and \
       nd[-1]["depth"] - nd[0]["depth"] >= 2:
        print("   verif is CONSTANT along the family and depth grows without bound, so")
        print("   NO function of the certificate cost alone can bound the depth. The")
        print("   two costs have to be carried separately.")
    bl = [r for r in rows if r["instance"].startswith("bits")]
    print("   the contrast family bits(n) has verif = depth = "
          + ", ".join(f"{r['verif']}/{r['depth']}" for r in bl)
          + ", so the separation is a property of the instances, not of the "
            "definitions.")

    out = REPO / "research/worker_H10_support_20260914/H10_search_vs_verification.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "can a parameter built from certificate (verification) cost bound "
                    "the depth of actually FINDING a safe decision?",
        "definitions": {
            "verif": "max over h of min over j safe at h of the least number of tests "
                     "whose answers at h force j to be safe",
            "depth": "least worst-case depth of a deterministic tree ending where some "
                     "decision is safe in every still-consistent world",
        },
        "rows": rows,
        "parameters_tested": verdict,
        "not_established": [
            "refuting a parameter is not proposing one",
            "deterministic zero-error trees, worst case, unit test costs",
            "exact on the listed instance sizes only",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
