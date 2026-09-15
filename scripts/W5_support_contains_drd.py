#!/usr/bin/env python3
"""W5 (the supervisor's highest-risk direction): does the Support model already
CONTAIN the generic decision-region problem?

If it does, an "acquisition theorem" proved in the Support model is a re-embedded
DRD theorem, and `actual support geometry` supplies no novelty by itself. That is a
useful NEGATIVE result, and it says which restriction has to be added before more
Lean is written.

THE EMBEDDING (exactly as specified). A DRD instance is: worlds H, decisions
1..m, safe sets D_j subset H, binary tests q_e, a cost per test. Put d = m+2 and

    anchor  0
    bad tip b_j = 1 - (d-1) e_j                       for each decision j
    marker  p_e = z_e (e_{m+1} - e_{m+2}),  z_e > 0 distinct
    K_h = {0} u {b_j : h not in D_j} u {p_e : q_e(h) = 1}

The corpus's geometry is
    selectedRadius f {i} = supportOsc {i}^c f / 2 = osc(a |-> sum_{l != i} a_l)/2

so the two target theorems are
    selectedRadius_{K_h}({j}) = 0 if h in D_j, (d-1)/2 if h not in D_j
    p_e in K_h  <->  q_e(h) = 1.

WHAT IS CHECKED, all in exact Fraction arithmetic
 1. the radius formula, for EVERY world and EVERY decision;
 2. marker membership equivalence;
 3. the markers are distinct from the anchor, from every bad tip, and from each
    other -- the separation the formula needs;
 4. THE REDUCTION ITSELF: the optimal adaptive risk at every hard pathwise budget,
    computed independently in the DRD model and in the physical model, over ALL
    deterministic adaptive trees. Equal curves means the physical model is not
    solving a different problem.
 5. THE SIDE CONDITION, as a negative control. The supervisor's caveat is that the
    permitted query catalog must be the declared markers ONLY. We ALSO run the
    variant where the learner may probe bad tips, and check the curves then DIFFER
    -- if they did not, the caveat would be vacuous and the check would prove
    nothing about the catalog.

WHAT THIS DOES NOT ESTABLISH
 - It is an embedding, not an equivalence of the two model CLASSES: every DRD
   instance appears inside the Support model, not conversely.
 - Only the instances enumerated below are checked; this is NUMERICAL EVIDENCE for
   the embedding, exact per instance, not a proof over all instances. The algebra
   above is a proof sketch; the Lean statement is not attempted here.
 - Nothing is claimed about whether the Support PAPER's theorems are DRD theorems;
   what is shown is that the model is expressive enough to contain DRD instances.

    .venv/bin/python scripts/W5_support_contains_drd.py
"""
from __future__ import annotations

from fractions import Fraction as F
from functools import lru_cache
import json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def build(m: int, ntests: int):
    d = m + 2
    zero = tuple(F(0) for _ in range(d))
    bad = [tuple(F(1) - (F(d - 1) if l == j else F(0)) for l in range(d))
           for j in range(m)]
    markers = []
    for e in range(ntests):
        z = F(e + 1)                      # positive and pairwise distinct
        markers.append(tuple((z if l == m else (-z if l == m + 1 else F(0)))
                             for l in range(d)))
    return d, zero, bad, markers


def support_of(h, m, ntests, Dsets, tests, zero, bad, markers):
    pts = [zero]
    pts += [bad[j] for j in range(m) if h not in Dsets[j]]
    pts += [markers[e] for e in range(ntests) if tests[e][h]]
    return pts


def selected_radius(points, i, d):
    vals = [sum(a[l] for l in range(d) if l != i) for a in points]
    return (max(vals) - min(vals)) / 2


def drd_curve(H, m, Dsets, tests, costs, budgets):
    allH = frozenset(H)

    @lru_cache(maxsize=None)
    def best(C, budget):
        if not C:
            return 0
        val = min(sum(1 for h in C if h not in Dsets[j]) for j in range(m))
        for e in range(len(tests)):
            if costs[e] > budget:
                continue
            yes = frozenset(h for h in C if tests[e][h])
            no = frozenset(h for h in C if not tests[e][h])
            v = best(yes, budget - costs[e]) + best(no, budget - costs[e])
            if v < val:
                val = v
        return val

    return [F(best(allH, B), len(H)) for B in budgets]


def physical_curve(H, m, ntests, Dsets, tests, costs, budgets, d, zero, bad,
                   markers, allow_bad_tip_probes=False):
    supports = {h: support_of(h, m, ntests, Dsets, tests, zero, bad, markers)
                for h in H}
    safe = {(h, j): (selected_radius(supports[h], j, d) == 0)
            for h in H for j in range(m)}
    probes = [(lambda h, e=e: markers[e] in supports[h], costs[e])
              for e in range(ntests)]
    if allow_bad_tip_probes:
        probes += [(lambda h, j=j: bad[j] in supports[h], 1) for j in range(m)]
    allH = frozenset(H)

    @lru_cache(maxsize=None)
    def best(C, budget):
        if not C:
            return 0
        val = min(sum(1 for h in C if not safe[(h, j)]) for j in range(m))
        for (ask, c) in probes:
            if c > budget:
                continue
            yes = frozenset(h for h in C if ask(h))
            no = frozenset(h for h in C if not ask(h))
            v = best(yes, budget - c) + best(no, budget - c)
            if v < val:
                val = v
        return val

    return [F(best(allH, B), len(H)) for B in budgets]


def instances():
    out = []
    H = list(range(4))
    out.append(("4 worlds / 2 decisions / 2 tests", H, 2,
                [frozenset({0, 1}), frozenset({2, 3})],
                [{h: (h in (0, 2)) for h in H}, {h: (h in (0, 1)) for h in H}],
                [1, 1]))
    H = list(range(6))
    out.append(("6 worlds / 3 decisions / 3 tests", H, 3,
                [frozenset({0, 1}), frozenset({2, 3}), frozenset({4, 5})],
                [{h: (h % 2 == 0) for h in H},
                 {h: (h < 3) for h in H},
                 {h: (h in (0, 3, 5)) for h in H}],
                [1, 2, 1]))
    H = list(range(8))
    out.append(("8 worlds / 3 decisions / 3 bit tests", H, 3,
                [frozenset({0, 1, 2, 3}), frozenset({0, 1, 4, 5}),
                 frozenset({0, 2, 4, 6})],
                [{h: bool(h & 1) for h in H}, {h: bool(h & 2) for h in H},
                 {h: bool(h & 4) for h in H}],
                [1, 1, 1]))
    H = list(range(5))
    out.append(("5 worlds / 2 decisions / 1 uninformative test", H, 2,
                [frozenset({0, 1}), frozenset({1, 2})],
                [{h: True for h in H}],
                [1]))
    return out


def main():
    rows = []
    print("W5: does the Support model contain the generic decision-region problem?\n")
    for name, H, m, Dsets, tests, costs in instances():
        ntests = len(tests)
        d, zero, bad, markers = build(m, ntests)

        pts = [zero] + bad + markers
        if len(set(pts)) != len(pts):
            raise AssertionError(f"{name}: declared points are not distinct")
        for e in range(ntests):
            if sum(markers[e]) != 0:
                raise AssertionError("a marker does not have coordinate sum 0")
        for j in range(m):
            if sum(bad[j]) != 1:
                raise AssertionError("a bad tip does not have coordinate sum 1")

        bad_radius = 0
        for h in H:
            K = support_of(h, m, ntests, Dsets, tests, zero, bad, markers)
            for j in range(m):
                got = selected_radius(K, j, d)
                want = F(0) if h in Dsets[j] else F(d - 1, 2)
                if got != want:
                    bad_radius += 1
                    print(f"   RADIUS MISMATCH {name} h={h} j={j}: {got} vs {want}")
        bad_marker = 0
        for h in H:
            K = support_of(h, m, ntests, Dsets, tests, zero, bad, markers)
            for e in range(ntests):
                if (markers[e] in K) != bool(tests[e][h]):
                    bad_marker += 1
        if bad_radius or bad_marker:
            raise AssertionError(f"{name}: embedding is wrong "
                                 f"({bad_radius} radius, {bad_marker} membership)")

        budgets = list(range(0, sum(costs) + 2))
        a = drd_curve(H, m, Dsets, tests, costs, budgets)
        b = physical_curve(H, m, ntests, Dsets, tests, costs, budgets, d, zero,
                           bad, markers)
        same = (a == b)
        c = physical_curve(H, m, ntests, Dsets, tests, costs, budgets, d, zero,
                           bad, markers, allow_bad_tip_probes=True)
        catalog_matters = (c != a)

        print(f"{name}:  d = {d}")
        print(f"   radius formula exact on all {len(H)}x{m} (world, decision) pairs;"
              f" marker membership exact on all {len(H)}x{ntests}")
        print(f"   optimal risk by budget  DRD       {[str(x) for x in a]}")
        print(f"                           physical  {[str(x) for x in b]}"
              f"   -> {'IDENTICAL' if same else 'DIFFERENT'}")
        print(f"   control, bad tips probeable       {[str(x) for x in c]}"
              f"   -> catalog restriction "
              f"{'MATTERS' if catalog_matters else 'is VACUOUS here'}")
        if not same:
            raise AssertionError(f"{name}: the embedding does NOT preserve the value")
        rows.append({"instance": name, "worlds": len(H), "decisions": m,
                     "tests": ntests, "d": d, "budgets": budgets,
                     "drd_optimal": [str(x) for x in a],
                     "physical_optimal": [str(x) for x in b],
                     "identical": same,
                     "with_bad_tip_probes": [str(x) for x in c],
                     "catalog_restriction_matters": catalog_matters})
        print()

    any_control = any(r["catalog_restriction_matters"] for r in rows)
    print("CONCLUSION (for the instances checked, exactly):")
    print("  every DRD instance above embeds into the Support model with the radius")
    print("  reading off safety and marker membership reading off the test, and the")
    print("  optimal adaptive risk-versus-budget curve is IDENTICAL in the two models.")
    print("  So in this model an acquisition theorem is a DRD theorem re-embedded.")
    if any_control:
        print("  The catalog restriction is REAL: letting the learner probe bad tips")
        print("  changes the curve, so the equivalence genuinely needs the declared")
        print("  markers to be the whole permitted catalog.")
    else:
        print("  WARNING: the bad-tip control never separated on these instances, so")
        print("  they do not demonstrate that the catalog restriction is needed.")
    print("\n  This is a NEGATIVE result about novelty, not a theorem about all")
    print("  instances: the algebra is a sketch, no Lean module is attempted here,")
    print("  and the embedding goes DRD -> Support only.")

    out = REPO / "research/worker_W_support_drd_20260914/W5_support_contains_drd.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "does the Support model contain the generic decision-region "
                    "problem?",
        "embedding": "d = m+2; anchor 0; bad tip b_j = 1 - (d-1) e_j; marker "
                     "p_e = z_e (e_{m+1} - e_{m+2}) with z_e > 0 distinct; "
                     "K_h = {0} u {b_j : h not in D_j} u {p_e : q_e(h)=1}",
        "verified_exactly": [
            "selectedRadius_{K_h}({j}) = 0 iff h in D_j, else (d-1)/2",
            "p_e in K_h iff q_e(h) = 1",
            "anchor, bad tips and markers pairwise distinct; markers have "
            "coordinate sum 0 and bad tips coordinate sum 1",
            "the optimal adaptive risk at every hard pathwise budget agrees between "
            "the DRD model and the physical model, over ALL deterministic trees",
        ],
        "catalog_side_condition": "the permitted queries must be the declared "
                                  "markers; a control that also allows probing bad "
                                  "tips changes the curve on at least one instance",
        "instances": rows,
        "not_established": [
            "an embedding DRD -> Support, not an equivalence of model classes",
            "numerical evidence on the listed instances, exact per instance; the "
            "algebra is a sketch and there is no Lean module",
            "no claim that the Support paper's own theorems are DRD theorems",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
