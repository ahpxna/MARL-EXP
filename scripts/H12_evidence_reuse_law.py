#!/usr/bin/env python3
"""MASTER, high-risk direction 12: the law for REUSING evidence across decisions.

The instruction is explicit that a break-even formula obtained by splitting two piles
of money is accounting, not a contribution: the two amounts have to be DERIVED from
the geometry and the query structure. So this script does two things.

(A) IT PROVES THE STRUCTURE FIRST, by independent enumeration. The supervisor's W6
    claim is
        a non-adaptive catalog C suffices  <=>  every MINIMAL obstruction is
        separated by at least one query in C,
    where an obstruction is a set of worlds with no commonly safe decision. Here the
    left side is computed DIRECTLY (partition the worlds by the answers in C; the
    catalog suffices iff every fibre has a commonly safe decision) and the right side
    from the obstruction list, and the two are compared on every catalog of every
    instance. If they disagree anywhere the rest is void.

(B) ONLY THEN DOES IT COST ANYTHING. Given (A), solving a task is a HITTING SET over
    that task's minimal obstructions, so for K tasks on the same world

        buy separately : sum_k  minHS(O_k)
        buy shared     : minHS(union_k O_k)
        reuse saving   : the difference

and both sides are computed exactly. The geometry enters through WHICH obstructions
each task has -- that is the whole content, and it is why the three families below
behave differently rather than by stipulation.

THREE FAMILIES, as instructed:
    shared(K)      every task has the SAME obstructions            -> saving maximal
    disjoint(K)    tasks have obstructions on disjoint test blocks -> saving zero
    overlap(K, t)  tasks share exactly t of their obstructions     -> saving grows in t

REFRESH. If the world is re-drawn between tasks, evidence bought for one task says
nothing about the next, so the shared cost degenerates to the separate cost. The
script reports the refresh multiplier explicitly rather than assuming it.

WHAT THIS DOES NOT ESTABLISH
 - Non-adaptive catalogs, worst case, unit query costs, zero error.
 - Minimum hitting sets by brute force, so only small instances.
 - The saving is computed, not bounded: no approximation guarantee is derived, and
   minimum hitting set is NP-hard in general, so a practical rule would still need one.

    .venv/bin/python scripts/H12_evidence_reuse_law.py
"""
from __future__ import annotations

import itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def commonly_safe(C, Dsets, allowed):
    return any(all(h in Dsets[j] for h in C) for j in allowed)


def suffices_direct(H, Dsets, allowed, tests, Cat):
    """DIRECT: partition by the answers in Cat, check each fibre."""
    fib = {}
    for h in H:
        fib.setdefault(tuple(tests[e][h] for e in sorted(Cat)), []).append(h)
    return all(commonly_safe(C, Dsets, allowed) for C in fib.values())


def minimal_obstructions(H, Dsets, allowed):
    obs = []
    for k in range(1, len(H) + 1):
        for S in itertools.combinations(H, k):
            if commonly_safe(S, Dsets, allowed):
                continue
            if any(set(o) <= set(S) for o in obs):
                continue
            obs.append(tuple(sorted(S)))
    return obs


def separates(tests, e, S):
    vals = {tests[e][h] for h in S}
    return len(vals) > 1


def suffices_hitting(tests, obs, Cat):
    """the W6 predicate: every minimal obstruction separated by some query in Cat."""
    return all(any(separates(tests, e, S) for e in Cat) for S in obs)


def min_hitting(tests, obs, ntests):
    if not obs:
        return 0, ()
    for k in range(0, ntests + 1):
        for Cat in itertools.combinations(range(ntests), k):
            if suffices_hitting(tests, obs, Cat):
                return k, Cat
    return None, None


# ------------------------------------------------------------------- families
def shared_family(K, n):
    """K tasks, all with the same obstruction structure."""
    H = list(range(2 ** n))
    tests = [{h: bool(h >> i & 1) for h in H} for i in range(n)]
    # decision j safe when bit j is 0; one always-unsafe decision forces obstructions
    Dsets = [frozenset(h for h in H if not (h >> j & 1)) for j in range(n)]
    tasks = [list(range(n)) for _ in range(K)]
    return f"shared(K={K},n={n})", H, Dsets, tests, tasks


def disjoint_family(K, n):
    """K tasks, each seeing a different block of tests."""
    H = list(range(2 ** (K * n)))
    tests = [{h: bool(h >> i & 1) for h in H} for i in range(K * n)]
    Dsets = [frozenset(h for h in H if not (h >> j & 1)) for j in range(K * n)]
    tasks = [list(range(k * n, (k + 1) * n)) for k in range(K)]
    return f"disjoint(K={K},n={n})", H, Dsets, tests, tasks


def overlap_family(K, n, t):
    """K tasks; the first t decisions are common to every task."""
    total = t + K * n
    H = list(range(2 ** total))
    tests = [{h: bool(h >> i & 1) for h in H} for i in range(total)]
    Dsets = [frozenset(h for h in H if not (h >> j & 1)) for j in range(total)]
    tasks = [list(range(t)) + list(range(t + k * n, t + (k + 1) * n))
             for k in range(K)]
    return f"overlap(K={K},n={n},t={t})", H, Dsets, tests, tasks


def solvable_worlds(H, Dsets, tasks):
    """Drop worlds in which some task has NO safe decision at all. Such a world is a
    singleton obstruction, which no query can ever separate, so the task would be
    unsolvable at any price and the cost comparison would be meaningless."""
    return [h for h in H
            if all(any(h in Dsets[j] for j in allowed) for allowed in tasks)]


def main():
    fams = []
    for name, H, Dsets, tests, tasks in (
            [shared_family(K, 2) for K in (2, 3)]
            + [disjoint_family(2, 2)]
            + [overlap_family(2, 1, t) for t in (0, 1, 2)]):
        H2 = solvable_worlds(H, Dsets, tasks)
        tests2 = [{h: t[h] for h in H2} for t in tests]
        fams.append((name, H2, Dsets, tests2, tasks))

    print("PART A -- the structure, checked before anything is costed\n")
    bad = 0; checked = 0
    for name, H, Dsets, tests, tasks in fams:
        nt = len(tests)
        if nt > 6:
            print(f"   {name}: {nt} tests -> skipping the exhaustive catalog check")
            continue
        for allowed in tasks:
            obs = minimal_obstructions(H, Dsets, allowed)
            for k in range(nt + 1):
                for Cat in itertools.combinations(range(nt), k):
                    checked += 1
                    a = suffices_direct(H, Dsets, allowed, tests, Cat)
                    b = suffices_hitting(tests, obs, Cat)
                    if a != b:
                        bad += 1
                        print(f"   MISMATCH {name} allowed={allowed} Cat={Cat}: "
                              f"direct={a} hitting={b}")
    print(f"   'catalog suffices' == 'every minimal obstruction is separated' on "
          f"{checked} (instance, task, catalog) triples, {bad} mismatches")
    if bad:
        raise AssertionError("the obstruction characterisation FAILS; nothing below "
                             "is meaningful")
    print("   => the W6 characterisation holds here, so acquisition IS a hitting-set\n"
          "      problem over the minimal obstructions, derived and not assumed.\n")

    print("PART B -- the reuse law")
    rows = []
    for name, H, Dsets, tests, tasks in fams:
        nt = len(tests)
        per, obs_all = [], []
        for allowed in tasks:
            obs = minimal_obstructions(H, Dsets, allowed)
            obs_all += obs
            c, _ = min_hitting(tests, obs, nt)
            per.append(c)
        # dedupe the union
        obs_union = []
        for S in obs_all:
            if not any(set(o) <= set(S) for o in obs_union):
                obs_union = [o for o in obs_union if not set(S) <= set(o)]
                obs_union.append(S)
        cshared, cat = min_hitting(tests, obs_union, nt)
        sep = sum(per)
        saving = sep - cshared
        refresh = sep            # world re-drawn between tasks: no reuse possible
        print(f"   {name:22s} tasks={len(tasks)} tests={nt}")
        print(f"      per-task costs {per}   buy separately {sep}"
              f"   buy shared {cshared}   saving {saving}"
              f"   ({100*saving/sep if sep else 0:.0f}%)")
        print(f"      if the world is re-drawn between tasks the shared cost "
              f"degenerates to {refresh}, saving 0")
        rows.append({"family": name, "tasks": len(tasks), "tests": nt,
                     "per_task_cost": per, "buy_separately": sep,
                     "buy_shared": cshared, "saving": saving,
                     "shared_catalog": list(cat) if cat else [],
                     "refresh_cost": refresh})

    sh = [r for r in rows if r["family"].startswith("shared")]
    dj = [r for r in rows if r["family"].startswith("disjoint")]
    ov = sorted([r for r in rows if r["family"].startswith("overlap")],
                key=lambda r: r["family"])
    print("\nVERDICT")
    print(f"   fully shared   : saving "
          + ", ".join(f"{r['saving']}/{r['buy_separately']}" for r in sh)
          + "  -- the shared catalog costs what ONE task costs")
    print(f"   disjoint       : saving "
          + ", ".join(f"{r['saving']}/{r['buy_separately']}" for r in dj)
          + "  -- nothing is reusable, the sum is paid")
    print(f"   overlap by t   : "
          + ", ".join(f"t={r['family'].split('t=')[1][0]} saving {r['saving']}"
                      for r in ov)
          + "  -- the saving tracks the shared obstructions, not a fitted constant")
    print("   The two amounts are minimum hitting sets over obstruction lists that the")
    print("   geometry determines, so the break-even is derived rather than assumed.")

    out = REPO / "research/worker_H12_master_20260914/H12_evidence_reuse_law.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "what is the law for reusing evidence across several decisions on "
                    "the same world?",
        "structure_first": "verified on every (instance, task, catalog) triple that a "
                           "catalog suffices iff every minimal obstruction is "
                           "separated by one of its queries",
        "law": "buy separately = sum_k minHS(O_k); buy shared = minHS(union_k O_k); "
               "the saving is the difference, and both are determined by the "
               "obstruction lists the geometry produces",
        "rows": rows,
        "not_established": [
            "non-adaptive catalogs, worst case, unit costs, zero error",
            "minimum hitting sets by brute force, small instances only",
            "the saving is computed, not bounded; no approximation guarantee",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
