#!/usr/bin/env python3
"""Structural target C: close the constant, do not grow the census.

The interval is still 1/2 <= eps_nest* <= 2/3, and `G5_nesting_constant_search.py`
found nothing above 1/2 in an EXHAUSTIVE two-action sweep. Two branches were asked
for; this file runs both, and neither is another census.

BRANCH 1 -- a RULE, which is what a proof of the 1/2 upper bound would have to supply.
An exhaustive search shows `min over pi` never exceeds 1/2, but a search is not a
proof. A proof needs an ORDERING RULE together with an argument. So here four concrete
rules are run against EVERY instance of the exhaustive family, and the question asked
is the sharp one: does some rule achieve `eps <= 1/2` on every instance? A rule that
does is a proof candidate; a rule that fails is eliminated, with the failing instance
printed. This narrows what has to be proved instead of adding evidence for it.

  desc      remove the largest |g| first
  greedy_R  at each step remove the element leaving the smallest |remaining sum|
  greedy_reg at each step remove the element leaving the smallest regret at that budget
  altern    largest |g| first, but alternating sign whenever both signs remain

BRANCH 2 -- MORE ACTIONS, where the objective stops being a subset sum. With h = 2 the
loss is |sum of the omitted g_i| / sum|g_i|, and that one-dimensional structure is
exactly why 1/2 is never beaten: a ranking that removes the large-|g| entries first
keeps every prefix within 1/2. With h >= 3 the loss is a max-minus-min of an h-vector
and no longer collapses to a signed scalar sequence, which is where an instance forcing
every ranking above 1/2 would have to live. This part scans h = 3 and h = 4 at sizes
the two-action sweep could not reach.

WHAT THIS DOES NOT ESTABLISH
 - A rule surviving every instance of the searched family is a proof CANDIDATE, not a
   proof; the family is bounded in size and alphabet.
 - Branch 2 is a bounded scan, not exhaustive, and is labelled as such.
 - No improvement of the 2/3 upper bound is derived.

    .venv/bin/python scripts/G6_nesting_upper_rule.py
"""
from __future__ import annotations

from fractions import Fraction as F
import itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


# ------------------------------------------------------------ two actions
def opt_per_budget(g):
    n = len(g)
    return {k: min(abs(sum(g[i] for i in range(n) if i not in T))
                   for T in itertools.combinations(range(n), k))
            for k in range(n + 1)}


def eps_of(g, pi, opt, D):
    n = len(g)
    run = sum(g)
    worst = 0
    for k in range(n + 1):
        if k > 0:
            run -= g[pi[k - 1]]
        worst = max(worst, abs(run) - opt[k])
    return F(worst, D)


def rule_desc(g):
    return tuple(sorted(range(len(g)), key=lambda i: (-abs(g[i]), i)))


def rule_greedy_R(g):
    n = len(g); left = set(range(n)); run = sum(g); order = []
    while left:
        best = min(left, key=lambda i: (abs(run - g[i]), i))
        run -= g[best]; left.discard(best); order.append(best)
    return tuple(order)


def rule_greedy_reg(g):
    n = len(g); opt = opt_per_budget(g)
    left = set(range(n)); run = sum(g); order = []
    for k in range(1, n + 1):
        best = min(left, key=lambda i: (abs(run - g[i]) - opt[k], i))
        run -= g[best]; left.discard(best); order.append(best)
    return tuple(order)


def rule_altern(g):
    n = len(g)
    pos = sorted([i for i in range(n) if g[i] > 0], key=lambda i: (-abs(g[i]), i))
    neg = sorted([i for i in range(n) if g[i] < 0], key=lambda i: (-abs(g[i]), i))
    zer = [i for i in range(n) if g[i] == 0]
    order = []
    run = sum(g)
    while pos or neg:
        take_pos = (run > 0 and pos) or (not neg)
        src = pos if take_pos else neg
        i = src.pop(0)
        run -= g[i]; order.append(i)
    return tuple(order + zer)


RULES = {"desc": rule_desc, "greedy_R": rule_greedy_R,
         "greedy_reg": rule_greedy_reg, "altern": rule_altern}


def canonical(m, lo, hi):
    seen = set()
    for g in itertools.combinations_with_replacement(range(lo, hi + 1), m):
        if all(v == 0 for v in g):
            continue
        key = min(g, tuple(sorted(-v for v in g)))
        if key in seen:
            continue
        seen.add(key)
        yield key


def branch1():
    print("BRANCH 1 -- does a RULE reach 1/2 on every instance?")
    half = F(1, 2)
    stats = {r: {"max": F(0), "worst_g": None, "fails": 0, "fail_example": None}
             for r in RULES}
    total = 0
    for m, lo, hi in ((3, -3, 3), (4, -3, 3), (5, -3, 3), (6, -2, 2)):
        for g in canonical(m, lo, hi):
            total += 1
            D = sum(abs(v) for v in g)
            opt = opt_per_budget(g)
            for name, rule in RULES.items():
                e = eps_of(g, rule(list(g)), opt, D)
                st = stats[name]
                if e > st["max"]:
                    st["max"], st["worst_g"] = e, g
                if e > half:
                    st["fails"] += 1
                    if st["fail_example"] is None:
                        st["fail_example"] = (g, str(e))
    print(f"   {total} instances (exhaustive up to the stated size and alphabet)")
    out = []
    for name, st in stats.items():
        ok = st["fails"] == 0
        print(f"      {name:11s} max eps = {str(st['max']):>7s} "
              f"({float(st['max']):.4f}) at g={st['worst_g']}"
              f"   -> {'ALWAYS <= 1/2' if ok else str(st['fails']) + ' instances EXCEED 1/2'}")
        if not ok:
            print(f"                   first failure: g={st['fail_example'][0]}, "
                  f"eps={st['fail_example'][1]}")
        out.append({"rule": name, "max_eps": str(st["max"]),
                    "argmax_g": list(st["worst_g"]) if st["worst_g"] else None,
                    "instances_above_half": st["fails"],
                    "first_failure": (None if ok else
                                      {"g": list(st["fail_example"][0]),
                                       "eps": st["fail_example"][1]}),
                    "always_at_most_half": ok})
    survivors = [o["rule"] for o in out if o["always_at_most_half"]]
    if survivors:
        print(f"   SURVIVING RULES: {survivors}.  Each is a proof candidate for the")
        print("   1/2 upper bound in the two-action case: what remains is an argument")
        print("   that the rule's prefix stays within 1/2 of the per-budget optimum.")
    else:
        print("   No rule survives. Any proof of the 1/2 upper bound must use an")
        print("   ordering more adaptive than the four tried.")
    return {"instances": total, "rules": out, "survivors": survivors}


# ------------------------------------------------------- three or more actions
def eps_general(rows):
    m = len(rows); h = len(rows[0])
    D = sum(max(r) - min(r) for r in rows)
    if D == 0:
        return F(0)

    def Lnum(S):
        vals = [sum(rows[i][a] for i in range(m) if i not in S) for a in range(h)]
        return max(vals) - min(vals)

    opt = {k: min(Lnum(set(T)) for T in itertools.combinations(range(m), k))
           for k in range(m + 1)}
    return min(F(max(Lnum(set(pi[:k])) - opt[k] for k in range(m + 1)), D)
               for pi in itertools.permutations(range(m)))


def branch2():
    print("\nBRANCH 2 -- more actions, a bounded SCAN (not exhaustive)")
    out = []
    best_overall = (F(0), None, None)
    for h, m, alpha in ((3, 5, (-1, 0, 1)), (3, 4, (-2, -1, 0, 1, 2)),
                        (4, 4, (-1, 0, 1)), (4, 3, (-2, -1, 0, 1, 2))):
        rowset = list(itertools.product(alpha, repeat=h))
        best = (F(0), None)
        n = 0
        for rows in itertools.combinations_with_replacement(rowset, m):
            n += 1
            e = eps_general(list(rows))
            if e > best[0]:
                best = (e, rows)
        print(f"   h={h} m={m} entries {alpha}: {n} instances -> max eps_nest = "
              f"{best[0]} = {float(best[0]):.6f}")
        out.append({"actions": h, "components": m, "alphabet": list(alpha),
                    "instances": n, "max_eps": str(best[0]),
                    "argmax": [list(r) for r in best[1]] if best[1] else None})
        if best[0] > best_overall[0]:
            best_overall = (best[0], h, best[1])
    print(f"   best over every scan: {best_overall[0]} = "
          f"{float(best_overall[0]):.6f} at h={best_overall[1]}")
    return out, best_overall


def main():
    b1 = branch1()
    b2, best = branch2()
    print("\nVERDICT")
    if best[0] > F(1, 2):
        print(f"   An instance with eps_nest = {best[0]} > 1/2 was found at "
              f"h = {best[1]} actions. The lower end of [1/2, 2/3] MOVES.")
    else:
        print("   Nothing above 1/2 anywhere, including at 3 and 4 actions. Together")
        print("   with branch 1 that is a coherent picture: if a rule provably keeps")
        print("   every prefix within 1/2, then 1/2 is the answer and the 2/3 upper")
        print("   bound is simply not tight. The remaining work is the ARGUMENT for a")
        print("   surviving rule, not more search.")
    out = REPO / "research/worker_G6_nesting_20260914/G6_nesting_upper_rule.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "branch1_rules": b1, "branch2_scan": b2,
        "best_found": str(best[0]),
        "beats_half": best[0] > F(1, 2),
        "not_established": [
            "a rule surviving the searched family is a proof candidate, not a proof",
            "branch 2 is a bounded scan, not exhaustive",
            "no improvement of the 2/3 upper bound is derived",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
