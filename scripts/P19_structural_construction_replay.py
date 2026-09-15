#!/usr/bin/env python3
"""P19 -- Structural: the explicit all-m construction, with a REPLAYABLE witness.

Audit item T2: `P14_structural_family_allm.json` stores only values, column counts and
support sizes.  A verifier cannot replay the certificate without re-running a solver.
This script stores, for every m:

  * the labelled component list of g_m = (-3, (-1)^p, (+1)^q, 3);
  * the m-1 explicit orderings as LABEL sequences (so equal values stay distinguishable);
  * the uniform mixture weight 1/(m-1);
  * the per-budget defect vector of every ordering;
  * the resulting V_avg, V_path and their ratio, in exact Fractions.

It also verifies, independently of any solver:

  (a) every ordering is a permutation of g_m (multiset check on labels);
  (b) its defect profile is 0...0, 2, 0...0 with the 2 at exactly budget j;
  (c) the mixture is balanced: every budget carries expectation 2/((m+4)(m-1));
  (d) for small m, by exhaustive search over ALL labelled permutations, that no
      ordering has total defect < 2 -- the lower bound the Lean module proves in
      general (`StructuralFamilyLower.two_le_totalDefect`).

The Lean counterparts are `LeanStructuralFamilyLowerV1` (lower bound + mixture) and
`LeanStructuralFamilyUpperV1` (this construction, for every p, q with q <= p <= q+1).
"""
import json, itertools, os, sys
from fractions import Fraction as F

OUT = "research/worker_P19_structural_20260915"


def altFrom(s, a, b):
    """Greedy alternation: always step back towards 0."""
    out = []
    while a + b > 0:
        if s >= 0:
            if a == 0:
                out.append(1); s += 1; b -= 1
            else:
                out.append(-1); s -= 1; a -= 1
        else:
            if b == 0:
                out.append(-1); s -= 1; a -= 1
            else:
                out.append(1); s += 1; b -= 1
    return out


def pq(m):
    return (m - 2 + 1) // 2, (m - 2) // 2


def order_odd(t, p, q):
    return altFrom(0, t, t) + [-3, 3] + altFrom(0, p - t, q - t)


def order_even(t, p, q):
    return altFrom(0, t, t - 1) + [3, -3] + altFrom(-1, p - t, q + 1 - t)


def schedule(m, j):
    p, q = pq(m)
    if j % 2 == 1:
        return order_odd((j - 1) // 2, p, q)
    return order_even(j // 2, p, q)


def dfc(s):
    return abs(s) - abs(s) % 2


def defect_profile(l):
    s = 0
    out = []
    for x in l:
        s += x
        out.append(dfc(s))
    return out


def components(m):
    p, q = pq(m)
    return [-3] + [-1] * p + [1] * q + [3]


def label_sequence(m, seq):
    """Turn a value sequence into a LABEL sequence over the labelled components,
    consuming each label once.  Fails loudly if it is not a permutation."""
    comps = components(m)
    pool = {}
    for idx, v in enumerate(comps):
        pool.setdefault(v, []).append(idx)
    labels = []
    for v in seq:
        if v not in pool or not pool[v]:
            raise AssertionError(f"m={m}: value {v} not available -- not a permutation")
        labels.append(pool[v].pop(0))
    if any(pool[v] for v in pool):
        raise AssertionError(f"m={m}: leftover components -- not a permutation")
    return labels


def brute_lower(m):
    """Exhaustive over ALL labelled permutations: the minimum total defect."""
    comps = components(m)
    best = None
    for perm in itertools.permutations(range(m)):
        seq = [comps[i] for i in perm]
        tot = sum(defect_profile(seq)[:-1])
        if best is None or tot < best:
            best = tot
    return best


def main():
    os.makedirs(OUT, exist_ok=True)
    rows = []
    mmax = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    for m in range(5, mmax + 1):
        p, q = pq(m)
        assert q <= p <= q + 1, (m, p, q)
        D = m + 4
        assert sum(abs(v) for v in components(m)) == D
        orders, profiles, labels = [], [], []
        for j in range(1, m):
            seq = schedule(m, j)
            lab = label_sequence(m, seq)
            prof = defect_profile(seq)
            # (b) the profile is 0...0,2,0...0 with the 2 at budget j
            budgets = prof[: m - 1]
            expected = [0] * (m - 1)
            expected[j - 1] = 2
            assert budgets == expected, (m, j, budgets)
            assert prof[-1] == 0, (m, j, prof[-1])
            orders.append(seq)
            labels.append(lab)
            profiles.append(budgets)
        w = F(1, m - 1)
        # (c) balanced: every budget has the same expectation
        exp_per_budget = [sum(w * F(profiles[i][k], D) for i in range(m - 1))
                          for k in range(m - 1)]
        target = F(2, D * (m - 1))
        assert all(e == target for e in exp_per_budget), (m, exp_per_budget[:3], target)
        v_avg = max(exp_per_budget)
        v_path = sum(w * max(F(pr, D) for pr in profiles[i]) for i in range(m - 1))
        assert v_avg == F(2, D * (m - 1)), (m, v_avg)
        assert v_path == F(2, D), (m, v_path)
        assert v_path / v_avg == m - 1
        row = {
            "m": m, "p": p, "q": q, "D": D,
            "components": components(m),
            "V_avg": str(v_avg), "V_path": str(v_path), "ratio": m - 1,
            "eps_nest": str(F(2, D)),
        }
        if m <= 30:
            row["orderings_labels"] = labels
            row["orderings_values"] = orders
            row["defect_profiles"] = profiles
            row["mixture_weight"] = str(w)
        if m <= 9:
            bl = brute_lower(m)
            assert bl == 2, (m, bl)
            row["brute_force_min_total_defect"] = bl
            row["brute_force_permutations"] = 1
            for i in range(2, m + 1):
                row["brute_force_permutations"] *= i
        rows.append(row)

    out = {
        "script": "P19_structural_construction_replay.py",
        "family": "g_m = (-3, (-1)^p, (+1)^q, 3), p=ceil((m-2)/2), q=floor((m-2)/2)",
        "m_range": [5, mmax],
        "checks": {
            "permutation_of_g_m": "labelled multiset consumed exactly",
            "defect_profile": "0...0,2,0...0 with the 2 at budget j, for every j",
            "balanced_mixture": "every budget expectation equals 2/((m+4)(m-1))",
            "brute_force_lower_bound_m_le_9": "min total defect over ALL labelled permutations is 2",
        },
        "law": {
            "V_avg": "2/((m+4)(m-1))",
            "V_path": "2/(m+4)",
            "ratio": "m-1",
        },
        "lean": {
            "lower": "LeanStructuralFamilyLowerV1 (two_le_totalDefect, avg_lower, path_lower)",
            "upper": "LeanStructuralFamilyUpperV1 (exists_one_defect)",
        },
        "not_established": [
            "The separation level 2/(m+4) DECREASES in m: this is not an unbounded "
            "separation at a fixed normalised epsilon.",
            "Orderings are stored only for m <= 30 to keep the artifact small; the "
            "construction is deterministic and regenerable for every m.",
        ],
        "rows": rows,
    }
    path = os.path.join(OUT, "P19_structural_construction_replay.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"PASS  m=5..{mmax}: construction verified, mixture balanced, "
          f"V_path/V_avg = m-1 exactly; brute-force lower bound 2 for m<=9")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
