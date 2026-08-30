#!/usr/bin/env python3
"""Exact-integer falsification search for V7 structural characterizations."""
from __future__ import annotations

import argparse
import itertools
import json
import random
from collections import Counter


def popcount(mask: int) -> int:
    return mask.bit_count()


def objective_values(m: int, support: tuple[tuple[int, ...], ...], slopes: tuple[int, ...]):
    full_mask = (1 << m) - 1
    values = {}
    for selected in range(1 << m):
        omitted = full_mask ^ selected
        row = [sum(slopes[j] * a[j] for j in range(m) if omitted & (1 << j)) for a in support]
        values[selected] = max(row) - min(row)  # exactly 2 * selectedRadius
    return values


def optimal_levels(m: int, obj: dict[int, int]):
    out = {}
    for k in range(m + 1):
        family = [s for s in range(1 << m) if popcount(s) == k]
        best = min(obj[s] for s in family)
        out[k] = frozenset(s for s in family if obj[s] == best)
    return out


def nested_chain_exists(m: int, opt) -> bool:
    reachable = {0}
    for k in range(1, m + 1):
        reachable = {s for s in opt[k] if any((p & s) == p for p in reachable)}
        if not reachable:
            return False
    return True


def weak_adjacent_edges(m: int, opt) -> bool:
    return all(any((s & t) == s for s in opt[k] for t in opt[k + 1]) for k in range(m))


def all_optima_extend(m: int, opt) -> bool:
    return all(all(any((s & t) == s for t in opt[k + 1]) for s in opt[k]) for k in range(m))


def all_optima_accessible(m: int, opt) -> bool:
    return all(all(any((s & t) == t for t in opt[k - 1]) for s in opt[k]) for k in range(1, m + 1))


def submodular(m: int, obj) -> bool:
    for a in range(1 << m):
        for b in range(1 << m):
            if obj[a] + obj[b] < obj[a | b] + obj[a & b]:
                return False
    return True


def supermodular(m: int, obj) -> bool:
    for a in range(1 << m):
        for b in range(1 << m):
            if obj[a] + obj[b] > obj[a | b] + obj[a & b]:
                return False
    return True


def monotone_nonincreasing(m: int, obj) -> bool:
    return all(obj[s | (1 << j)] <= obj[s]
               for s in range(1 << m) for j in range(m) if not s & (1 << j))


def mconvex_equal_cardinality(m: int, obj) -> bool:
    for k in range(1, m):
        family = [s for s in range(1 << m) if popcount(s) == k]
        for x in family:
            for y in family:
                for i in range(m):
                    if x & (1 << i) and not y & (1 << i):
                        ok = False
                        for j in range(m):
                            if y & (1 << j) and not x & (1 << j):
                                xp = (x ^ (1 << i)) | (1 << j)
                                yp = (y ^ (1 << j)) | (1 << i)
                                if obj[x] + obj[y] >= obj[xp] + obj[yp]:
                                    ok = True
                                    break
                        if not ok:
                            return False
    return True


def deficit_values(m: int, obj, slopes):
    full_mask = (1 << m) - 1
    out = {}
    for omitted in range(1 << m):
        selected = full_mask ^ omitted
        modular = sum(abs(slopes[j]) for j in range(m) if omitted & (1 << j))
        out[omitted] = modular - obj[selected]
    return out


def coextremizable(m, support, slopes):
    max_bits = tuple(1 if s > 0 else 0 for s in slopes)
    min_bits = tuple(0 if s > 0 else 1 for s in slopes)
    return max_bits in support and min_bits in support


def properties(m, support, slopes):
    obj = objective_values(m, support, slopes)
    opt = optimal_levels(m, obj)
    deficit = deficit_values(m, obj, slopes)
    return {
        "scalar_prefix": nested_chain_exists(m, opt),
        "weak_adjacent_optimal_extension": weak_adjacent_edges(m, opt),
        "all_optima_extend": all_optima_extend(m, opt),
        "all_optima_accessible": all_optima_accessible(m, opt),
        "objective_submodular": submodular(m, obj),
        "objective_supermodular": supermodular(m, obj),
        "objective_monotone_nonincreasing": monotone_nonincreasing(m, obj),
        "objective_mconvex_equal_cardinality": mconvex_equal_cardinality(m, obj),
        "deficit_submodular": submodular(m, deficit),
        "deficit_supermodular": supermodular(m, deficit),
        "global_extrema_compatible": coextremizable(m, support, slopes),
    }, obj, opt


def encode_world(m, support, slopes, obj, opt):
    return {
        "m": m,
        "support": [list(a) for a in support],
        "slopes": list(slopes),
        "objective_twice_radius_by_selected_mask": {str(k): v for k, v in obj.items()},
        "optimal_masks_by_cardinality": {str(k): sorted(v) for k, v in opt.items()},
    }


def add_world(acc, m, support, slopes, corpus):
    props, obj, opt = properties(m, support, slopes)
    rankable = props["scalar_prefix"]
    acc["worlds"] += 1
    acc["rankable"] += int(rankable)
    for name, value in props.items():
        acc["property_true_counts"][name] += int(value)
        relation = "matches" if value == rankable else ("false_positive" if value else "false_negative")
        acc["comparison_counts"][name][relation] += 1
        if relation != "matches" and name not in acc["minimal_counterexamples"][relation]:
            payload = encode_world(m, support, slopes, obj, opt)
            payload["corpus"] = corpus
            payload["candidate_value"] = value
            payload["scalar_prefix"] = rankable
            acc["minimal_counterexamples"][relation][name] = payload


def valid_projection(support, m):
    return all({a[j] for a in support} == {0, 1} for j in range(m))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--random-per-m", type=int, default=5000)
    parser.add_argument("--seed", type=int, default=7401)
    parser.add_argument("--out", required=True)
    args = parser.parse_args()
    acc = {
        "protocol": "structural_candidate_falsification_v1_exact_integer",
        "worlds": 0,
        "rankable": 0,
        "property_true_counts": Counter(),
        "comparison_counts": {},
        "minimal_counterexamples": {"false_positive": {}, "false_negative": {}},
        "corpus_counts": Counter(),
    }
    names = [
        "scalar_prefix", "weak_adjacent_optimal_extension", "all_optima_extend",
        "all_optima_accessible", "objective_submodular", "objective_supermodular",
        "objective_monotone_nonincreasing", "objective_mconvex_equal_cardinality",
        "deficit_submodular", "deficit_supermodular", "global_extrema_compatible",
    ]
    acc["comparison_counts"] = {n: Counter() for n in names}

    # Exact reproduction of the existing 12,352-world m=3 corpus.
    m = 3
    full = tuple(itertools.product((0, 1), repeat=m))
    for mask in range(1, 1 << len(full)):
        support = tuple(a for bit, a in enumerate(full) if mask & (1 << bit))
        if not valid_projection(support, m):
            continue
        for slopes in itertools.product((-2, -1, 1, 2), repeat=m):
            add_world(acc, m, support, slopes, "exhaustive_m3_existing")
            acc["corpus_counts"]["exhaustive_m3_existing"] += 1

    # Tractable exhaustive m=4 slice: every support with full projections,
    # fixed nondegenerate slopes.  Sign/scale diversity is covered below.
    m = 4
    full = tuple(itertools.product((0, 1), repeat=m))
    slopes = (-3, -1, 2, 4)
    for mask in range(1, 1 << len(full)):
        support = tuple(a for bit, a in enumerate(full) if mask & (1 << bit))
        if not valid_projection(support, m):
            continue
        add_world(acc, m, support, slopes, "exhaustive_m4_all_supports_fixed_slopes")
        acc["corpus_counts"]["exhaustive_m4_all_supports_fixed_slopes"] += 1

    rng = random.Random(args.seed)
    slope_values = (-4, -3, -2, -1, 1, 2, 3, 4)
    for m in (4, 5, 6):
        full = tuple(itertools.product((0, 1), repeat=m))
        count = 0
        while count < args.random_per_m:
            p = rng.uniform(0.12, 0.9)
            support = tuple(a for a in full if rng.random() < p)
            if not support or not valid_projection(support, m):
                continue
            slopes = tuple(rng.choice(slope_values) for _ in range(m))
            corpus = f"random_m{m}"
            add_world(acc, m, support, slopes, corpus)
            acc["corpus_counts"][corpus] += 1
            count += 1

    # Exact encodings of the frozen W1/W2/W3 geometry witnesses.
    frozen_witnesses = [
        (3, ((0, 0, 0), (0, 1, 1), (1, 0, 0)), (-2, 1, -3), "frozen_W1"),
        (2, ((0, 0), (1, 1)), (-1, 1), "frozen_W2"),
        (3, ((0, 0, 1), (0, 1, 0), (1, 0, 0)), (-3, -3, 1), "frozen_W3"),
    ]
    for m, support, slopes, corpus in frozen_witnesses:
        add_world(acc, m, support, slopes, corpus)
        acc["corpus_counts"][corpus] += 1

    acc["property_true_counts"] = dict(acc["property_true_counts"])
    acc["comparison_counts"] = {k: dict(v) for k, v in acc["comparison_counts"].items()}
    acc["corpus_counts"] = dict(acc["corpus_counts"])
    with open(args.out, "w", encoding="utf-8") as handle:
        json.dump(acc, handle, indent=2, sort_keys=True)
        handle.write("\n")
    print(json.dumps({
        "worlds": acc["worlds"],
        "rankable": acc["rankable"],
        "corpus_counts": acc["corpus_counts"],
        "comparison_counts": acc["comparison_counts"],
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
