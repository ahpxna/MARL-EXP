#!/usr/bin/env python3
"""R3 push: exact R_eps on the same seeded family, now out to m = 20.

Extends research/worker_distinct_completion_20260913/R3_recourse_scaling.json
(which stopped at m = 12 because the published transition step is quadratic in
the layer size).  Same generator, same seeds, same epsilon grid; EQUAL seed
count (6) at every m in {6,8,10,12,14,16,18,20}, so the per-cell maxima are
comparable.  m >= 18 is SKIPPED (timing measured, not assumed: see the
`skipped` field of the JSON).

It also checks, on every instance, the two exact claims of the accompanying
theorem (LeanStructuralRecourseUniformNestingV1):
  (i)  the nested top-span chain has excess <= min(tau_k, 2*A_k) <= (2/3)*D
       at every budget k, where A_k = span mass of the k largest-span
       components and tau_k = D - A_k;
  (ii) consequently R_eps = 0 for eps = 2/3.
Both are asserted, not printed.

Re-run:  python3 scripts/R3_recourse_push.py
"""
import hashlib
import json
import random
import sys
import time
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from R3_recourse_core import (good_layers, instance_data, solve,  # noqa: E402
                              solve_reference, topspan_chain)

ROOT = Path("/Users/phanan/cig-amf-main")
OUT = ROOT / "research/worker_distinct_completion_20260913/R3_recourse_push.json"
EPS_GRID = [F(1, 4), F(1, 10), F(1, 20), F(1, 50), F(1, 200), F(1, 1000), F(0)]
SEEDS = 6
MS = [6, 8, 10, 12, 14, 16, 18, 20]


def gen(m, seed):
    rng = random.Random(20260913 + 100 * m + seed)
    return [[0] + [rng.randint(-4, 4) for _ in range(5)] for _ in range(m)]


def theorem_check(matrix):
    """Exact check of the uniform-nesting bound.  Returns the worst excess as a
    Fraction of D.  Raises AssertionError if the proved bound is violated."""
    m = len(matrix)
    vals, D, spans = instance_data(matrix)
    chain = topspan_chain(matrix)
    order = sorted(range(m), key=lambda i: (-spans[i], i))
    worst = F(0)
    for k in range(m + 1):
        S = chain[k]
        assert S.bit_count() == k
        if k:
            assert chain[k - 1] & S == chain[k - 1], "chain not nested"
        layer_opt = None
        A = sum(spans[i] for i in order[:k])           # mass of k largest spans
        tau = D - A                                    # mass of the rest
        # exact optimum at this budget
        import numpy as np
        pc = np.bitwise_count(np.arange(1 << m, dtype=np.uint32))
        layer_opt = int(vals[np.flatnonzero(pc == k)].min())
        excess = int(vals[S]) - layer_opt
        assert excess <= min(tau, 2 * A), (
            f"claim (i) violated at k={k}: excess={excess} > min({tau},{2*A})")
        assert 3 * excess <= 2 * D, f"2/3 bound violated at k={k}"
        worst = max(worst, F(excess, D))
    return worst


def main():
    rows, t0 = [], time.time()
    worst_topspan = F(0)
    for m in MS:
        for seed in range(SEEDS):
            M = gen(m, seed)
            data = instance_data(M)
            worst_topspan = max(worst_topspan, theorem_check(M))
            # eps = 2/3 must give a nested chain (theorem consequence)
            assert solve(M, F(2, 3), _data=data)[0] == 0, "R_{2/3} != 0"
            for eps in EPS_GRID:
                value, path, sizes = solve(M, eps, _data=data)
                if m <= 8:   # cross-validate the fast DP against the published one
                    assert value == solve_reference(M, eps), "fast DP != published DP"
                rows.append({"m": m, "seed": seed, "epsilon": str(eps),
                             "R_epsilon": value, "good_layer_sizes": sizes})
        print(f"  m={m} done ({time.time()-t0:.1f}s)", flush=True)

    table = {}
    for r in rows:
        table.setdefault(r["epsilon"], {}).setdefault(r["m"], []).append(r["R_epsilon"])
    print(f"\nmax R_epsilon per (epsilon, m)   [{len(rows)} exact DP searches]")
    print("  epsilon  " + "".join(f"  m={m:<4}" for m in MS))
    for eps in EPS_GRID:
        k = str(eps)
        print(f"  {k:<8} " + "".join(f"  {max(table[k][m]):<6}" for m in MS))
    print(f"\nworst top-span-chain excess over all instances: {worst_topspan}"
          f" (proved bound 2/3)")

    OUT.write_text(json.dumps({
        "question": "at fixed epsilon does R_epsilon grow with m, or is it bounded?",
        "status": "NUMERICAL EVIDENCE on one seeded random family; not a theorem",
        "generator": "rows = [0] + 5 iid uniform ints in [-4,4]; seed 20260913+100m+s",
        "seeds_per_m": SEEDS, "m_grid": MS, "searches": len(rows),
        "skipped": "m >= 22 (measured: the eps=1/4 transition is ~10x per +2 in m; "
                   "m=20 eps=1/4 already takes ~143 s per instance); "
                   "h = 6 scenario columns only; entry range [-4,4] only",
        "core_sha256": hashlib.sha256((ROOT / "scripts/R3_recourse_core.py").read_bytes()).hexdigest(),
        "cross_validated_against_published_dp": "m in {6,8}, every epsilon cell",
        "max_R_epsilon_by_epsilon_and_m": {
            e: {str(m): max(table[e][m]) for m in MS} for e in table},
        "worst_topspan_chain_excess": str(worst_topspan),
        "results": rows,
    }, indent=2) + "\n")
    print(f"-> {OUT}")


if __name__ == "__main__":
    main()
