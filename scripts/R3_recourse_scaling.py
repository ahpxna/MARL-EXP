#!/usr/bin/env python3
"""R3: is the fixed-epsilon recourse R_eps bounded, or does it grow?

R_eps(f) = min over chains (S_k) of eps-good sets, |S_k| = k, of max_k |S_k \\ S_{k+1}|
i.e. the worst number of DELETIONS forced at a single budget step.

The published probe (`fixed_epsilon_recourse.py`, 72 exact DP searches) reports
max R_eps = 1 over m in {6,8,10} at eps in {1/4, 1/10, 1/20}. That shows R_eps is
small there, but it does not separate the two axes of the open question:

    (a) at FIXED eps, does R_eps grow with the number of components m?
    (b) at FIXED m, does R_eps grow as eps decreases to 0?

This probe sweeps both axes on the same exact rational DP (same layer
construction, same transition recurrence) and reports max R_eps per (eps, m)
cell. Exact `Fraction` arithmetic throughout; no floating point decides anything.

Raises on any internal inconsistency (the DP re-verifies its own optimal path).
Re-run:  python3 scripts/R3_recourse_scaling.py
"""
import hashlib
import json
import random
import time
from fractions import Fraction as F
from pathlib import Path

SRC = Path("research/worker_distinct_completion_20260913/fixed_epsilon_recourse.py")


def run(matrix, eps):
    """Exact DP, identical in structure to the published probe."""
    m = len(matrix)
    h = len(matrix[0])
    U = (1 << m) - 1
    denom = sum(max(row) - min(row) for row in matrix)
    if not denom:
        raise ValueError("zero normalization")
    vals = []
    layers = [[] for _ in range(m + 1)]
    for S in range(1 << m):
        residual = [sum(matrix[i][a] for i in range(m) if not S >> i & 1) for a in range(h)]
        vals.append(F(max(residual) - min(residual), denom))
    for k in range(m + 1):
        layer = [S for S in range(1 << m) if S.bit_count() == k]
        opt = min(vals[S] for S in layer)
        layers[k] = [S for S in layer if vals[S] <= opt + eps]
    D = {0: 0}
    parents = []
    for layer in layers[1:]:
        new = {}
        parent = {}
        for T in layer:
            value, S = min((max(v, (S & ~T).bit_count()), S) for S, v in D.items())
            new[T] = value
            parent[T] = S
        D = new
        parents.append(parent)
    T = U
    path = [T]
    for parent in reversed(parents):
        T = parent[T]
        path.append(T)
    path.reverse()
    value = D[U]
    assert max((S & ~T).bit_count() for S, T in zip(path, path[1:])) == value
    assert all(S in layer for S, layer in zip(path, layers))
    return value, [len(L) for L in layers]


def main():
    # EQUAL seed count at every m: a max over 8 draws is not comparable with a
    # max over 3, and comparing them would fake an m-trend. m = 14 and beyond
    # were SKIPPED (the transition step is quadratic in the layer size); stated,
    # not silently truncated.
    SEEDS = 6
    plan = {6: SEEDS, 8: SEEDS, 10: SEEDS, 12: SEEDS}
    eps_grid = [F(1, 4), F(1, 10), F(1, 20), F(1, 50), F(1, 200), F(1, 1000), F(0)]
    rows = []
    t0 = time.time()
    for m, nseed in plan.items():
        for seed in range(nseed):
            rng = random.Random(20260913 + 100 * m + seed)
            matrix = [[0] + [rng.randint(-4, 4) for _ in range(5)] for _ in range(m)]
            for eps in eps_grid:
                value, layer_sizes = run(matrix, eps)
                rows.append({"m": m, "seed": seed, "epsilon": str(eps),
                             "R_epsilon": value, "good_layer_sizes": layer_sizes})
        print(f"  m={m} done ({time.time()-t0:.1f}s)", flush=True)

    table = {}
    for r in rows:
        table.setdefault(r["epsilon"], {}).setdefault(r["m"], []).append(r["R_epsilon"])

    print(f"\nmax R_epsilon per (epsilon, m)   [{len(rows)} exact DP searches]")
    ms = sorted(plan)
    print("  epsilon  " + "".join(f"  m={m:<4}" for m in ms))
    grows_with_m = False
    for eps in eps_grid:
        k = str(eps)
        line = f"  {k:<8} "
        col = []
        for m in ms:
            v = max(table[k][m])
            col.append(v)
            line += f"  {v:<6}"
        print(line)
        if col[-1] > col[0]:
            grows_with_m = True

    max_by_eps = {str(e): max(max(table[str(e)][m]) for m in ms) for e in eps_grid}
    print("\nmax over all m, per epsilon:", max_by_eps)
    print("does the max grow with m at some fixed epsilon?", grows_with_m)

    out = Path("research/worker_distinct_completion_20260913/R3_recourse_scaling.json")
    out.write_text(json.dumps({
        "question": "at fixed epsilon does R_epsilon grow with m, or is it bounded?",
        "dp_source_mirrored_from": str(SRC),
        "dp_source_sha256": hashlib.sha256(SRC.read_bytes()).hexdigest() if SRC.exists() else None,
        "skipped": "m >= 14: transition step is quadratic in layer size, outside the time budget",
        "searches": len(rows),
        "max_R_epsilon_by_epsilon_and_m": {
            e: {str(m): max(table[e][m]) for m in ms} for e in table},
        "grows_with_m_at_some_fixed_epsilon": grows_with_m,
        "results": rows,
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
