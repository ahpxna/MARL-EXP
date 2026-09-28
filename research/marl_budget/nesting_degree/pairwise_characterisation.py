#!/usr/bin/env python3
"""Test: is the nesting degree of a system O_1..O_{m-1} (|O_k| = k) equal to
ceil(max_{j<k} |O_j \\ O_k| / 2)?  R*(O) = min over chains C_1 c ... c C_{m-1} of
max_k |C_k \\ O_k|, computed exactly by DP over subsets (bitmasks).
The lower bound R* >= ceil(maxpair/2) is proved (LeanMarlNestingDegreeGeneralV1.nesting_lower);
this script tests the UPPER direction.  Exhaustive for m <= 6 (all systems) and m = 7
(O_3 fixed by symmetry), random sampling for larger m.  Output: new JSON, refuses to overwrite."""
import itertools, json, random, sys, hashlib, pathlib, time
from math import comb

def popc(x): return bin(x).count("1")

def rstar(m, O):
    # O: dict k -> bitmask, k = 1..m-1
    INF = 10**9
    best = {0: 0}
    for k in range(1, m):
        nb = {}
        for c, v in best.items():
            for i in range(m):
                if not (c >> i) & 1:
                    d = c | (1 << i)
                    val = max(v, popc(d & ~O[k]))
                    if val < nb.get(d, INF):
                        nb[d] = val
        best = nb
    return min(best.values())

def maxpair(m, O):
    return max((popc(O[j] & ~O[k]) for j in range(1, m) for k in range(j + 1, m)), default=0)

def subsets(m, k):
    return [sum(1 << i for i in c) for c in itertools.combinations(range(m), k)]

def main():
    out = pathlib.Path("research/marl_budget/nesting_degree/pairwise_characterisation.json")
    if out.exists():
        print("refusing to overwrite", out); return 2
    random.seed(20260927)
    res = {"producer": "research/marl_budget/nesting_degree/pairwise_characterisation.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "rows": []}
    t0 = time.time()
    for m in range(2, 8):
        layers = {k: subsets(m, k) for k in range(1, m)}
        if m == 7:
            layers[3] = [0b0000111]
        systems = itertools.product(*[layers[k] for k in range(1, m)])
        n = 0; bad = 0; hist = {}; ex = None
        for sysv in systems:
            O = {k: sysv[k - 1] for k in range(1, m)}
            r = rstar(m, O); lb = (maxpair(m, O) + 1) // 2
            n += 1
            hist[r] = hist.get(r, 0) + 1
            if r != lb:
                bad += 1
                if ex is None: ex = {"O": {k: [i for i in range(m) if (O[k] >> i) & 1] for k in O}, "rstar": r, "ceil_half_maxpair": lb}
        res["rows"].append({"m": m, "mode": "exhaustive" + (" (O_3 fixed)" if m == 7 else ""), "systems": n,
                            "mismatch": bad, "rstar_hist": hist, "max_rstar": max(hist), "floor_m1_4": (m + 1) // 4, "example_mismatch": ex})
        print(f"m={m} systems={n} mismatch={bad} hist={hist} floor((m+1)/4)={(m+1)//4} ({time.time()-t0:.0f}s)", flush=True)
    for m in range(8, 12):
        N = 20000 if m <= 9 else 5000
        bad = 0; hist = {}; ex = None
        for _ in range(N):
            O = {k: sum(1 << i for i in random.sample(range(m), k)) for k in range(1, m)}
            r = rstar(m, O); lb = (maxpair(m, O) + 1) // 2
            hist[r] = hist.get(r, 0) + 1
            if r != lb:
                bad += 1
                if ex is None: ex = {"O": {k: [i for i in range(m) if (O[k] >> i) & 1] for k in O}, "rstar": r, "ceil_half_maxpair": lb}
        res["rows"].append({"m": m, "mode": f"random {N}", "systems": N, "mismatch": bad, "rstar_hist": hist,
                            "max_rstar_seen": max(hist), "floor_m1_4": (m + 1) // 4, "example_mismatch": ex})
        print(f"m={m} random={N} mismatch={bad} hist={hist} floor((m+1)/4)={(m+1)//4} ({time.time()-t0:.0f}s)", flush=True)
    out.write_text(json.dumps(res, indent=1)); print("wrote", out)
    return 0

if __name__ == "__main__":
    sys.exit(main())
