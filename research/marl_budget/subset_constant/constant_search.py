#!/usr/bin/env python3
"""Is the constant 2 in LeanMarlSubsetFrontierV1.subset_price_le sharp?
Maximise  F_k(0) / (d_k * delta)  over set functions f on m items (random restarts + hill
climbing on integer tables), where P_k is the gain prefix (ties broken adversarially: the
WORST tie-broken top-k set), d_k = min over optimal T of |P_k \\ T|, and delta is the local
i-versus-rest interaction.  The proved bound is ratio <= 2.  Exploratory; prints the best found.
Output: new JSON, refuses to overwrite."""
import itertools, json, random, sys, pathlib, hashlib
def run(m, restarts, steps, seed):
    rng = random.Random(seed)
    subsets = [frozenset(c) for r in range(m+1) for c in itertools.combinations(range(m), r)]
    def ratio(f):
        g = [f[frozenset([i])] - f[frozenset()] for i in range(m)]
        delta = max(abs(f[A | {i}] - f[A] - g[i]) for A in subsets for i in range(m) if i not in A)
        if delta <= 0: return 0.0, None
        best_r, arg = 0.0, None
        for k in range(1, m):
            ks = [S for S in subsets if len(S) == k]
            best = max(f[S] for S in ks)
            opt = [S for S in ks if f[S] >= best - 1e-12]
            # all top-k sets by gain (every member >= every non-member)
            for P in ks:
                if all(g[i] >= g[j] for i in P for j in range(m) if j not in P):
                    d = min(len(P - T) for T in opt)
                    if d == 0: continue
                    r = (best - f[P]) / (d * delta)
                    if r > best_r: best_r, arg = r, (k, sorted(P), d)
        return best_r, arg
    overall = (0.0, None, None)
    for _ in range(restarts):
        f = {S: rng.randint(-6, 6) for S in subsets}
        cur, arg = ratio(f)
        for _ in range(steps):
            S = rng.choice(subsets); old = f[S]; f[S] = old + rng.choice([-2, -1, 1, 2])
            new, a2 = ratio(f)
            if new >= cur: cur, arg = new, a2
            else: f[S] = old
        if cur > overall[0]: overall = (cur, arg, {"".join(map(str, sorted(S))) or "-": v for S, v in f.items()})
    return overall
if __name__ == "__main__":
    out = pathlib.Path("research/marl_budget/subset_constant/constant_search.json")
    if out.exists(): print("refusing to overwrite"); sys.exit(2)
    res = {"producer": str(pathlib.Path(__file__)), "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(), "rows": []}
    for m, restarts, steps in ((2, 200, 200), (3, 200, 400), (4, 100, 600), (5, 40, 800)):
        r, arg, f = run(m, restarts, steps, 7 + m)
        res["rows"].append({"m": m, "max_ratio_found": r, "where": arg, "table": f})
        print(f"m={m}: max F/(d*delta) found = {r:.4f} at {arg}", flush=True)
    out.write_text(json.dumps(res, indent=1)); print("wrote", out)
