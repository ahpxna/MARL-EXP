#!/usr/bin/env python3
"""P1, EXPLORATORY: is there a D6 world where NESTING itself costs more than one revision?

Two parts.

(A) EXACT combinatorics, independent of the loss.  For budget k let O_k be one optimal k-set.
    If for every system (O_k)_k some ranking pi has |pi_k \\ O_k| <= R at every k, then
    G(R) = min_pi max_k min_{|S'|=k, |S' \\ pi_k| <= R} (l_{S'} - l*_k) = 0 for EVERY set loss l
    (ties only add optimal sets).  We count the systems with no such ranking, for small (m, R).
    Budgets with min(k, m-k) <= R never bind.  Symmetry: one binding O_k is fixed to {0..k-1}.

(B) EXPLORATORY hill-climb (labelled; not a proof, not an exhaustive search) for an integer
    world F on {0,1}^m with the corner reference (cornerQ2-style q_i(u) = [u = 0]) whose
    D6 compression loss l_S = osc(F - sum_{j in S} productResponse_j)/2 has, as its UNIQUE
    optima at the binding budgets, a system from (A) that no ranking covers within R = 1.
    Then G(1) > 0 exactly.  Every reported world is re-evaluated from scratch in exact integer
    arithmetic (doubled losses are integers under the corner reference), including G(R) by a
    prefix DP over all subsets and delta_box = max |mixedDifference|.

Transcription (same as d6_frontier_exact.py): corner reference gives productResponse_j(u) =
F(e_j^u); retainedResidual_S(x) = F(x) - sum_{j in S} F(e_j^{x_j}); mixedDifference as in
LeanProductSurrogateV4.mixedDifference; delta_box = its max absolute value.
"""
import hashlib
import itertools
import json
import os
import random
import sys
import time

import numpy as np

REPO = "/Users/phanan/cig-amf-main"
OUT_DIR = os.path.join(REPO, "research/marl_budget/P1_d6_frontier")


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def popcount(x):
    return bin(x).count("1")


# ---------------------------------------------------------------- (A) combinatorics
def chain_exists(m, O, R):
    """Is there a ranking whose k-prefix is within R of O[k] for every k in O?"""
    reach = {0}
    for k in range(1, m + 1):
        new = set()
        for A in reach:
            for j in range(m):
                if not (A >> j) & 1:
                    B = A | (1 << j)
                    if k in O and popcount(B & ~O[k]) > R:
                        continue
                    new.add(B)
        reach = new
        if not reach:
            return False
    return True


def bad_systems(m, R, limit_examples=5):
    ks = [k for k in range(1, m) if min(k, m - k) > R]
    if not ks:
        return {"m": m, "R": R, "binding_k": ks, "systems": 1, "bad": 0, "examples": []}
    bysize = {k: [x for x in range(1 << m) if popcount(x) == k] for k in ks}
    kfix = ks[len(ks) // 2]
    others = [k for k in ks if k != kfix]
    tot = bad = 0
    examples = []
    for combo in itertools.product(*[bysize[k] for k in others]):
        O = dict(zip(others, combo))
        O[kfix] = (1 << kfix) - 1
        tot += 1
        if not chain_exists(m, O, R):
            bad += 1
            if len(examples) < limit_examples:
                examples.append({str(k): [j for j in range(m) if (O[k] >> j) & 1] for k in sorted(O)})
    return {"m": m, "R": R, "binding_k": ks, "fixed_k": kfix, "systems": tot, "bad": bad,
            "examples": examples}


# ---------------------------------------------------------------- (B) D6 loss, integers
class World:
    def __init__(self, m):
        self.m = m
        self.N = 1 << m
        idx = np.arange(self.N)
        self.AND = idx[:, None] & idx[None, :]          # AND[S, x] = S & x
        self.pc = np.array([popcount(x) for x in range(self.N)])
        self.bits = np.array([[(x >> j) & 1 for j in range(m)] for x in range(self.N)])

    def two_losses(self, F):
        """2 l_S for every S (integer).  Residual_S(x) = F[x] - sum_{j in S} F[e_j^{x_j}]
        = F[x] - |S| F[0] - cs[S & x], cs[mask] = sum_{j in mask} (F[e_j] - F[0])."""
        c = np.array([F[1 << j] - F[0] for j in range(self.m)], dtype=np.int64)
        cs = self.bits @ c
        Rm = F[None, :] - cs[self.AND]
        return Rm.max(axis=1) - Rm.min(axis=1)

    def delta_box(self, F):
        best = 0
        for i in range(self.m):
            lo = [y for y in range(self.N) if not (y >> i) & 1]
            rho = [int(F[y | (1 << i)] - F[y]) for y in lo]
            best = max(best, max(rho) - min(rho))
        return best

    def scores(self, F):
        return [abs(int(F[1 << j] - F[0])) for j in range(self.m)]


def G_values(w, tl, Rmax):
    """G(R) for R = 0..Rmax, doubled units, by a prefix DP over all subsets."""
    m, N, pc = w.m, w.N, w.pc
    lstar = {k: min(int(tl[S]) for S in range(N) if pc[S] == k) for k in range(m + 1)}
    out = []
    for R in range(Rmax + 1):
        h = [0] * N
        for A in range(N):
            k = pc[A]
            if 0 < k < m:
                h[A] = min(int(tl[S]) - lstar[k] for S in range(N)
                           if pc[S] == k and popcount(S & ~A) <= R)
        best = [None] * N
        best[0] = 0
        for A in sorted(range(1, N), key=lambda x: pc[x]):
            best[A] = max(h[A], min(best[A & ~(1 << j)] for j in range(m) if (A >> j) & 1))
        out.append(best[N - 1])
    return out, lstar


def score_frontier(w, F, tl, lstar):
    m, N, pc = w.m, w.N, w.pc
    sc = w.scores(F)
    rows = []
    for k in range(1, m):
        sums = {S: sum(sc[j] for j in range(m) if (S >> j) & 1) for S in range(N) if pc[S] == k}
        top = max(sums.values())
        for P in [S for S in sums if sums[S] == top]:
            Fk = [min(int(tl[S]) - lstar[k] for S in range(N) if pc[S] == k and popcount(S & ~P) <= R)
                  for R in range(min(k, m - k) + 1)]
            rows.append({"k": k, "prefix": [j for j in range(m) if (P >> j) & 1], "two_F_k": Fk})
    return rows


def margin(w, tl, O):
    """min over binding k of (second-best 2l among k-sets other than O_k) - 2l_{O_k}."""
    pc = w.pc
    best = None
    for k, Ok in O.items():
        others = min(int(tl[S]) for S in range(w.N) if pc[S] == k and S != Ok)
        v = others - int(tl[Ok])
        best = v if best is None else min(best, v)
    return best


def search(m, O, seed, steps, bound, w):
    rng = random.Random(seed)
    F = np.array([rng.randint(-bound, bound) for _ in range(w.N)], dtype=np.int64)
    tl = w.two_losses(F)
    cur = margin(w, tl, O)
    for t in range(steps):
        x = rng.randrange(w.N)
        old = F[x]
        F[x] = max(-bound, min(bound, old + rng.choice([-2, -1, 1, 2])))
        tl2 = w.two_losses(F)
        new = margin(w, tl2, O)
        if new >= cur:
            cur, tl = new, tl2
        else:
            F[x] = old
        if cur > 0 and t % 50 == 0:
            break
    return F, cur


def main():
    t0 = time.time()
    part_a = []
    for (m, R) in [(5, 1), (6, 1), (7, 1), (7, 2), (8, 2)]:
        res = bad_systems(m, R)
        print("A: m=%d R=%d binding k=%s systems=%d bad=%d (%.1fs)" % (
            m, R, res["binding_k"], res["systems"], res["bad"], time.time() - t0), flush=True)
        part_a.append(res)
    m = 7
    w = World(m)
    targets = [{int(k): sum(1 << j for j in v) for k, v in ex.items()} for ex in part_a[2]["examples"]]
    n_seeds = int(os.environ.get("P1_SEEDS", "20"))
    steps = int(os.environ.get("P1_STEPS", "4000"))
    bound = int(os.environ.get("P1_BOUND", "6"))
    found = []
    for ti, O in enumerate(targets):
        for seed in range(n_seeds):
            F, cur = search(m, O, 1000 * ti + seed, steps, bound, w)
            print("B: target %d seed %d margin %d (%.1fs)" % (ti, seed, cur, time.time() - t0), flush=True)
            if cur > 0:
                tl = w.two_losses(F)
                G, lstar = G_values(w, tl, 3)
                d = w.delta_box(F)
                rec = {"target": {str(k): [j for j in range(m) if (v >> j) & 1] for k, v in O.items()},
                       "seed": 1000 * ti + seed, "F": [int(v) for v in F], "delta_box": d,
                       "two_G": G, "G_over_delta": [g / (2 * d) if d else None for g in G],
                       "two_lstar": {str(k): v for k, v in lstar.items()},
                       "margin_two": cur, "scores": w.scores(F),
                       "score_frontier_two": score_frontier(w, F, tl, lstar)}
                ok = G[1] > 0 and G[0] >= G[1] >= G[2]
                rec["self_check_G1_positive_and_monotone"] = ok
                print("   FOUND: 2G(R)=%s delta=%d G/delta=%s check=%s" % (
                    G, d, ["%.3f" % v for v in rec["G_over_delta"]], ok), flush=True)
                found.append(rec)
                break
    producer = os.path.abspath(__file__)
    doc = {"artifact": "P1 exploratory search: price of nesting beyond one revision (D6 loss)",
           "evidence_class": "Part A EXACT finite enumeration; Part B EXPLORATORY hill-climb, "
                             "each hit re-evaluated exactly (integers)",
           "producer": os.path.relpath(producer, REPO), "producer_sha256": sha256_file(producer),
           "settings": {"m": m, "seeds_per_target": n_seeds, "steps": steps, "bound": bound},
           "model": __doc__, "part_A_combinatorics": part_a, "part_B_found": found}
    out_path = os.environ.get("P1_OUT", os.path.join(OUT_DIR, "d6_nesting_search.json"))
    if os.path.exists(out_path):
        print("REFUSE: %s exists; never overwrite" % out_path, flush=True)
        sys.exit(3)
    with open(out_path, "w") as fh:
        json.dump(doc, fh, indent=1)
    print("wrote %s; %d worlds with G(1) > 0 (%.1fs)" % (out_path, len(found), time.time() - t0), flush=True)


if __name__ == "__main__":
    main()
