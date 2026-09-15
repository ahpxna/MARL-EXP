#!/usr/bin/env python3
"""R3 (A): can a DESIGNED instance force large recourse at a FIXED eps > 0?

Random instances (scripts/R3_recourse_push.py) reach R_eps = 0 for every
eps >= 1/10 and only grow once eps <= 1/50.  This probe searches for adversarial
integer support matrices instead of sampling them.

Design principle the search exploits: the tolerance is eps * D with
D = sum of component spans, so an adversary wants D as SMALL as possible in
integer units.  Entries are therefore drawn from {0..C} with C in {1,2}: for a
0/1 matrix every non-constant row has span 1, D = #non-constant rows, and the
tolerance eps*D is only ~m/10 integer units at eps = 1/10.  That is the most
rigid regime available at a fixed tolerance.

Method: lexicographic hill-climbing on
    score(matrix) = (R_eps, R_{eps/5}, R_0)
with single-entry moves and random restarts.  Exact arithmetic throughout
(integer oscillations, Fraction tolerance); the DP re-verifies its own witness
and raises on mismatch.

Re-run:  python3 scripts/R3_recourse_adversarial.py
"""
import hashlib
import json
import random
import sys
import time
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from R3_recourse_core import instance_data, solve  # noqa: E402

OUT = Path("/Users/phanan/cig-amf-main/research/worker_distinct_completion_20260913"
           "/R3_recourse_adversarial.json")


def score(M, eps):
    try:
        data = instance_data(M)
    except ValueError:
        return None
    out = []
    for e in (eps, eps / 5 if eps else F(0), F(0)):
        out.append(solve(M, e, _data=data)[0])
    return tuple(out)


def climb(m, h, C, eps, rng, steps):
    M = [[rng.randint(0, C) for _ in range(h)] for _ in range(m)]
    for i in range(m):
        M[i][0] = 0
    s = score(M, eps)
    while s is None:
        M = [[0] + [rng.randint(0, C) for _ in range(h - 1)] for _ in range(m)]
        s = score(M, eps)
    for _ in range(steps):
        i, a = rng.randrange(m), rng.randrange(1, h)
        old = M[i][a]
        new = rng.randint(0, C)
        if new == old:
            continue
        M[i][a] = new
        t = score(M, eps)
        if t is None or t < s:
            M[i][a] = old
        else:
            s = t
    return s, M


def main():
    t0 = time.time()
    rng = random.Random(20260913)
    configs = []
    for eps in (F(1, 4), F(1, 10), F(1, 20)):
        for m in (8, 10, 12):
            for h in (4, 6):
                for C in (1, 2):
                    configs.append((eps, m, h, C))
    RESTARTS, STEPS = 12, 300
    rows = []
    best_overall = {}
    for eps, m, h, C in configs:
        best, bestM = (-1,), None
        for _ in range(RESTARTS):
            s, M = climb(m, h, C, eps, rng, STEPS)
            if s > best:
                best, bestM = s, [r[:] for r in M]
        # independent re-verification of the reported optimum
        assert solve(bestM, eps)[0] == best[0]
        rows.append({"epsilon": str(eps), "m": m, "h": h, "entry_max": C,
                     "best_R_eps": best[0], "R_eps_over_5": best[1],
                     "R_0": best[2], "witness_matrix": bestM})
        k = str(eps)
        if best[0] > best_overall.get(k, (-1,))[0]:
            best_overall[k] = (best[0], m, h, C)
        print(f"  eps={eps} m={m} h={h} C={C}: R_eps={best[0]} "
              f"(R_eps/5={best[1]}, R_0={best[2]})  [{time.time()-t0:.0f}s]", flush=True)

    print("\nbest R_eps found per epsilon (max over all searched configs):")
    for k, v in best_overall.items():
        print(f"  eps={k}: R_eps={v[0]} at m={v[1]} h={v[2]} C={v[3]}")

    OUT.write_text(json.dumps({
        "question": "(A) does a DESIGNED instance force large recourse at fixed eps?",
        "status": "NUMERICAL EVIDENCE (bounded search); absence of a witness is not a proof",
        "method": f"lexicographic hill-climbing, {RESTARTS} restarts x {STEPS} "
                  "single-entry moves per configuration",
        "searched_configs": len(configs),
        "search_space": "entries in {0..C}, first column pinned to 0 "
                        "(osc is translation invariant per row)",
        "skipped": "m > 12; h > 6; C > 2; no move set larger than one entry; "
                   "no exhaustive enumeration of any configuration",
        "core_sha256": hashlib.sha256(
            Path('/Users/phanan/cig-amf-main/scripts/R3_recourse_core.py').read_bytes()
        ).hexdigest(),
        "best_R_eps_per_epsilon": {k: {"R_eps": v[0], "m": v[1], "h": v[2],
                                       "entry_max": v[3]} for k, v in best_overall.items()},
        "results": rows,
    }, indent=2) + "\n")
    print(f"-> {OUT}")


if __name__ == "__main__":
    main()
