#!/usr/bin/env python3
"""P1, EXACT combinatorics of the nesting degree (independent of any loss).

For m items and a revision radius R, a SYSTEM is one k-set O_k per budget k.  A CHAIN is
C_1 < C_2 < ... < C_{m-1} with |C_k| = k (= the prefix sets of a ranking).  The system is
R-coverable if some chain has |C_k \\ O_k| <= R at every k.  If every system is R-coverable
then G(R) = 0 for every set loss (take O_k optimal; ties only help).

Budgets with min(k, m-k) <= R never bind (any chain works there).  Symmetry: one binding O_k is
fixed to {0, ..., k-1}; this loses no generality because the property is invariant under
relabelling the items.

Usage: nesting_degree_comb.py m R   -> nesting_degree_m{m}_R{R}.json (never overwritten)
"""
import hashlib
import itertools
import json
import os
import sys
import time

OUT_DIR = "/Users/phanan/cig-amf-main/research/marl_budget/P1_d6_frontier"


def popcount(x):
    return bin(x).count("1")


def main():
    m, R = int(sys.argv[1]), int(sys.argv[2])
    out = os.path.join(OUT_DIR, "nesting_degree_m%d_R%d.json" % (m, R))
    if os.path.exists(out):
        print("REFUSE: %s exists" % out, flush=True)
        sys.exit(3)
    t0 = time.time()
    ks = [k for k in range(1, m) if min(k, m - k) > R]
    bysize = {k: [x for x in range(1 << m) if popcount(x) == k] for k in range(m + 1)}
    # near[k][O] = k-sets C with |C \ O| <= R
    near = {k: {O: [C for C in bysize[k] if popcount(C & ~O) <= R] for O in bysize[k]} for k in ks}
    kfix = ks[len(ks) // 2]
    others = [k for k in ks if k != kfix]
    tot = bad = 0
    examples = []
    lo, hi = ks[0], ks[-1]

    def coverable(O):
        # binding levels are consecutive lo..hi; below lo and above hi everything is free
        reach = set(near[lo][O[lo]])
        for k in range(lo + 1, hi + 1):
            allowed = set(near[k][O[k]])
            reach = {B for B in allowed if any((B & ~(1 << j)) in reach for j in range(m) if (B >> j) & 1)}
            if not reach:
                return False
        return True

    for combo in itertools.product(*[bysize[k] for k in others]):
        O = dict(zip(others, combo))
        O[kfix] = (1 << kfix) - 1
        tot += 1
        if not coverable(O):
            bad += 1
            if len(examples) < 10:
                examples.append({str(k): [j for j in range(m) if (O[k] >> j) & 1] for k in sorted(O)})
        if tot % 100000 == 0:
            print("  %d systems, %d bad (%.0fs)" % (tot, bad, time.time() - t0), flush=True)
    doc = {"artifact": "nesting degree, exact enumeration", "m": m, "R": R, "binding_k": ks,
           "fixed_k": kfix, "systems": tot, "not_R_coverable": bad, "examples": examples,
           "all_R_coverable": bad == 0, "seconds": round(time.time() - t0, 1),
           "producer": "research/marl_budget/P1_d6_frontier/nesting_degree_comb.py",
           "producer_sha256": hashlib.sha256(open(os.path.abspath(__file__), "rb").read()).hexdigest(),
           "evidence_class": "EXACT finite enumeration (not a proof)", "model": __doc__}
    with open(out, "w") as fh:
        json.dump(doc, fh, indent=1)
    print("m=%d R=%d systems=%d not coverable=%d -> %s (%.0fs)" % (m, R, tot, bad, out, time.time() - t0),
          flush=True)


if __name__ == "__main__":
    main()
