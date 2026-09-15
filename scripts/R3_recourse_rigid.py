#!/usr/bin/env python3
"""R3 (A), rigid regime: an EXACT witness that a fixed eps > 0 does not force
R_eps = 0.

Observation (exact, not heuristic).  For an integer support matrix every
oscillation val(S) is an integer, and the eps-good test at budget k is
    val(S) <= opt_k + eps * D,   D = sum of component spans.
If eps * D < 1 then `val(S) <= opt_k + eps*D` forces `val(S) <= opt_k`:
eps-good collapses to EXACTLY optimal, hence R_eps = R_0 for that instance.
So for any fixed eps > 0, instances with D < 1/eps are as rigid as eps = 0.

With D < 1/eps and integer spans, at most floor(1/eps)-1 components can have
span >= 1; a span-0 component is constant, contributes nothing to any
oscillation, and only gives a chain extra slack.  The extremal instances are
therefore 0/1 matrices with m <= floor(1/eps)-1 non-constant rows (a row of
span 1 is {0,1} after translation, and osc is translation invariant per row).

This probe searches that family directly: an instance is a set of h columns in
{0,1}^m, val(S) = range over columns c of |c restricted to the complement of S|.
It reports, per (m,h), the largest R_0 found, and re-verifies each witness with
the independent DP at the corresponding eps = 1/(m+1) (so eps*D = m/(m+1) < 1).

Re-run:  python3 scripts/R3_recourse_rigid.py
"""
import hashlib
import itertools
import json
import random
import sys
import time
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from R3_recourse_core import solve  # noqa: E402

OUT = Path("/Users/phanan/cig-amf-main/research/worker_distinct_completion_20260913"
           "/R3_recourse_rigid.json")


def matrix_of(cols, m):
    """cols: list of ints (bitmask over the m rows) -> m x h 0/1 matrix."""
    return [[(c >> i) & 1 for c in cols] for i in range(m)]


def nonconstant(M):
    return all(max(r) - min(r) == 1 for r in M)


def search(m, h, trials, rng):
    """Random restarts + hill-climbing on the column set, maximizing R_0."""
    best, bestM = 0, None
    universe = list(range(1 << m))
    for _ in range(trials):
        cols = [rng.choice(universe) for _ in range(h)]
        M = matrix_of(cols, m)
        if not nonconstant(M):
            continue
        cur = solve(M, F(0))[0]
        improved = True
        while improved:
            improved = False
            for pos in range(h):
                for c in universe:
                    if c == cols[pos]:
                        continue
                    old = cols[pos]
                    cols[pos] = c
                    M2 = matrix_of(cols, m)
                    if nonconstant(M2):
                        v = solve(M2, F(0))[0]
                        if v > cur:
                            cur, improved = v, True
                            continue
                    cols[pos] = old
            if improved:
                continue
        M = matrix_of(cols, m)
        if cur > best and nonconstant(M):
            best, bestM = cur, M
    return best, bestM


def main():
    t0 = time.time()
    rng = random.Random(20260913)
    rows = []
    for m in range(4, 10):
        for h in (3, 4, 5, 6):
            trials = 40 if m <= 7 else 12
            best, M = search(m, h, trials, rng)
            rec = {"m": m, "h": h, "trials": trials, "max_R_0_found": best}
            if M is not None and best > 0:
                D = sum(max(r) - min(r) for r in M)
                assert D == m, (D, m)
                eps = F(1, m + 1)          # eps*D = m/(m+1) < 1
                v = solve(M, eps)[0]
                assert v == best, ("rigidity collapse failed", v, best)
                # and the strongest fixed tolerance that is still rigid here
                rec.update({"witness_matrix": M, "D": D,
                            "eps_certified": str(eps),
                            "R_eps_at_eps_certified": v})
            rows.append(rec)
            print(f"  m={m} h={h}: max R_0 = {best}  [{time.time()-t0:.0f}s]", flush=True)

    # strongest certified statement: largest eps with a witness
    best_eps, best_rec = None, None
    for r in rows:
        if r.get("R_eps_at_eps_certified", 0) > 0:
            e = F(r["eps_certified"])
            if best_eps is None or e > best_eps or (e == best_eps and
                    r["R_eps_at_eps_certified"] > best_rec["R_eps_at_eps_certified"]):
                best_eps, best_rec = e, r
    print("\nstrongest certified fixed tolerance with R_eps > 0:")
    print(f"  eps = {best_eps}, R_eps = {best_rec['R_eps_at_eps_certified']}, "
          f"m = {best_rec['m']}, h = {best_rec['h']}" if best_rec else "  none found")

    OUT.write_text(json.dumps({
        "question": "(A) is there an instance with R_eps > 0 at a FIXED eps > 0?",
        "status": "EXACT finite witnesses (integer DP); the search for the LARGEST "
                  "such eps is heuristic, the witnesses themselves are exact",
        "rigidity_collapse": "eps*D < 1 and integer oscillations => eps-good = exactly "
                             "optimal => R_eps = R_0",
        "searched": "0/1 column sets, m in 4..9, h in 3..6, random restarts + "
                    "single-column hill climbing on R_0",
        "skipped": "m >= 10 (there eps=1/(m+1) <= 1/11 only); h >= 7; no exhaustive "
                   "enumeration of any (m,h); spans > 1 not searched",
        "core_sha256": hashlib.sha256(
            Path('/Users/phanan/cig-amf-main/scripts/R3_recourse_core.py').read_bytes()
        ).hexdigest(),
        "strongest_certified": {"epsilon": str(best_eps), "record": best_rec}
                               if best_rec else None,
        "results": rows,
    }, indent=2) + "\n")
    print(f"-> {OUT}")


if __name__ == "__main__":
    main()
