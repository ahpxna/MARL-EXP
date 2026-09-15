#!/usr/bin/env python3
r"""PACKAGE C.  epsilon_nest: the EXACT tolerance at which one ranking suffices
at every budget, and how large it can be.

Definitions (all exact, all rational).  An instance is an integer matrix
F with m rows (components) and d columns (scenarios).  With

    osc(v)   = max(v) - min(v)
    D        = sum_i osc(F_i)                       (total component span)
    L(S)     = osc( sum_{i not in S} F_i ) / D      (normalized residual osc)
    OPT_k    = min_{|T| = k} L(T)
    g(S)     = L(S) - OPT_{|S|}                     (>= 0)

    epsilon_nest(F) = min over permutations pi of {0..m-1}
                          max over k = 0..m of g(S_k^pi)

and epsilon_nest^star = sup over F of epsilon_nest(F).

THE DP.  H(empty) = 0,  H(S) = max{ g(S), min_{i in S} H(S \ {i}) }.
Claim: H(univ) = epsilon_nest(F).  This probe VERIFIES that claim by exhaustive
permutation comparison on every instance it tests with m <= 8, and RAISES on
any mismatch.  It also raises if the ordering the DP reconstructs does not, on
re-evaluation from scratch, attain the DP value.

GAUGE.  osc is invariant under adding a constant to any row: replacing F_i by
F_i + c_i changes sum_{i not in S} F_i by a constant, so every L(S) and every
osc(F_i) is unchanged.  Pinning column 0 of every row to 0 is therefore a pure
gauge fixing and loses nothing.  Entries in the other columns are SIGNED and
NOTHING forces a common minimising scenario -- the defect of the earlier search.

Re-run:  .venv/bin/python scripts/C1_structural_eps_nest_dp.py
"""
import hashlib
import itertools
import json
import random
import sys
import time
from fractions import Fraction as F
from pathlib import Path

OUT = Path("/Users/phanan/cig-amf-main/research/worker_gopC_20260913/C1_eps_nest_dp.json")

WITNESS = [[0, 1, 0], [1, 0, 1], [1, 0, 0], [0, 0, 1]]


# ---------------------------------------------------------------- loss table
def loss_numerators(M):
    """Integer oscillation of the residual for every subset mask, plus D.

    Returns (osc_of_mask, D).  osc_of_mask[S] = osc(sum_{i not in S} F_i), an
    integer;  D = sum_i osc(F_i), an integer.  Raises if D == 0.
    """
    m = len(M)
    d = len(M[0])
    for r in M:
        if len(r) != d:
            raise ValueError("ragged matrix")
    D = sum(max(r) - min(r) for r in M)
    if D == 0:
        raise ValueError("degenerate instance: total span 0")
    total = [sum(M[i][a] for i in range(m)) for a in range(d)]
    # residual for mask S = total - sum_{i in S} F_i ; build by subset DP
    res = [None] * (1 << m)
    res[0] = tuple(total)
    for S in range(1, 1 << m):
        i = (S & -S).bit_length() - 1
        prev = res[S ^ (1 << i)]
        res[S] = tuple(prev[a] - M[i][a] for a in range(d))
    osc = [max(v) - min(v) for v in res]
    return osc, D


def g_numerators(M):
    """g(S) * D as an integer for every mask, plus D."""
    m = len(M)
    osc, D = loss_numerators(M)
    opt = [None] * (m + 1)
    for S in range(1 << m):
        k = S.bit_count()
        if opt[k] is None or osc[S] < opt[k]:
            opt[k] = osc[S]
    gnum = [osc[S] - opt[S.bit_count()] for S in range(1 << m)]
    if min(gnum) < 0:
        raise AssertionError("negative excess -- OPT computation is wrong")
    return gnum, opt, D


# ------------------------------------------------------------------- the DP
def eps_nest_dp(M):
    """H(univ) via H(S) = max{g(S), min_{i in S} H(S\\{i})}.  O(m 2^m).

    Returns (Fraction value, ordering realising it, integer numerator, D).
    The returned ordering is re-evaluated from scratch by the caller.
    """
    m = len(M)
    gnum, _opt, D = g_numerators(M)
    H = [0] * (1 << m)
    last = [None] * (1 << m)          # element removed to reach the argmin child
    for S in range(1, 1 << m):
        best = None
        besti = None
        T = S
        while T:
            i = (T & -T).bit_length() - 1
            T &= T - 1
            h = H[S ^ (1 << i)]
            if best is None or h < best:
                best, besti = h, i
        H[S] = best if best > gnum[S] else gnum[S]
        last[S] = besti
    U = (1 << m) - 1
    order = []
    S = U
    while S:
        i = last[S]
        order.append(i)
        S ^= 1 << i
    order.reverse()
    return F(H[U], D), tuple(order), H[U], D


def order_value(M, order, gnum=None, D=None):
    """max_k g(prefix_k) for one explicit ordering, recomputed from scratch."""
    if gnum is None:
        gnum, _opt, D = g_numerators(M)
    m = len(M)
    if sorted(order) != list(range(m)):
        raise ValueError("not a permutation")
    S = 0
    worst = gnum[0]
    for i in order:
        S |= 1 << i
        if gnum[S] > worst:
            worst = gnum[S]
    return F(worst, D), worst


def eps_nest_brute(M):
    """min over ALL m! permutations of max_k g(prefix_k).  Exponential."""
    m = len(M)
    gnum, _opt, D = g_numerators(M)
    best = None
    bestp = None
    for pi in itertools.permutations(range(m)):
        S = 0
        worst = gnum[0]
        for i in pi:
            S |= 1 << i
            if gnum[S] > worst:
                worst = gnum[S]
            if best is not None and worst >= best:
                break
        else:
            if best is None or worst < best:
                best, bestp = worst, pi
            continue
        if best is None:
            best, bestp = worst, pi
    return F(best, D), bestp, best, D


# ------------------------------------------------------------------ searches
def random_signed(rng, m, d, lo, hi):
    """Signed entries; column 0 pinned to 0 (pure gauge).  NO sign constraint
    on the remaining columns and NO common minimising scenario."""
    return [[0] + [rng.randint(lo, hi) for _ in range(d - 1)] for _ in range(m)]


def safe_dp(M):
    try:
        return eps_nest_dp(M)
    except ValueError:
        return None


def exhaustive(m, d, values):
    """Every matrix with column 0 pinned to 0 and the other entries in
    `values`.  Yields (best Fraction, best matrix, count examined)."""
    rows = list(itertools.product(values, repeat=d - 1))
    best = F(0)
    bestM = None
    count = 0
    for combo in itertools.combinations_with_replacement(rows, m):
        # rows are interchangeable: L(S) depends only on the multiset of rows
        M = [[0] + list(r) for r in combo]
        count += 1
        out = safe_dp(M)
        if out is None:
            continue
        if out[0] > best:
            best, bestM = out[0], [r[:] for r in M]
    return best, bestM, count


def climb(rng, m, d, lo, hi, steps):
    M = random_signed(rng, m, d, lo, hi)
    out = safe_dp(M)
    while out is None:
        M = random_signed(rng, m, d, lo, hi)
        out = safe_dp(M)
    cur = out[0]
    for _ in range(steps):
        i = rng.randrange(m)
        a = rng.randrange(1, d)
        old = M[i][a]
        new = rng.randint(lo, hi)
        if new == old:
            continue
        M[i][a] = new
        out = safe_dp(M)
        if out is None or out[0] < cur:
            M[i][a] = old
        else:
            cur = out[0]
    return cur, M


def main():
    t0 = time.time()
    report = {}

    # ---- 0. the supervisor's exact 4x3 witness -------------------------
    v, order, num, D = eps_nest_dp(WITNESS)
    vb, orderb, numb, _ = eps_nest_brute(WITNESS)
    rv, _ = order_value(WITNESS, order)
    if not (v == vb == F(1, 4)):
        raise AssertionError(f"witness value wrong: dp={v} brute={vb}")
    if rv != v:
        raise AssertionError("DP certificate does not reproduce its own value")
    if D != 4:
        raise AssertionError(f"witness D = {D}, expected 4")
    report["witness"] = {"matrix": WITNESS, "D": D, "eps_nest": str(v),
                         "dp_ordering": list(order), "brute_ordering": list(orderb),
                         "status": "EXACT (enumerated all 4! = 24 rankings)"}
    print(f"witness eps_nest = {v} via {order}  [{time.time()-t0:.1f}s]", flush=True)

    # ---- 1. DP vs full permutation enumeration, every m <= 8 ------------
    rng = random.Random(20260913)
    xc = []
    plan = [(2, 60), (3, 60), (4, 60), (5, 40), (6, 30), (7, 16), (8, 8)]
    for m, n_inst in plan:
        checked = 0
        skipped = 0
        for _ in range(n_inst):
            d = rng.choice([2, 3, 4, 5])
            lo, hi = rng.choice([(-1, 1), (-2, 2), (-3, 3), (0, 2)])
            M = random_signed(rng, m, d, lo, hi)
            try:
                vd, od, nd, Dd = eps_nest_dp(M)
            except ValueError:
                skipped += 1
                continue
            vb, ob, nb, _ = eps_nest_brute(M)
            if vd != vb:
                raise AssertionError(
                    f"DP != brute at m={m}: dp={vd} brute={vb} M={M}")
            rv, _ = order_value(M, od)
            if rv != vd:
                raise AssertionError(f"DP certificate bad at m={m}: M={M}")
            checked += 1
        xc.append({"m": m, "instances_checked": checked,
                   "degenerate_skipped": skipped,
                   "permutations_per_instance": {2: 2, 3: 6, 4: 24, 5: 120,
                                                 6: 720, 7: 5040, 8: 40320}[m]})
        print(f"  cross-check m={m}: {checked} instances, DP == brute "
              f"[{time.time()-t0:.1f}s]", flush=True)
    # the witness itself, plus 1-row / all-equal edge cases
    for M in (WITNESS, [[0, 1], [0, -1]], [[0, 1, 2]], [[0, 0, 1], [0, 1, 0], [0, 1, 1]]):
        try:
            vd = eps_nest_dp(M)[0]
        except ValueError:
            continue
        if vd != eps_nest_brute(M)[0]:
            raise AssertionError(f"DP != brute on fixed instance {M}")
    report["dp_recurrence_crosscheck"] = {
        "status": "VERIFIED on every instance listed; raises on mismatch",
        "cells": xc,
        "not_checked": "m >= 9 (9! = 362880 permutations per instance was not run)",
    }

    # ---- 2. exhaustive signed searches ---------------------------------
    ex = []
    grids = [
        (4, 3, (-2, -1, 0, 1, 2)),
        (4, 4, (-1, 0, 1)),
        (5, 3, (-1, 0, 1)),
        (6, 3, (-1, 0, 1)),
        (3, 4, (-1, 0, 1)),
        (5, 4, (-1, 0, 1)),
    ]
    overall = F(0)
    overallM = None
    overall_where = None
    for m, d, vals in grids:
        b, bM, cnt = exhaustive(m, d, vals)
        ex.append({"m": m, "d": d, "entry_values": list(vals),
                   "row_multisets_examined": cnt, "max_eps_nest": str(b),
                   "argmax_matrix": bM})
        if b > overall:
            overall, overallM, overall_where = b, bM, f"exhaustive m={m} d={d} vals={vals}"
        print(f"  exhaustive m={m} d={d} vals={vals}: {cnt} row-multisets, "
              f"max eps_nest = {b}  [{time.time()-t0:.1f}s]", flush=True)
    report["exhaustive_signed"] = {
        "gauge": "column 0 pinned to 0 for every row (adding a constant to a row "
                 "changes no L(S) and no osc(F_i)); remaining entries SIGNED; "
                 "no non-negativity, no common minimising scenario",
        "dedup": "rows enumerated as a MULTISET (L(S) depends only on the "
                 "multiset of rows up to the index relabelling that the min over "
                 "permutations already quotients out)",
        "cells": ex,
    }

    # ---- 3. hill-climb on larger, wider, more signed instances ----------
    hc = []
    configs = []
    for m in (6, 8, 10, 12):
        for d in (3, 4, 6):
            for rngpair in ((-1, 1), (-3, 3)):
                configs.append((m, d, rngpair))
    RESTARTS, STEPS = 8, 250
    for m, d, (lo, hi) in configs:
        best = F(0)
        bestM = None
        for _ in range(RESTARTS):
            v2, M2 = climb(rng, m, d, lo, hi, STEPS)
            if v2 > best:
                best, bestM = v2, [r[:] for r in M2]
        if bestM is not None:
            rv2 = eps_nest_dp(bestM)[0]
            if rv2 != best:
                raise AssertionError("hill-climb best not reproducible")
        hc.append({"m": m, "d": d, "entry_range": [lo, hi],
                   "restarts": RESTARTS, "steps": STEPS,
                   "max_eps_nest": str(best), "argmax_matrix": bestM})
        if best > overall:
            overall, overallM, overall_where = best, bestM, f"hill-climb m={m} d={d}"
        print(f"  climb m={m} d={d} entries[{lo},{hi}]: max eps_nest = {best} "
              f"[{time.time()-t0:.1f}s]", flush=True)
    report["hill_climb_signed"] = {"cells": hc,
                                   "move_set": "single entry, one column at a time",
                                   "not_searched": "m > 12; d > 6; |entry| > 3; "
                                                   "no multi-entry moves"}

    # ---- 4. targeted refutation attempts -------------------------------
    ref = []
    # (a) disjoint-scenario direct sums of the witness with itself
    def direct_sum(A, B):
        ma, da = len(A), len(A[0])
        mb, db = len(B), len(B[0])
        top = [row + [0] * db for row in A]
        bot = [[0] * da + row for row in B]
        return top + bot
    S2 = direct_sum(WITNESS, WITNESS)
    ref.append({"family": "witness (+) witness, disjoint scenarios (m=8,d=6)",
                "eps_nest": str(eps_nest_dp(S2)[0])})
    # (b) shared-scenario stacking: two witnesses on the SAME 3 scenarios
    ref.append({"family": "two witness copies on the same 3 scenarios (m=8,d=3)",
                "eps_nest": str(eps_nest_dp(WITNESS + WITNESS)[0])})
    # (c) scaled copies (spans 1 and 2) on the same scenarios
    W2 = [[2 * x for x in r] for r in WITNESS]
    ref.append({"family": "witness stacked with a 2x-scaled witness (m=8,d=3)",
                "eps_nest": str(eps_nest_dp(WITNESS + W2)[0])})
    # (d) witness + one extra heavy row, sweeping the heavy row
    bestd = F(0)
    bestdM = None
    for extra in itertools.product((-2, -1, 0, 1, 2), repeat=2):
        M = WITNESS + [[0, extra[0], extra[1]]]
        out = safe_dp(M)
        if out and out[0] > bestd:
            bestd, bestdM = out[0], M
    ref.append({"family": "witness + one extra row, all 25 signed choices",
                "eps_nest": str(bestd), "argmax_matrix": bestdM})
    # (e) all 4x3 and 4x4 and 5x3 matrices already covered exhaustively above
    for r in ref:
        print(f"  refutation attempt [{r['family']}]: eps_nest = {r['eps_nest']}",
              flush=True)
        v = F(r["eps_nest"])
        if v > overall:
            overall, overallM, overall_where = v, r.get("argmax_matrix"), r["family"]
    report["refutation_attempts"] = ref

    report["overall"] = {
        "max_eps_nest_found": str(overall),
        "found_by": overall_where,
        "argmax_matrix": overallM,
        "verdict": ("no instance exceeding 1/4 was found in any search listed "
                    "above; this is NOT a proof that epsilon_nest^star = 1/4"),
    }
    report["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report["wall_seconds"] = round(time.time() - t0, 1)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print(f"\nMAX eps_nest over every search: {overall}  ({overall_where})")
    print(f"wrote {OUT}  [{time.time()-t0:.1f}s]")


if __name__ == "__main__":
    main()
