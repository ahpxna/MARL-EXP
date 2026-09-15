#!/usr/bin/env python3
"""SUPPORT probe 3 -- structure of the law, and HONEST SCOPE BOUNDING.

Four jobs:

  E.  Repair + retest the general window-family law.  In SUPPORT_depth_probe.py
      the general law missed exactly the rows where some A_j is already empty
      (D=0 with no queries).  Corrected law:
          D = 0                                    if min_j |A_j| = 0
          D = min over compositions s = t_1+..+t_k of sum_i (g(t_i)+t_i)  else
      and retest, including compositions with parts >= 3 (s = 3,4), which the
      earlier run never exercised.

  F.  Exhaustive check of the REPAIRED interval lemma:
          H(s) := min |union of s cyclic length-L intervals, EACH of which
                       has a private point lying in no other interval|
          claim: H(s) = floor(s/2)*(L+1) + (s mod 2)*L, for m > s*L.
      The old s-1-private version is FALSE; a retained regression exhibits it.
      This checks a union lemma, not the final adaptive query-depth theorem.

  G.  Independent UPPER-BOUND certificate: simulate the explicit "grow a NO-run
      then pinch both ends" strategy against EVERY adversary answer sequence,
      and report its true worst-case depth.  This does not consult the minimax.

  H.  SCOPE BOUND / negative control: run the general law against RANDOM window
      hypergraphs that do not come from a cyclic kernel.  If it fails there,
      say so -- the law is then claimed only for the kernel family.

  B4'. Repaired geometry-sensitivity control (the old one was blind).

Run:  python3 scripts/SUPPORT_law_probe.py
"""
from itertools import combinations
import random, sys, time

sys.path.insert(0, "/Users/phanan/cig-amf-main/scripts")
from SUPPORT_depth_probe import (cyc, optimal_depth, law_product_parity, INF,
                                 g_threats, tent, windows, Game)
from fractions import Fraction as Fr


def ball_windows(m, r):
    A = []
    for j in range(m):
        mask = 0
        for w in range(m):
            if cyc(m, j, w) < r:
                mask |= 1 << w
        A.append(mask)
    return A


# ------------------------------------------------- E. corrected general law

def law_general_fixed(m, A, s):
    if any(a == 0 for a in A):
        return 0
    gs = {t: g_threats(m, A, t) for t in range(1, s + 1)}
    best = [INF] * (s + 1)
    best[0] = 0
    for k in range(1, s + 1):
        for t in range(1, k + 1):
            if gs[t] >= INF or best[k - t] >= INF:
                continue
            best[k] = min(best[k], best[k - t] + gs[t] + t)
    return best[s]


def part_E():
    print("\n" + "=" * 74)
    print("E. corrected general law, incl. s=3,4 (compositions with parts >= 3)")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'r':>2} {'D':>4} {'gen':>4} {'prod-parity':>12} {'ok':>4}")
    nok = nbad = 0
    for r in (1, 2, 3):
        L = 2 * r - 1
        for s in (1, 2, 3, 4):
            for m in (11, 12, 13):
                if s * L + 1 > m:
                    continue
                A = ball_windows(m, r)
                d, _ = optimal_depth(m, A, s)
                g = law_general_fixed(m, A, s)
                p = law_product_parity(s, r)
                ok = (d == g == p)
                nok += ok
                nbad += (not ok)
                print(f"   {m:>3} {s:>2} {r:>2} {d:>4} {g:>4} {p:>12} "
                      f"{'OK' if ok else 'MISS':>4}")
    print(f"   -> {nok} agree, {nbad} disagree")

    print("\n   heterogeneous rows that previously 'missed' (empty-window rows):")
    for m, rho, s in [(11, 2, 1), (11, 2, 2), (13, 3, 2)]:
        ker = tent(rho)
        h = [Fr(1) if w % 2 == 0 else Fr(1, 2) for w in range(m)]
        for k in range(0, 2 * (rho + 1) + 1):
            eps = Fr(k, 4)
            A = windows(m, ker, h, eps)
            if not any(a == 0 for a in A):
                continue
            d, _ = optimal_depth(m, A, s)
            g = law_general_fixed(m, A, s)
            print(f"      m={m} rho={rho} s={s} eps={eps}: D={d} gen_fixed={g} "
                  f"{'OK' if d == g else 'STILL MISSING'}")


# ------------------------------------------------------- F. interval lemma

def H_brute(m, L, s, *, require_all_private=True):
    """Minimum union size with a private point in EVERY interval.

    require_all_private=False reproduces the disproved legacy definition,
    solely for the negative control below.  The parity claim is only tested
    in the non-wrapping-capacity regime m > s*L.
    """
    if not (s >= 1 and 1 <= L < m and m > s * L):
        raise ValueError("interval check requires s >= 1, 1 <= L < m, m > s*L")
    ivs = []
    for x in range(m):
        mask = 0
        for t in range(L):
            mask |= 1 << ((x + t) % m)
        ivs.append(mask)
    best = INF
    # choose (with repetition allowed) s intervals; last one is the "final" one
    for combo in _tuples(range(m), s):
        masks = [ivs[x] for x in combo]
        union = 0
        for mk in masks:
            union |= mk
        if bin(union).count("1") >= best:
            continue
        # holes: a_i in I_i, in no other I_k
        ok = True
        holes = []
        for i in range(s if require_all_private else s - 1):
            priv = masks[i]
            for k in range(s):
                if k != i:
                    priv &= ~masks[k]
            if priv == 0:
                ok = False
                break
            holes.append(priv)
        if not ok:
            continue
        # Private sets are disjoint; retain the independent matching check.
        if not _sdr(holes, m):
            continue
        best = min(best, bin(union).count("1"))
    return best


def _tuples(rng, k):
    if k == 0:
        yield ()
        return
    for x in rng:
        for rest in _tuples(rng, k - 1):
            yield (x,) + rest


def _sdr(masks, m):
    """Hall's condition via simple matching (tiny sizes)."""
    n = len(masks)
    matchR = {}

    def try_k(i, seen):
        for p in range(m):
            if masks[i] >> p & 1 and p not in seen:
                seen.add(p)
                if p not in matchR or try_k(matchR[p], seen):
                    matchR[p] = i
                    return True
        return False

    for i in range(n):
        if not try_k(i, set()):
            return False
    return True


def part_F():
    print("\n" + "=" * 74)
    print("F. ALL-private interval lemma, m > s*L (not a query-depth proof)")
    intervals = [{0, 1, 2}, {2, 3, 4}, {1, 2, 3}]
    assert 0 not in intervals[1] | intervals[2]
    assert 4 not in intervals[0] | intervals[2]
    assert len(set.union(*intervals)) == 5
    assert not intervals[2] - (intervals[0] | intervals[1])
    legacy = H_brute(13, 3, 3, require_all_private=False)
    assert legacy <= 5 < 7, ("legacy negative control failed", legacy)
    print(f"   legacy s-1-private definition: H(3)={legacy} < claimed 7; RETRACTED")
    print("=" * 74)
    print(f"   {'m':>3} {'L':>2} {'s':>2} {'H(s)':>5} {'claim':>6} {'ok':>4}")
    nbad = 0
    for L in (1, 3, 5):
        for s in (1, 2, 3, 4):
            m = max(13, s * L + 2)
            if m > 16:
                print(f"   L={L} s={s}: SKIPPED (m={m} would need "
                      f"{m}^{s} placements) -- grid SHRUNK, stated not silent")
                continue
            h = H_brute(m, L, s)
            claim = (s // 2) * (L + 1) + (s % 2) * L
            ok = h == claim
            nbad += (not ok)
            print(f"   {m:>3} {L:>2} {s:>2} {h:>5} {claim:>6} "
                  f"{'OK' if ok else 'MISS':>4}")
    print(f"   -> repaired interval-grid mismatches: {nbad}")
    if nbad:
        raise AssertionError(f"repaired ALL-private interval lemma failed in {nbad} cells")


# ------------------------------------------- G. explicit strategy certificate

def simulate_pinch(m, r, s, verbose=False):
    """Worst-case depth of the explicit strategy:
       repeat: grow a run of NOs on fresh territory; when a NO would complete
       a window the adversary must answer YES; pinch the other end too; then
       move to fresh territory.  Implemented as an exhaustive game where the
       ALGORITHM is fixed (this strategy) and the ADVERSARY plays optimally."""
    L = 2 * r - 1
    A = ball_windows(m, r)

    def terminal(q0, q1):
        c1 = bin(q1).count("1")
        for j in range(m):
            a = A[j]
            if a & q1:
                continue
            if c1 == s or (a & ~q0) == 0:
                return True
        return False

    def consistent(q0, q1):
        c1 = bin(q1).count("1")
        if c1 > s:
            return False
        return (m - bin(q0 | q1).count("1")) >= s - c1

    def next_query(q0, q1):
        """The strategy's move. Pure function of the state."""
        asked = q0 | q1
        # 1. if a live run can be extended into a win, extend it
        # find the longest run of NOs whose extension is still useful
        best = None
        for start in range(m):
            # run [start, start+c-1] of NOs
            c = 0
            while c < m and (q0 >> ((start + c) % m)) & 1:
                c += 1
            if c == 0 or c >= L:
                continue
            left = (start - 1) % m
            right = (start + c) % m
            for end in (left, right):
                if asked >> end & 1:
                    continue
                key = (-c, end)
                if best is None or key < best[0]:
                    best = (key, end)
        if best is not None:
            return best[1]
        # 2. otherwise start a fresh run: an unasked point maximally far from
        #    every asked point
        bestp, bestd = None, -1
        for p in range(m):
            if asked >> p & 1:
                continue
            d = min([cyc(m, p, q) for q in range(m) if asked >> q & 1],
                    default=m)
            if d > bestd:
                bestd, bestp = d, p
        return bestp

    memo = {}

    def rec(q0, q1):
        if terminal(q0, q1):
            return 0
        k = (q0, q1)
        if k in memo:
            return memo[k]
        memo[k] = INF
        a = next_query(q0, q1)
        if a is None:
            memo[k] = INF
            return INF
        b = 1 << a
        vals = []
        if consistent(q0 | b, q1):
            vals.append(rec(q0 | b, q1))
        if bin(q1).count("1") + 1 <= s and consistent(q0, q1 | b):
            vals.append(rec(q0, q1 | b))
        v = INF if not vals else 1 + max(vals)
        memo[k] = v
        return v

    return rec(0, 0)


def part_G():
    print("\n" + "=" * 74)
    print("G. explicit strategy certificate (upper bound, minimax NOT consulted)")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'r':>2} {'strategy':>9} {'law':>4} {'minimax':>8} {'ok':>4}")
    nbad = 0
    for r in (1, 2, 3):
        L = 2 * r - 1
        for s in (1, 2, 3, 4):
            for m in (11, 12, 13):
                if s * L + 1 > m:
                    continue
                u = simulate_pinch(m, r, s)
                lw = law_product_parity(s, r)
                A = ball_windows(m, r)
                d, _ = optimal_depth(m, A, s)
                ok = (u == lw == d)
                nbad += (not ok)
                print(f"   {m:>3} {s:>2} {r:>2} {u:>9} {lw:>4} {d:>8} "
                      f"{'OK' if ok else 'MISS':>4}")
    print(f"   -> mismatches: {nbad}")


# --------------------------------------------------- H. scope bound (random)

def part_H(seed=20260912, trials=60):
    print("\n" + "=" * 74)
    print("H. SCOPE BOUND: general law on RANDOM window hypergraphs")
    print("=" * 74)
    print("   If the law only holds for the cyclic-kernel family, this must")
    print("   produce failures.  A law that never fails here would be suspect.")
    rng = random.Random(seed)
    agree = fail = skip = 0
    examples = []
    for t in range(trials):
        m = rng.choice([7, 8, 9])
        s = rng.choice([1, 2, 3])
        k = rng.choice([2, 3, 4])
        A = []
        for j in range(m):
            pts = rng.sample(range(m), k)
            mask = 0
            for p in pts:
                mask |= 1 << p
            A.append(mask)
        # feasibility: some j safe for every W of size s
        feas = True
        for W in combinations(range(m), s):
            wm = 0
            for w in W:
                wm |= 1 << w
            if not any((A[j] & wm) == 0 for j in range(m)):
                feas = False
                break
        if not feas:
            skip += 1
            continue
        d, _ = optimal_depth(m, A, s, use_sym=False)
        if d >= INF:
            skip += 1
            continue
        g = law_general_fixed(m, A, s)
        if d == g:
            agree += 1
        else:
            fail += 1
            if len(examples) < 5:
                examples.append((m, s, k, d, g, [bin(a) for a in A]))
    print(f"   feasible trials: {agree+fail}   law agrees: {agree}   "
          f"law FAILS: {fail}   skipped(infeasible): {skip}")
    for e in examples:
        print(f"      FAIL m={e[0]} s={e[1]} k={e[2]}: D={e[3]} law={e[4]}")
    if fail == 0:
        print("   WARNING: zero failures -- either the law is more general than")
        print("   claimed, or this control is not discriminating.  Treat as")
        print("   'not yet falsified', NOT as proof of generality.")


# ---------------------------------------- B4'. repaired sensitivity control

def part_B4():
    print("\n" + "=" * 74)
    print("B4'. repaired geometry-sensitivity control (graded mutilation)")
    print("=" * 74)
    m, r, s = 11, 2, 2
    A0 = ball_windows(m, r)
    base, _ = optimal_depth(m, A0, s, use_sym=False)
    print(f"   baseline m={m} r={r} s={s}: D={base}")
    changed = False
    for k in range(0, m + 1):
        A = list(A0)
        for j in range(k):
            A[j] = (1 << m) - 1       # window j destroyed
        d, _ = optimal_depth(m, A, s, use_sym=False)
        flag = "" if d == base else "  <-- CHANGED"
        print(f"   windows destroyed: {k:>2}  D={d if d < INF else 'INF'}{flag}")
        if d != base:
            changed = True
    print(f"   -> control is discriminating: {changed}")
    print("   (the earlier B4 destroyed ONE window out of 11 equivalent ones")
    print("    and could therefore never return False -- it was not a check.)")


def main():
    t0 = time.time()
    part_E()
    part_F()
    part_G()
    part_B4()
    part_H()
    print(f"\nelapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
