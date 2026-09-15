#!/usr/bin/env python3
"""N3 -- how much of the Support speedup is ADAPTIVITY?  Pin the NONADAPTIVE depth.

PRIMITIVE (unchanged, copied from scripts/SUPPORT_depth_probe.py semantics):
  * m points on a cycle Z_m; hidden world W subset Z_m with |W| = s; m > s*L.
  * window A_j = {j, j+1, ..., j+L-1} mod m   (L >= 1).
  * query = point membership, one bit: oracle(a) = (a in W).
  * decision j is SAFE iff A_j cap W = empty.
  * a state is TERMINAL iff some j has A_j cap q1 = empty AND
      (A_j subset q0  OR  |q1| = s).
    This is verbatim the `terminal` predicate of SUPPORT_depth_probe.Game --
    "j is safe in EVERY world consistent with the transcript".

WHAT IS COMPUTED (each part raises AssertionError on mismatch; nothing is
printed-and-ignored):

  A.  Explicit NONADAPTIVE UPPER bound s*L: run the "s disjoint blocks of
      length L" one-shot protocol against EVERY world of size s and check the
      output is genuinely safe.  This exercises the disputed step
      "you have observed s holes" operationally.

  B.  EXACT nonadaptive minimax D_1(m,s,L) = min |Q| over ALL Q subset Z_m
      such that every consistent answer pattern leaves a state that is
      terminal.  Claim: D_1 = s*L.

  C.  The LOWER-bound CERTIFICATE, run as a machine-checked construction, for
      EVERY Q with |Q| <= s*L - 1 (not just |Q| = sL-1):
        c1. p not in Q exists; cut there; windows inside Q are line intervals.
        c2. greedy-by-right-endpoint hitting set Y; assert Y hits every window
            inside Q; assert the greedy witnesses are PAIRWISE DISJOINT;
            assert |Y| <= s-1 (via k*L <= |Q| < s*L).
        c3. assert |Y| + |complement Q| >= ceil(m/L) >= s+1  (the mandatory
            consistency count), and assert Y u complement(Q) really does hit
            every one of the m cyclic windows.
        c4. assert the transcript (YES on Y, NO on Q\\Y) has >= 1 consistent
            world, i.e. it is not an impossible transcript.
        c5. assert NO decision j is safe in every consistent world: build the
            explicit killing world for each j.

  D.  NEGATIVE CONTROL for C.  Re-run the identical certificate at |Q| = s*L
      (Q = the s disjoint blocks).  It MUST break.  A certificate that also
      "succeeds" at sL would not be a check at all.

  E.  Exact b-BATCH DP for b = 1, 2, 3 (batch fixed BEFORE its replies):
        D_b(state) = min_Q { |Q| + max_{y : child nonempty} D_{b-1}(child) }
        D_0(state) = 0 if terminal else INF
      plus the fully adaptive minimax H (SUPPORT_depth_probe.optimal_depth,
      re-derived here for general L, cross-checked against the repo routine on
      odd L).  Reports the measured adaptivity ratio s*L / H.

  F.  Feasibility boundary: at m = s*L the game is INFEASIBLE (H = INF), so
      the hypothesis m > s*L is load bearing and not decorative.

SKIPPED CONFIGURATIONS (stated, never silent):
  * Parts B/C are capped at m <= 12 and s*L <= 10: part B enumerates 3^m
    (Q, answer) pairs and part C enumerates EVERY Q of size <= sL-1, so larger
    m leaves the time budget.
  * Part E (b-batch DP) is capped at m <= 15 and b <= 4.  b >= 5 is NOT
    computed anywhere, so no cell is certified to have reached the b -> infinity
    value except where D_b already equals the separately computed minimax H.
  * m = 16 (s=3,L=5) and m = 17 (s=2,L=8) are run only under --long (15.6 s and
    22.6 s respectively); their values are printed as previously-measured text
    in the default run and are NOT re-verified there.
  * Only L in {1,...,8} and s in {1,...,6} appear anywhere.  Nothing outside a
    printed row is claimed.
  * Part E2's cross-check against the repo routine SUPPORT_depth_probe
    .optimal_depth is possible only for ODD L (the repo helper builds balls of
    radius r, i.e. L = 2r-1); even-L rows print '-' there.

Run:  python3 scripts/N3_nonadaptive_depth_probe.py
"""
import sys, time
from itertools import combinations
from math import ceil

sys.path.insert(0, "/Users/phanan/cig-amf-main/scripts")

INF = 10 ** 6


# ------------------------------------------------------------- primitives

def windows_cyclic(m, L):
    """A_j = {j, j+1, ..., j+L-1} mod m, as bitmasks."""
    assert 1 <= L <= m
    A = []
    for j in range(m):
        mask = 0
        for t in range(L):
            mask |= 1 << ((j + t) % m)
        A.append(mask)
    return A


def popcount(x):
    return bin(x).count("1")


def terminal(m, A, s, q0, q1):
    """Some j is safe in EVERY world consistent with (q0 = NO set, q1 = YES set).
    Verbatim semantics of SUPPORT_depth_probe.Game.terminal."""
    c1 = popcount(q1)
    for j in range(m):
        a = A[j]
        if a & q1:
            continue
        if c1 == s or (a & ~q0) == 0:
            return True
    return False


def consistent(m, s, q0, q1):
    """At least one world W with |W| = s, q1 subset W, W cap q0 = empty."""
    c1 = popcount(q1)
    if c1 > s:
        return False
    free = m - popcount(q0 | q1)
    return free >= s - c1


def consistent_worlds(m, s, q0, q1):
    """Explicit list of consistent worlds (bitmasks).  Small m only."""
    c1 = popcount(q1)
    if c1 > s:
        return []
    freepts = [p for p in range(m) if not ((q0 | q1) >> p & 1)]
    if len(freepts) < s - c1:
        return []
    out = []
    for extra in combinations(freepts, s - c1):
        w = q1
        for p in extra:
            w |= 1 << p
        out.append(w)
    return out


# ---------- 0. the consistency FILTER itself is checked, not trusted

def part_0(cases):
    """Every later part prunes answer patterns with `consistent(...)`.  A wrong
    filter here could silently delete the adversary's true winning transcript,
    which would make every downstream lower bound vacuous.  So compare the
    closed-form filter against brute-force enumeration of worlds, on EVERY
    (q0,q1) pair, for small m."""
    print("=" * 74)
    print("0. the `consistent` filter vs brute-force world enumeration")
    print("=" * 74)
    tot = 0
    for (m, s) in cases:
        for q0 in range(1 << m):
            for q1 in range(1 << m):
                if q0 & q1:
                    continue
                a = consistent(m, s, q0, q1)
                b = len(consistent_worlds(m, s, q0, q1)) > 0
                assert a == b, ("consistency filter is WRONG", m, s, q0, q1, a, b)
                tot += 1
    print(f"   {tot} (q0,q1) states checked over {cases}: filter is exact")


# ------------------------------------------- A. explicit nonadaptive protocol

def part_A(grid):
    print("\n" + "=" * 74)
    print("A. explicit s-disjoint-blocks protocol, checked against EVERY world")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'L':>2} {'|Q|':>4} {'worlds':>7} "
          f"{'all-NO used':>12} {'holes used':>11}")
    for (m, s, L) in grid:
        A = windows_cyclic(m, L)
        assert m > s * L, (m, s, L)
        blocks = [tuple((i * L + t) % m for t in range(L)) for i in range(s)]
        seen = set()
        for b in blocks:
            for p in b:
                assert p not in seen, ("blocks are NOT disjoint", m, s, L)
                seen.add(p)
        Q = sorted(seen)
        assert len(Q) == s * L
        n_allno = n_holes = 0
        for Wt in combinations(range(m), s):
            wm = 0
            for w in Wt:
                wm |= 1 << w
            # one-shot: all sL answers arrive together
            allno = None
            for i, b in enumerate(blocks):
                if all(not (wm >> p & 1) for p in b):
                    allno = i
                    break
            if allno is not None:
                j = (allno * L) % m
                assert A[j] & wm == 0, ("all-NO block not safe", m, s, L, Wt)
                n_allno += 1
                continue
            # every block has a YES -> the observed YES set must BE W
            yes = [p for p in Q if wm >> p & 1]
            assert len(yes) >= s, ("fewer than s holes observed", m, s, L, Wt)
            assert len(yes) == s, ("more than s holes observed", m, s, L, Wt)
            ym = 0
            for p in yes:
                ym |= 1 << p
            assert ym == wm, ("observed holes != W", m, s, L, Wt)
            # m > sL guarantees a surviving window
            safe = [j for j in range(m) if A[j] & wm == 0]
            assert safe, ("no safe window although m > sL", m, s, L, Wt)
            n_holes += 1
        print(f"   {m:>3} {s:>2} {L:>2} {len(Q):>4} "
              f"{n_allno + n_holes:>7} {n_allno:>12} {n_holes:>11}")
    print("   -> upper bound D_nonadaptive <= s*L verified constructively on this grid")


# ---------------------------------- B. exact nonadaptive minimax (= D_1)

def nonadaptive_min(m, L, s, cap=None):
    """min |Q| such that EVERY consistent answer pattern on Q is terminal.
    Exhaustive over subsets in increasing size.  Returns INF if none <= cap."""
    A = windows_cyclic(m, L)
    if terminal(m, A, s, 0, 0):
        return 0
    hi = m if cap is None else min(m, cap)
    for k in range(1, hi + 1):
        for Qt in combinations(range(m), k):
            ok = True
            for r in range(0, min(s, k) + 1):
                if not ok:
                    break
                for yes in combinations(Qt, r):
                    q1 = 0
                    for p in yes:
                        q1 |= 1 << p
                    q0 = 0
                    for p in Qt:
                        if not (q1 >> p & 1):
                            q0 |= 1 << p
                    if not consistent(m, s, q0, q1):
                        continue
                    if not terminal(m, A, s, q0, q1):
                        ok = False
                        break
            if ok:
                return k
    return INF


def part_B(grid):
    print("\n" + "=" * 74)
    print("B. EXACT nonadaptive minimax D_1 over ALL query sets Q")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'L':>2} {'D_1':>4} {'s*L':>4} {'ok':>4}")
    bad = 0
    for (m, s, L) in grid:
        d1 = nonadaptive_min(m, L, s)
        ok = (d1 == s * L)
        bad += (not ok)
        print(f"   {m:>3} {s:>2} {L:>2} {d1:>4} {s*L:>4} {'OK' if ok else 'MISS':>4}")
    print(f"   -> mismatches: {bad}")
    if bad:
        raise AssertionError(f"D_1 != s*L in {bad} cells of the part-B grid")


# ------------------------------------- C. lower-bound certificate machinery

def cut_and_linearise(m, Q_mask):
    """Return p not in Q and the linear order starting at p+1 (p excluded)."""
    p = None
    for x in range(m):
        if not (Q_mask >> x & 1):
            p = x
            break
    assert p is not None, "Q = Z_m; the cut step needs |Q| < m"
    order = [(p + 1 + t) % m for t in range(m - 1)]
    return p, order


def greedy_hitting_set(m, L, Q_mask, A):
    """Windows entirely inside Q become line intervals after cutting at some
    p not in Q.  Greedy by smallest right endpoint.  Returns (Y_mask, witnesses)
    where witnesses are the intervals picked (pairwise disjoint by construction,
    verified by the caller)."""
    p, order = cut_and_linearise(m, Q_mask)
    pos = {v: i for i, v in enumerate(order)}
    ivs = []
    for j in range(m):
        if A[j] & ~Q_mask:
            continue                      # not contained in Q
        pts = [(j + t) % m for t in range(L)]
        assert p not in pts, "a window inside Q cannot contain the cut point"
        idx = [pos[v] for v in pts]
        assert max(idx) - min(idx) == L - 1, (
            "window inside Q is not contiguous in the cut order", j)
        ivs.append((max(idx), min(idx), j, A[j]))
    ivs.sort()
    Y = 0
    witnesses = []
    live = list(ivs)
    while live:
        right, left, j, mask = live[0]
        hitpoint = order[right]
        Y |= 1 << hitpoint
        witnesses.append(mask)
        live = [iv for iv in live if not (iv[3] >> hitpoint & 1)]
    return Y, witnesses, ivs


def hits_all_cyclic_windows(m, A, H_mask):
    return all(A[j] & H_mask for j in range(m))


def certificate(m, s, L, Q_mask, strict=True):
    """Run the full lower-bound construction on this Q.  Returns a dict of
    verdicts.  strict=True asserts each step (used for |Q| < sL); strict=False
    only reports (used for the negative control at |Q| = sL)."""
    A = windows_cyclic(m, L)
    q = popcount(Q_mask)
    out = {"|Q|": q}

    Y, witnesses, ivs = greedy_hitting_set(m, L, Q_mask, A)
    k = popcount(Y)
    out["|Y|"] = k

    # c2a: Y hits every window inside Q
    hits_inside = all((mask & Y) for (_, _, _, mask) in ivs)
    out["Y_hits_inside"] = hits_inside
    # c2b: witnesses pairwise disjoint
    disj = True
    for i in range(len(witnesses)):
        for j2 in range(i + 1, len(witnesses)):
            if witnesses[i] & witnesses[j2]:
                disj = False
    out["witnesses_disjoint"] = disj
    out["n_witnesses"] = len(witnesses)
    # c2c: |Y| <= s-1
    out["Y_small"] = (k <= s - 1)

    # c3: counting bound
    Qc = ((1 << m) - 1) & ~Q_mask
    out["cover_count_ok"] = (k + popcount(Qc) >= ceil(m / L))
    out["ceil_ge_s1"] = (ceil(m / L) >= s + 1)
    out["Y_u_Qc_hits_all"] = hits_all_cyclic_windows(m, A, Y | Qc)

    # c4: transcript consistency
    q0 = Q_mask & ~Y
    q1 = Y
    worlds = consistent_worlds(m, s, q0, q1)
    out["n_consistent_worlds"] = len(worlds)
    out["transcript_consistent"] = (len(worlds) > 0)

    # c5: no decision safe in every consistent world
    unsafe_all = True
    killer = {}
    for j in range(m):
        if A[j] & Y:
            killer[j] = ("meets Y", None)
            continue
        # must contain an unknown point
        unknown = A[j] & Qc
        if unknown == 0:
            unsafe_all = False
            killer[j] = ("SAFE: inside Q and misses Y", None)
            continue
        x = (unknown & -unknown).bit_length() - 1
        # complete W to contain Y u {x}.  Needs |Y| <= s-1 AND enough free
        # points; BOTH can fail, and at |Q| = sL the first one does.
        need = s - k - 1
        if need < 0:
            unsafe_all = False
            killer[j] = ("|Y| = s already: Y u {x} exceeds the budget", x)
            continue
        pool = [p for p in range(m) if (Qc >> p & 1) and p != x]
        if need > len(pool):
            unsafe_all = False
            killer[j] = ("cannot complete world: too few free points", x)
            continue
        w = Y | (1 << x)
        for p in pool[:need]:
            w |= 1 << p
        assert popcount(w) == s, ("killer world has wrong size", m, s, L, j)
        assert w & q0 == 0, ("killer world contradicts a NO answer", m, s, L, j)
        assert A[j] & w, ("constructed killer world does not kill j", m, s, L, j)
        killer[j] = ("killed by unknown", x)
    out["no_safe_output"] = unsafe_all
    out["not_terminal"] = not terminal(m, A, s, q0, q1)

    if strict:
        assert hits_inside, ("greedy Y misses a window inside Q", m, s, L, Q_mask)
        assert disj, ("greedy witnesses are not pairwise disjoint", m, s, L, Q_mask)
        assert len(witnesses) * L <= q, ("disjoint witnesses overflow Q",
                                         m, s, L, Q_mask, len(witnesses))
        assert out["Y_small"], ("|Y| > s-1", m, s, L, Q_mask, k)
        assert out["ceil_ge_s1"], ("ceil(m/L) < s+1 although m > sL", m, s, L)
        assert out["Y_u_Qc_hits_all"], ("Y u Q^c misses a cyclic window",
                                        m, s, L, Q_mask)
        assert out["cover_count_ok"], ("counting bound violated", m, s, L, Q_mask)
        assert out["transcript_consistent"], ("IMPOSSIBLE TRANSCRIPT",
                                              m, s, L, Q_mask)
        assert unsafe_all, ("some output is safe in every consistent world",
                            m, s, L, Q_mask, killer)
        assert out["not_terminal"], ("state is terminal", m, s, L, Q_mask)
    return out


def part_C(grid):
    print("\n" + "=" * 74)
    print("C. lower-bound certificate on EVERY Q with |Q| <= s*L - 1")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'L':>2} {'#Q tested':>10} {'max|Y|':>7} "
          f"{'min free':>9} {'min worlds':>11}")
    for (m, s, L) in grid:
        nQ = 0
        maxY = -1
        minfree = 10 ** 9
        minw = 10 ** 9
        for k in range(0, s * L):
            for Qt in combinations(range(m), k):
                qm = 0
                for p in Qt:
                    qm |= 1 << p
                r = certificate(m, s, L, qm, strict=True)
                nQ += 1
                maxY = max(maxY, r["|Y|"])
                minfree = min(minfree, r["|Y|"] + (m - k) - (s + 1))
                minw = min(minw, r["n_consistent_worlds"])
        print(f"   {m:>3} {s:>2} {L:>2} {nQ:>10} {maxY:>7} "
              f"{minfree:>9} {minw:>11}")
    print("   -> lower bound D_nonadaptive >= s*L verified constructively on this grid")
    print("      ('min free' = |Y|+|Q^c|-(s+1), must be >= 0 everywhere)")


# --------------------------------------------- D. negative control for part C

def part_D(grid):
    print("\n" + "=" * 74)
    print("D. NEGATIVE CONTROL: same certificate at |Q| = s*L must BREAK")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'L':>2} {'|Y|':>4} {'s-1':>4} "
          f"{'Y_small':>8} {'no_safe_output':>15} {'breaks':>7}")
    nbroke = 0
    for (m, s, L) in grid:
        qm = 0
        for i in range(s):
            for t in range(L):
                qm |= 1 << ((i * L + t) % m)
        assert popcount(qm) == s * L
        r = certificate(m, s, L, qm, strict=False)
        breaks = (not r["Y_small"]) or (not r["no_safe_output"])
        nbroke += breaks
        print(f"   {m:>3} {s:>2} {L:>2} {r['|Y|']:>4} {s-1:>4} "
              f"{str(r['Y_small']):>8} {str(r['no_safe_output']):>15} "
              f"{str(breaks):>7}")
    print(f"   -> broke in {nbroke}/{len(grid)} cells")
    if nbroke != len(grid):
        raise AssertionError(
            "the |Q|=sL control did NOT break everywhere: the part-C certificate "
            "is then not discriminating and part C proves nothing")


# ------------------------------------------------------- E. b-batch DP + H

def make_perms(m, L):
    """Dihedral maps g with A_{g(j)} = g(A_j).  Rotations and reflections all
    work for the cyclic interval family; verified, not assumed."""
    A = windows_cyclic(m, L)
    perms = []
    for refl in (0, 1):
        for sh in range(m):
            perm = [((-j if refl else j) + sh) % m for j in range(m)]
            ok = True
            for j in range(m):
                img = 0
                for w in range(m):
                    if A[j] >> w & 1:
                        img |= 1 << perm[w]
                if A[perm[j]] != img:
                    ok = False
                    break
            if ok:
                perms.append(perm)
    assert len(perms) >= m, ("rotation symmetry lost", m, L)
    return perms


def perm_tables(m, perms):
    tabs = []
    full = 1 << m
    for perm in perms:
        t = [0] * full
        for mask in range(full):
            o = 0
            mm = mask
            while mm:
                b = mm & -mm
                w = b.bit_length() - 1
                o |= 1 << perm[w]
                mm ^= b
            t[mask] = o
        tabs.append(t)
    return tabs


class BatchDP:
    def __init__(self, m, L, s):
        self.m, self.L, self.s = m, L, s
        self.A = windows_cyclic(m, L)
        self.tabs = perm_tables(m, make_perms(m, L))
        self.full = (1 << m) - 1
        self.memoH = {}
        self.memoB = {}

    def canon(self, q0, q1):
        best = None
        for t in self.tabs:
            k = (t[q0], t[q1])
            if best is None or k < best:
                best = k
        return best

    def term(self, q0, q1):
        return terminal(self.m, self.A, self.s, q0, q1)

    def cons(self, q0, q1):
        return consistent(self.m, self.s, q0, q1)

    def H(self, q0=0, q1=0):
        """Fully adaptive minimax depth (one query per round)."""
        if self.term(q0, q1):
            return 0
        key = self.canon(q0, q1)
        v = self.memoH.get(key)
        if v is not None:
            return v
        self.memoH[key] = INF
        best = INF
        asked = q0 | q1
        c1 = popcount(q1)
        for a in range(self.m):
            b = 1 << a
            if asked & b:
                continue
            vals = []
            if self.cons(q0 | b, q1):
                vals.append(self.H(q0 | b, q1))
            if c1 + 1 <= self.s and self.cons(q0, q1 | b):
                vals.append(self.H(q0, q1 | b))
            if not vals:
                continue
            w = max(vals)
            if w >= INF:
                continue
            if 1 + w < best:
                best = 1 + w
        self.memoH[key] = best
        return best

    def D(self, b, q0=0, q1=0):
        """Exact b-batch complexity.  The batch Q is committed BEFORE any of
        its replies is revealed: the recursion picks one Q, then takes the max
        over every consistent reply pattern on that same Q."""
        if self.term(q0, q1):
            return 0
        if b == 0:
            return INF
        key = (b,) + self.canon(q0, q1)
        v = self.memoB.get(key)
        if v is not None:
            return v
        self.memoB[key] = INF
        # Q = empty gives D_{b-1}; also the upper seed for the size prune.
        best = self.D(b - 1, q0, q1)
        asked = q0 | q1
        U = [a for a in range(self.m) if not (asked >> a & 1)]
        c1 = popcount(q1)
        for k in range(1, min(len(U), best - 1) + 1):
            for Qt in combinations(U, k):
                qm = 0
                for p in Qt:
                    qm |= 1 << p
                worst = 0
                feasible = True
                for r in range(0, min(self.s - c1, k) + 1):
                    if not feasible:
                        break
                    for yes in combinations(Qt, r):
                        ym = 0
                        for p in yes:
                            ym |= 1 << p
                        nq1 = q1 | ym
                        nq0 = q0 | (qm & ~ym)
                        if not self.cons(nq0, nq1):
                            continue           # child empty: no such world
                        cv = self.D(b - 1, nq0, nq1)
                        if cv >= INF:
                            feasible = False
                            break
                        if cv > worst:
                            worst = cv
                            if k + worst >= best:
                                feasible = False
                                break
                if feasible and k + worst < best:
                    best = k + worst
            if k >= best:
                break
        self.memoB[key] = best
        return best


def part_E(grid, bmax=3):
    """Exact b-batch DP.  The batch Q is COMMITTED before any of its replies is
    seen: BatchDP.D picks one Q and then maximises over every consistent reply
    pattern on that same Q.  If the implementation had silently allowed
    adaptivity inside a batch, D_2 would collapse to H in every cell; the
    assertion at the end of this function fails in that case."""
    print("\n" + "=" * 74)
    print("E. exact b-batch DP vs fully adaptive H vs nonadaptive sL")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'L':>2} {'sL':>3} " +
          " ".join(f"{'D_'+str(b):>4}" for b in range(1, bmax + 1)) +
          f" {'H':>3} {'law':>4} {'sL/H':>6} {'rounds':>7} {'sec':>6}")
    rows = []
    worst_ratio = 0.0
    n_two_round_insufficient = 0
    for (m, s, L) in grid:
        t0 = time.time()
        dp = BatchDP(m, L, s)
        h = dp.H()
        law = (s // 2) * (L + 1) + (s % 2) * L
        ds = [dp.D(b) for b in range(1, bmax + 1)]
        assert h < INF, ("infeasible although m > sL", m, s, L)
        assert ds[0] == s * L, ("D_1 != sL", m, s, L, ds[0])
        for i in range(1, len(ds)):
            assert ds[i] <= ds[i - 1], ("D_b not monotone in b", m, s, L, ds)
        for v in ds:
            assert v >= h, ("D_b below the fully adaptive H", m, s, L, ds, h)
        assert h == law, ("adaptive H != parity law", m, s, L, h, law)
        if L == 1:
            # Bridge to the ONLY Lean-level exact adaptive-depth theorem for
            # this primitive: CIGAMF.P13.SupportCardinalityQueryLaw
            # .adaptive_cardinality_lower / .adaptive_cardinality_attained,
            # whose safety predicate is zero_radius_iff : ... = 0 <-> j notin W,
            # i.e. exactly the L = 1 window A_j = {j}.  Depth is exactly s there.
            assert h == s, ("L=1 adaptive depth != s (contradicts the Lean "
                            "cardinality law)", m, s, h)
            assert ds[0] == s, ("L=1 nonadaptive depth != s", m, s, ds[0])
        rounds = next((b for b in range(1, bmax + 1) if ds[b - 1] == h), None)
        if len(ds) >= 2 and ds[1] > h:
            n_two_round_insufficient += 1
        ratio = (s * L) / h
        worst_ratio = max(worst_ratio, ratio)
        rows.append((m, s, L, s * L, ds, h, law, ratio, rounds))
        print(f"   {m:>3} {s:>2} {L:>2} {s*L:>3} " +
              " ".join(f"{v:>4}" for v in ds) +
              f" {h:>3} {law:>4} {ratio:>6.3f} "
              f"{(str(rounds) if rounds else '>'+str(bmax)):>7} "
              f"{time.time()-t0:>6.1f}")
    print(f"   -> LARGEST measured adaptivity ratio sL/H on this grid: {worst_ratio:.4f}")
    print(f"   -> cells where TWO batches are provably NOT enough: "
          f"{n_two_round_insufficient}")
    assert worst_ratio < 2.0, ("ratio reached 2 -- the closed form 2L/(L+1) < 2 "
                               "would be violated", worst_ratio)
    # NEGATIVE CONTROL on the DP itself.  A batch that leaked adaptivity would
    # make D_2 = H everywhere, so this must be nonzero on a grid that contains
    # s = 2, L >= 4.
    if any(s == 2 and L >= 4 for (m, s, L) in grid):
        assert n_two_round_insufficient > 0, (
            "D_2 == H in every cell including s=2, L>=4: the batch constraint "
            "is not binding and the DP is measuring per-query adaptivity")
    return rows, worst_ratio


# ------------------ E2. INDEPENDENT verifier for D_1 / D_2 and for H

def D1_naive(m, L, s, q0, q1):
    """min |Q| making every consistent reply terminal.  No symmetry, no memo,
    no pruning -- a separate code path from BatchDP.D."""
    A = windows_cyclic(m, L)
    if terminal(m, A, s, q0, q1):
        return 0
    U = [a for a in range(m) if not ((q0 | q1) >> a & 1)]
    for k in range(1, len(U) + 1):
        for Qt in combinations(U, k):
            qm = 0
            for p in Qt:
                qm |= 1 << p
            ok = True
            for r in range(0, k + 1):
                if not ok:
                    break
                for yes in combinations(Qt, r):
                    ym = 0
                    for p in yes:
                        ym |= 1 << p
                    nq1 = q1 | ym
                    nq0 = q0 | (qm & ~ym)
                    if not consistent(m, s, nq0, nq1):
                        continue
                    if not terminal(m, A, s, nq0, nq1):
                        ok = False
                        break
            if ok:
                return k
    return INF


def D2_naive(m, L, s):
    """min over Q1 of |Q1| + max over consistent replies of D1_naive(child).
    Completely independent of BatchDP (no dihedral canonicalisation, no
    memoisation, no incremental prune)."""
    A = windows_cyclic(m, L)
    if terminal(m, A, s, 0, 0):
        return 0
    best = D1_naive(m, L, s, 0, 0)
    for k in range(1, m + 1):
        if k >= best:
            break
        for Qt in combinations(range(m), k):
            qm = 0
            for p in Qt:
                qm |= 1 << p
            worst = 0
            feasible = True
            for r in range(0, min(s, k) + 1):
                if not feasible:
                    break
                for yes in combinations(Qt, r):
                    ym = 0
                    for p in yes:
                        ym |= 1 << p
                    nq1 = ym
                    nq0 = qm & ~ym
                    if not consistent(m, s, nq0, nq1):
                        continue
                    v = D1_naive(m, L, s, nq0, nq1)
                    if v >= INF:
                        feasible = False
                        break
                    worst = max(worst, v)
            if feasible and k + worst < best:
                best = k + worst
    return best


def part_E2(grid):
    print("\n" + "=" * 74)
    print("E2. INDEPENDENT code path for D_1, D_2 and for the adaptive H")
    print("=" * 74)
    try:
        from SUPPORT_depth_probe import optimal_depth, ball_windows_shim  # noqa
        have = True
    except Exception:
        have = False
    from SUPPORT_depth_probe import optimal_depth as repo_depth

    def repo_ball_windows(m, r):
        A = []
        for j in range(m):
            mask = 0
            for w in range(m):
                d = abs(j - w) % m
                if min(d, m - d) < r:
                    mask |= 1 << w
            A.append(mask)
        return A

    print(f"   {'m':>3} {'s':>2} {'L':>2} {'D1':>3} {'D1nv':>5} {'D2':>3} "
          f"{'D2nv':>5} {'H':>3} {'Hrepo':>6}")
    for (m, s, L) in grid:
        dp = BatchDP(m, L, s)
        d1, d2, h = dp.D(1), dp.D(2), dp.H()
        d1n = D1_naive(m, L, s, 0, 0)
        d2n = D2_naive(m, L, s)
        hr = "-"
        if L % 2 == 1:
            r = (L + 1) // 2
            hr_v, _ = repo_depth(m, repo_ball_windows(m, r), s)
            hr = str(hr_v)
            assert hr_v == h, ("repo optimal_depth on ball_windows disagrees "
                               "with N3 H", m, s, L, hr_v, h)
        assert d1 == d1n, ("D_1 code paths disagree", m, s, L, d1, d1n)
        assert d2 == d2n, ("D_2 code paths disagree", m, s, L, d2, d2n)
        print(f"   {m:>3} {s:>2} {L:>2} {d1:>3} {d1n:>5} {d2:>3} "
              f"{d2n:>5} {h:>3} {hr:>6}")
    print("   -> independent paths agree on every listed cell")


# ---------------------------------------------- F. m > sL is load bearing

def part_F(cases):
    print("\n" + "=" * 74)
    print("F. the hypothesis m > s*L is load bearing (m = s*L is INFEASIBLE)")
    print("=" * 74)
    print(f"   {'m':>3} {'s':>2} {'L':>2} {'H':>8} {'killer world':>22}")
    for (s, L) in cases:
        m = s * L
        if m < 2 or L > m:
            continue
        dp = BatchDP(m, L, s)
        h = dp.H()
        w = 0
        for i in range(s):
            w |= 1 << ((i * L) % m)
        A = windows_cyclic(m, L)
        assert popcount(w) == s
        assert all(A[j] & w for j in range(m)), ("equispaced world misses a "
                                                 "window at m = sL", m, s, L)
        assert h >= INF, ("m = sL is feasible; the hypothesis is not needed",
                          m, s, L, h)
        print(f"   {m:>3} {s:>2} {L:>2} {'INF':>8} "
              f"{'equispaced ' + bin(w):>22}")
    print("   -> at m = sL an equispaced world hits every window: no safe action")


# ------------------------------------------------------ closed-form ratio

def part_ratio_closed_form():
    print("\n" + "=" * 74)
    print("closed-form ratio sL / H, H = floor(s/2)(L+1) + (s mod 2) L")
    print("=" * 74)
    best = (0.0, None)
    for L in range(1, 41):
        for s in range(1, 41):
            h = (s // 2) * (L + 1) + (s % 2) * L
            r = (s * L) / h
            assert r < 2.0, ("ratio >= 2", s, L, r)
            if r > best[0]:
                best = (r, (s, L))
    print(f"   sup over 1<=s,L<=40: {best[0]:.6f} at (s,L)={best[1]}")
    print("   s even: sL/H = 2L/(L+1) < 2.   s odd: 2sL/(sL+s+L-1) < 2.")
    print("   sup over all s,L is 2, NEVER attained: bounded separation only.")


# ------------------------------------------------------------------- main

def main():
    t0 = time.time()
    part_0([(m, sv) for m in (4, 5, 6, 7) for sv in (0, 1, 2, 3)])
    gridA = [(m, s, L) for (m, s, L) in [
        (3, 1, 1), (4, 3, 1), (5, 4, 1), (7, 6, 1),
        (4, 1, 2), (5, 2, 2), (6, 2, 2), (8, 3, 2),
        (5, 1, 3), (8, 2, 3), (9, 2, 3),
        (6, 1, 4), (7, 1, 5), (11, 2, 5), (11, 3, 3),
    ] if m > s * L]
    part_A(gridA)

    gridB = [(m, s, L) for (m, s, L) in gridA if m <= 12 and s * L <= 10]
    part_B(gridB)
    part_C(gridB)
    part_D(gridB)

    gridE = [(m, s, L) for (m, s, L) in gridA if m <= 9]
    rows, wr = part_E(gridE, bmax=3)
    part_E2([(m, s, L) for (m, s, L) in gridA if m <= 7])

    # Round-collapse table.  Separate grid because these cells need b = 4 and
    # are the slow ones; everything here is <= ~15 s.
    print("\n" + "#" * 74)
    print("# ROUND TRADEOFF: how many batches are needed to reach H")
    print("#" * 74)
    gridR = [(3, 1, 1), (5, 2, 2), (7, 2, 3), (9, 2, 4), (11, 2, 5),
             (13, 2, 6), (15, 2, 7),
             (7, 3, 2), (10, 3, 3), (13, 3, 4),
             (11, 4, 2), (13, 4, 3), (11, 5, 2)]
    part_E(gridR, bmax=4)

    part_F([(1, 1), (2, 1), (3, 1), (4, 1), (2, 2), (3, 2), (2, 3), (2, 4)])
    part_ratio_closed_form()

    if "--long" in sys.argv:
        print("\n" + "#" * 74)
        print("# LONG cells (excluded from the default run for the time budget)")
        print("#" * 74)
        part_E([(16, 3, 5), (17, 2, 8)], bmax=2)
    else:
        print("\n   NOT RUN in this invocation (time budget), previously measured:")
        print("     m=16 s=3 L=5: D_2 = 11 = H  (15.6 s)")
        print("     m=17 s=2 L=8: D_2 = 11 > H = 9  (22.6 s)")
        print("   re-run them with:  python3 scripts/N3_nonadaptive_depth_probe.py --long")

    print(f"\nelapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
