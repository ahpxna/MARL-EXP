#!/usr/bin/env python3
"""SUPPORT probe 2/2 -- exhaustive optimal decision-tree depth vs epsilon.

The game (derived, not assumed -- see SUPPORT_geometry_probe.py for the exact
verification of the radius law that produces it):

  * hidden world  W subset Z_m,  |W| = s  (or |W| <= s, both computed).
  * physical membership query, unchanged from
    LeanSupportPhysicalQueryContractV1 / LeanSupportCardinalityQueryLawV1:
        oracle(a) = (P_a in support W) = (a in W),  one bit.
  * decision = a coordinate j; it is EPSILON-SAFE iff
        selectedRadius (components W) {j} <= eps
    which by the verified radius law is
        max_{w in W} h_w * f(d_m(j,w)) <= 2*eps
    i.e.  W cap A_j = empty,  where  A_j = {w : h_w f(d_m(j,w)) > 2 eps}.

  A deterministic adaptive tree is VALID at eps iff on every branch its output
  is eps-safe for every W consistent with the answers on that branch.  D is the
  minimum worst-case depth of a valid tree.  Computed by exact minimax over
  knowledge states -- no sampling, no floats in the safety test.

Conjectured matching law (homogeneous kernel, window length L = 2r-1):
        D = floor(s/2)*(L+1) + (s mod 2)*L
          = r*s + (r-1)*[s odd]
General candidate law (any window family):
        D = min over compositions s = t_1+...+t_k of  sum_i ( g(t_i) + t_i )
        g(t) = min #cleared points that create t simultaneous threats.

Run:  python3 scripts/SUPPORT_depth_probe.py
"""
from fractions import Fraction as Fr
from itertools import combinations
import sys, time

INF = 10 ** 6

# ----------------------------------------------------- window family from eps

def cyc(m, a, b):
    d = abs(a - b) % m
    return min(d, m - d)

def tent(rho):
    return lambda d: Fr(max(0, rho + 1 - d))

def windows(m, ker, h, eps):
    """A_j = {w : h_w * f(d(j,w)) > 2 eps}  as bitmasks. Exact rationals."""
    two_eps = 2 * eps
    A = []
    for j in range(m):
        mask = 0
        for w in range(m):
            if h[w] * ker(cyc(m, j, w)) > two_eps:
                mask |= 1 << w
        A.append(mask)
    return A

def reaches(m, ker, h, eps):
    """r_w = min{d : h_w f(d) <= 2 eps}; w in A_j iff d(j,w) < r_w."""
    out = []
    for w in range(m):
        rw = 0
        for d in range(0, m):
            if h[w] * ker(d) <= 2 * eps:
                rw = d
                break
        else:
            rw = m
        out.append(rw)
    return out

# ------------------------------------------------------------- symmetry group

def sym_group(m, A):
    """All dihedral maps g with A_{g(j)} = g(A_j) for all j."""
    g = []
    for refl in (0, 1):
        for sh in range(m):
            perm = [((-j if refl else j) + sh) % m for j in range(m)]
            ok = True
            for j in range(m):
                img = 0
                mask = A[j]
                for w in range(m):
                    if mask >> w & 1:
                        img |= 1 << perm[w]
                if A[perm[j]] != img:
                    ok = False
                    break
            if ok:
                g.append(perm)
    return g

def apply_perm(perm, mask, m):
    out = 0
    for w in range(m):
        if mask >> w & 1:
            out |= 1 << perm[w]
    return out

# ------------------------------------------------------------------- minimax

class Game:
    def __init__(self, m, A, s, exact=True, use_sym=True):
        self.m = m
        self.A = A
        self.s = s
        self.exact = exact
        self.full = (1 << m) - 1
        self.memo = {}
        self.group = sym_group(m, A) if use_sym else [list(range(m))]
        self.nodes = 0

    def canon(self, q0, q1):
        best = None
        for perm in self.group:
            k = (apply_perm(perm, q0, self.m), apply_perm(perm, q1, self.m))
            if best is None or k < best:
                best = k
        return best

    def consistent(self, q0, q1):
        c1 = bin(q1).count("1")
        if c1 > self.s:
            return False
        if not self.exact:
            return True
        free = self.m - bin(q0 | q1).count("1")
        return free >= self.s - c1

    def terminal(self, q0, q1):
        c1 = bin(q1).count("1")
        for j in range(self.m):
            a = self.A[j]
            if a & q1:
                continue
            if c1 == self.s or (a & ~q0) == 0:
                return True
        return False

    def D(self, q0, q1):
        if self.terminal(q0, q1):
            return 0
        key = self.canon(q0, q1)
        v = self.memo.get(key)
        if v is not None:
            return v
        self.nodes += 1
        self.memo[key] = INF          # cycle guard (cannot recur: masks grow)
        best = INF
        asked = q0 | q1
        c1 = bin(q1).count("1")
        for a in range(self.m):
            bit = 1 << a
            if asked & bit:
                continue
            vals = []
            if self.consistent(q0 | bit, q1):
                vals.append(self.D(q0 | bit, q1))
            if c1 + 1 <= self.s and self.consistent(q0, q1 | bit):
                vals.append(self.D(q0, q1 | bit))
            if not vals:
                continue
            w = max(vals)
            if w >= INF:
                continue
            if 1 + w < best:
                best = 1 + w
        self.memo[key] = best
        return best

def optimal_depth(m, A, s, exact=True, use_sym=True):
    g = Game(m, A, s, exact, use_sym)
    return g.D(0, 0), g.nodes

# -------------------------------------------------------- independent checker

def optimal_depth_naive(m, A, s, exact=True):
    """Same value, computed WITHOUT symmetry reduction and WITHOUT memo reuse
    across calls -- an independent implementation path to cross-check."""
    full = (1 << m) - 1
    memo = {}

    def cons(q0, q1):
        c1 = bin(q1).count("1")
        if c1 > s:
            return False
        if not exact:
            return True
        return (m - bin(q0 | q1).count("1")) >= s - c1

    def term(q0, q1):
        c1 = bin(q1).count("1")
        for j in range(m):
            a = A[j]
            if a & q1:
                continue
            if c1 == s or (a & ~q0) == 0:
                return True
        return False

    def rec(q0, q1):
        if term(q0, q1):
            return 0
        k = (q0, q1)
        if k in memo:
            return memo[k]
        memo[k] = INF
        best = INF
        c1 = bin(q1).count("1")
        for a in range(m):
            b = 1 << a
            if (q0 | q1) & b:
                continue
            vals = []
            if cons(q0 | b, q1):
                vals.append(rec(q0 | b, q1))
            if c1 + 1 <= s and cons(q0, q1 | b):
                vals.append(rec(q0, q1 | b))
            if not vals:
                continue
            w = max(vals)
            if w < INF and 1 + w < best:
                best = 1 + w
        memo[k] = best
        return best

    return rec(0, 0)

# ------------------------------------------------------------- candidate laws

def law_product_parity(s, r):
    """D = r*s + (r-1)*[s odd]   (== floor(s/2)*2r + (s mod 2)*(2r-1))"""
    if r == 0:
        return 0
    return r * s + (r - 1) * (s % 2)

def law_naive_sL(s, r):
    """NEGATIVE CONTROL: the 'sweep' bound s*(2r-1). Must be WRONG for r>=2,s>=2."""
    return s * (2 * r - 1)

def law_window_only(s, r):
    """NEGATIVE CONTROL: '2r-1', ignores s. Must be WRONG for s>=2."""
    return max(0, 2 * r - 1)

def g_threats(m, A, t):
    """g(t) = min |N| over cleared sets N such that there are >= t distinct
    points p with some A_j subset N u {p}.  Exhaustive over |N| ascending.
    Only used for small m (it is exponential)."""
    if t <= 0:
        return 0
    for k in range(0, m + 1):
        for N in combinations(range(m), k):
            nm = 0
            for x in N:
                nm |= 1 << x
            threats = set()
            for p in range(m):
                if nm >> p & 1:
                    continue
                nm2 = nm | (1 << p)
                for j in range(m):
                    if (A[j] & ~nm2) == 0 and not (A[j] & 0):
                        threats.add(p)
                        break
            if len(threats) >= t:
                return k
    return INF

def law_general(m, A, s):
    """D = min over compositions of s of sum_i (g(t_i) + t_i)."""
    gs = {}
    for t in range(1, s + 1):
        gs[t] = g_threats(m, A, t)
    best = [INF] * (s + 1)
    best[0] = 0
    for k in range(1, s + 1):
        for t in range(1, k + 1):
            if gs[t] >= INF or best[k - t] >= INF:
                continue
            v = best[k - t] + gs[t] + t
            if v < best[k]:
                best[k] = v
    return best[s]

# --------------------------------------------------------------------- main

def banner(t):
    print("\n" + "=" * 74)
    print(t)
    print("=" * 74)

def main():
    t0 = time.time()
    banner("SUPPORT depth probe -- exact minimax over knowledge states")

    # ---- Part A: homogeneous correlated family, D(m,s,r) ----------------
    banner("A. homogeneous correlated family: D(m,s,r) vs law r*s+(r-1)*[s odd]")
    print("   window A_j = cyclic ball of radius r-1 (length L=2r-1)")
    print(f"   {'m':>3} {'s':>2} {'r':>2} {'L':>2} {'D(|W|=s)':>9} {'D(|W|<=s)':>10} "
          f"{'law':>5} {'sL':>4} {'2r-1':>5} {'states':>8}")
    rows = []
    for r in (1, 2, 3):
        L = 2 * r - 1
        for s in (1, 2, 3, 4):
            for m in range(max(5, s * L + 1), 14):
                if 2 * r - 1 >= m:
                    continue
                # homogeneous: reach r everywhere
                A = []
                for j in range(m):
                    mask = 0
                    for w in range(m):
                        if cyc(m, j, w) < r:
                            mask |= 1 << w
                    A.append(mask)
                if s * L + 1 > m:
                    continue
                d_eq, nodes = optimal_depth(m, A, s, exact=True)
                d_le, _ = optimal_depth(m, A, s, exact=False)
                lw = law_product_parity(s, r)
                rows.append((m, s, r, d_eq, d_le, lw))
                print(f"   {m:>3} {s:>2} {r:>2} {L:>2} {d_eq:>9} {d_le:>10} "
                      f"{lw:>5} {law_naive_sL(s,r):>4} {law_window_only(s,r):>5} "
                      f"{nodes:>8}")

    banner("A-summary: where does the law hold?")
    ok = [x for x in rows if x[3] == x[5]]
    bad = [x for x in rows if x[3] != x[5]]
    print(f"   matches (|W|=s): {len(ok)}/{len(rows)}")
    if bad:
        print("   MISMATCHES (m,s,r,D,D_le,law):")
        for b in bad:
            print("     ", b)
    print("   NOTE: mismatches at small m are expected -- the cycle is too")
    print("   short to host disjoint phases; the law is claimed only for")
    print("   m >= m0(s,r), read off below.")

    # smallest m at which the law holds and keeps holding
    banner("A-threshold: smallest m from which D == law for all larger tested m")
    for r in (1, 2, 3):
        for s in (1, 2, 3, 4):
            sub = sorted([x for x in rows if x[1] == s and x[2] == r])
            if not sub:
                continue
            thr = None
            for i in range(len(sub)):
                if all(sub[k][3] == sub[k][5] for k in range(i, len(sub))):
                    thr = sub[i][0]
                    break
            lw = law_product_parity(s, r)
            print(f"   s={s} r={r} law={lw:>3}  m0={thr}   "
                  f"(tested m in {sub[0][0]}..{sub[-1][0]}, "
                  f"D values {[x[3] for x in sub]})")

    # ---- Part B: negative controls --------------------------------------
    banner("B. NEGATIVE CONTROLS -- checks that can return False")
    nc = 0
    # B1 the naive sweep law s*L must be WRONG somewhere
    diff = [x for x in rows if x[3] != law_naive_sL(x[1], x[2])]
    print(f"   B1  D != s*(2r-1) in {len(diff)}/{len(rows)} rows "
          f"-> the naive sweep law is REFUTED. e.g. {diff[0] if diff else None}")
    nc += 1 if diff else 0
    # B2 the window-only law must be WRONG somewhere
    diff2 = [x for x in rows if x[3] != law_window_only(x[1], x[2])]
    print(f"   B2  D != (2r-1) in {len(diff2)}/{len(rows)} rows "
          f"-> the 'clear one window' law is REFUTED.")
    nc += 1 if diff2 else 0
    # B3 the cardinality-law value s must be WRONG for r>=2
    diff3 = [x for x in rows if x[2] >= 2 and x[3] != x[1]]
    print(f"   B3  D != s in {len(diff3)} of the {len([x for x in rows if x[2]>=2])} "
          f"rows with r>=2 -> NOT a renaming of the cardinality law.")
    nc += 1 if diff3 else 0
    # B4 mutilate the geometry: drop one window -> D must change somewhere
    m, r, s = 11, 2, 2
    A = []
    for j in range(m):
        mask = 0
        for w in range(m):
            if cyc(m, j, w) < r:
                mask |= 1 << w
        A.append(mask)
    d_full, _ = optimal_depth(m, A, s, use_sym=True)
    A2 = list(A)
    A2[0] = (1 << m) - 1          # window 0 becomes unusable
    d_cut, _ = optimal_depth(m, A2, s, use_sym=False)
    print(f"   B4  m=11 r=2 s=2: D(full)={d_full}, D(one window destroyed)={d_cut}"
          f"  -> {'CHANGED' if d_cut != d_full else 'UNCHANGED (probe is blind!)'}")
    # B5 independent implementation cross-check
    banner("B5. cross-check: symmetry-reduced minimax vs naive minimax")
    agree = dis = 0
    for (m, s, r) in [(7, 1, 2), (8, 2, 2), (9, 2, 2), (10, 3, 2), (11, 2, 3),
                      (9, 3, 1), (10, 4, 1), (11, 2, 2), (12, 2, 3)]:
        A = []
        for j in range(m):
            mask = 0
            for w in range(m):
                if cyc(m, j, w) < r:
                    mask |= 1 << w
            A.append(mask)
        a, _ = optimal_depth(m, A, s)
        b = optimal_depth_naive(m, A, s)
        flag = "OK " if a == b else "DIFF"
        if a == b:
            agree += 1
        else:
            dis += 1
        print(f"   {flag} m={m} s={s} r={r}: sym={a} naive={b}")
    print(f"   agree={agree} disagree={dis}")

    # ---- Part C: the epsilon phase curve --------------------------------
    banner("C. THE PHASE CURVE  D vs epsilon  (tent kernel, homogeneous h=1)")
    for m, rho in [(11, 2), (13, 3)]:
        ker = tent(rho)
        h = [Fr(1)] * m
        for s in (1, 2, 3):
            print(f"\n   m={m} rho={rho} s={s}   (f(d)=max(0,{rho}+1-d), h=1)")
            print(f"      {'eps':>6} {'2eps':>5} {'r(eps)':>7} {'|A_j|':>6} "
                  f"{'D':>4} {'law':>4}")
            prev = None
            for k in range(0, 2 * (rho + 1) + 1):
                eps = Fr(k, 2)
                A = windows(m, ker, h, eps)
                rr = reaches(m, ker, h, eps)
                r = rr[0]
                sz = bin(A[0]).count("1")
                if all(x == 0 for x in A):
                    d = 0
                else:
                    if s * max(1, sz) + 1 > m:
                        print(f"      {str(eps):>6} {str(2*eps):>5} {r:>7} {sz:>6} "
                              f"{'INFEAS':>4} {'-':>4}   (no safe j exists for "
                              f"some W: needs m >= s*|A|+1)")
                        continue
                    d, _ = optimal_depth(m, A, s)
                lw = law_product_parity(s, r)
                mark = "" if d == lw else "   <-- law MISS"
                print(f"      {str(eps):>6} {str(2*eps):>5} {r:>7} {sz:>6} "
                      f"{d:>4} {lw:>4}{mark}")
                if prev is not None and prev != d:
                    pass
                prev = d

    # ---- Part D: HETEROGENEOUS family -----------------------------------
    banner("D. HETEROGENEOUS heights -- the family of record")
    print("   h_w = 1 (even w) / 1/2 (odd w):  tall tips have a bigger danger")
    print("   ball than short tips at the SAME epsilon, so the window family")
    print("   {A_j} is no longer a single ball size.  Tests the general law.")
    for m, rho in [(11, 2), (12, 2), (13, 3)]:
        ker = tent(rho)
        h = [Fr(1) if w % 2 == 0 else Fr(1, 2) for w in range(m)]
        for s in (1, 2):
            print(f"\n   m={m} rho={rho} s={s}")
            print(f"      {'eps':>6} {'r_even':>7} {'r_odd':>6} "
                  f"{'|A_j| sizes':>14} {'D':>4} {'gen-law':>8} {'hom-law':>8}")
            for k in range(0, 2 * (rho + 1) + 1):
                eps = Fr(k, 4)
                A = windows(m, ker, h, eps)
                rr = reaches(m, ker, h, eps)
                sizes = sorted({bin(a).count("1") for a in A})
                if all(x == 0 for x in A):
                    d, gl = 0, 0
                else:
                    maxsz = max(bin(a).count("1") for a in A)
                    if s * maxsz + 1 > m:
                        print(f"      {str(eps):>6} {rr[0]:>7} {rr[1]:>6} "
                              f"{str(sizes):>14} {'INFEAS':>4}")
                        continue
                    d, _ = optimal_depth(m, A, s)
                    gl = law_general(m, A, s) if m <= 13 and s <= 2 else -1
                hl = law_product_parity(s, rr[0])
                mark = "" if d == gl else "  <-- gen-law MISS"
                print(f"      {str(eps):>6} {rr[0]:>7} {rr[1]:>6} "
                      f"{str(sizes):>14} {d:>4} {gl:>8} {hl:>8}{mark}")

    print(f"\nelapsed {time.time()-t0:.1f}s")

if __name__ == "__main__":
    main()
