#!/usr/bin/env python3
"""STRUCT probe 1: exact prefix-cover (menu) dimension by exhaustive
integer/rational computation.

Definitions mirrored EXACTLY from
  work/p13_conjectures/LeanStructuralPrefixCoverDimensionV1.lean
  work/p13_conjectures/LeanSupportGeometryV4.lean          (selectedRadius)
  work/p13_conjectures/LeanStructuralStaircaseFamilyV1.lean (staircaseF)

  EpsilonOptimalAt obj eps k S  :=  |S| = k  and  obj S <= obj T + eps for all |T| = k
  PrefixCover obj eps menu      :=  menu nonempty, every member a full ranking, and
                                    for every k <= |I| some ranking's k-prefix is
                                    EpsilonOptimalAt at k
  chi_prefix(obj, eps)          :=  sInf { |menu| : PrefixCover obj eps menu }

At eps = 0 a full ranking's k-prefix is optimal iff it minimises the objective
among all k-subsets, and the prefixes of a full ranking are exactly a maximal
chain in the Boolean lattice.  So

  chi_prefix(obj, 0) = min number of maximal chains of 2^I such that every
                       level k in {0..|I|} is met by some chain inside OPT_k.

All arithmetic here is exact: selectedRadius values are integers/2 and are
stored as the integer numerator (osc), so comparisons are integer comparisons.

Run:  python3 scripts/STRUCT_prefix_cover_exact.py
"""
from fractions import Fraction
from itertools import permutations
import sys

# ----------------------------------------------------------------------------
# exact objective machinery
# ----------------------------------------------------------------------------


def sumvec_table(vecs, n, nact):
    """sumvec[T] = sum of vecs[j] over j in bitmask T (exact ints)."""
    table = [None] * (1 << n)
    table[0] = tuple([0] * nact)
    for T in range(1, 1 << n):
        low = T & (-T)
        j = low.bit_length() - 1
        prev = table[T ^ low]
        v = vecs[j]
        table[T] = tuple(prev[a] + v[a] for a in range(nact))
    return table


def selected_radius_numerators(vecs, n, nact):
    """objective(S) = osc(sum_{j not in S} vecs[j]) / 2.

    Returns 2*objective(S) = osc, an integer, indexed by bitmask S.
    """
    table = sumvec_table(vecs, n, nact)
    full = (1 << n) - 1
    out = [0] * (1 << n)
    for S in range(1 << n):
        g = table[full ^ S]
        out[S] = max(g) - min(g)
    return out


def opt_levels(values, n):
    """values[S] = exact objective (any totally ordered exact type).
    Returns OPT[k] = list of bitmasks of popcount k attaining the level min."""
    best = [None] * (n + 1)
    opt = [[] for _ in range(n + 1)]
    for S in range(1 << n):
        k = bin(S).count("1")
        v = values[S]
        if best[k] is None or v < best[k]:
            best[k] = v
            opt[k] = [S]
        elif v == best[k]:
            opt[k].append(S)
    return opt, best


# ----------------------------------------------------------------------------
# exact minimum menu size
# ----------------------------------------------------------------------------


def maximal(masks):
    ms = sorted(set(masks), key=lambda m: -bin(m).count("1"))
    keep = []
    for m in ms:
        if not any((m | k) == k for k in keep):
            keep.append(m)
    return keep


def chain_level_masks(opt, n, cap=400000):
    """All maximal sets of levels coverable by a single maximal chain.

    Node (k, S) with S in OPT[k]; successors (k', S') with k' > k, S subset S'.
    Every chain contains the empty set, so we start from level 0.
    Returns (masks, ok) -- ok False means the cap was hit (NO silent truncation).
    """
    nodes = []
    for k in range(n + 1):
        for S in opt[k]:
            nodes.append((k, S))
    # index nodes by level, descending DP
    memo = {}
    budget = [cap]

    def F(idx):
        if idx in memo:
            return memo[idx]
        k, S = nodes[idx]
        out = [1 << k]
        for j, (k2, S2) in enumerate(nodes):
            if k2 <= k:
                continue
            if (S & S2) == S:  # S subset of S2
                for m in F(j):
                    out.append((1 << k) | m)
        res = maximal(out)
        budget[0] -= len(res)
        if budget[0] < 0:
            raise RuntimeError("mask cap exceeded")
        memo[idx] = res
        return res

    sys.setrecursionlimit(10000)
    roots = [i for i, (k, S) in enumerate(nodes) if k == 0]
    assert len(roots) == 1 and nodes[roots[0]][1] == 0
    try:
        res = F(roots[0])
    except RuntimeError:
        return None, False
    return res, True


def min_set_cover(masks, universe):
    """Exact minimum number of masks whose union is `universe` (branch & bound)."""
    masks = maximal(masks)
    best = [len(bin(universe)) + 5]

    def rec(covered, used):
        if covered == universe:
            best[0] = min(best[0], used)
            return
        if used + 1 >= best[0]:
            return
        rest = universe & ~covered
        # branch on the uncovered level with fewest covering masks
        lvls = [i for i in range(universe.bit_length()) if (rest >> i) & 1]
        pick, cands = None, None
        for i in lvls:
            c = [m for m in masks if (m >> i) & 1]
            if cands is None or len(c) < len(cands):
                pick, cands = i, c
            if not c:
                return  # uncoverable
        for m in cands:
            rec(covered | m, used + 1)

    rec(0, 0)
    return best[0]


def chi_prefix(values, n, verbose=False):
    opt, best = opt_levels(values, n)
    masks, ok = chain_level_masks(opt, n)
    if not ok:
        return None, opt, best
    universe = (1 << (n + 1)) - 1
    return min_set_cover(masks, universe), opt, best


def chi_prefix_bruteforce(values, n):
    """Independent check for small n: enumerate all n! maximal chains."""
    opt, _ = opt_levels(values, n)
    optset = [set(o) for o in opt]
    masks = set()
    for perm in permutations(range(n)):
        S, m = 0, 0
        if 0 in optset[0]:
            m |= 1
        for k, j in enumerate(perm, start=1):
            S |= 1 << j
            if S in optset[k]:
                m |= 1 << k
        masks.add(m)
    return min_set_cover(list(masks), (1 << (n + 1)) - 1)


# ----------------------------------------------------------------------------
# the staircase family  F_r  (LeanStructuralStaircaseFamilyV1)
# ----------------------------------------------------------------------------


def staircase(r):
    """Ground set StairRel r = Fin r x Bool, |I| = 2r.
    Actions StairAction r = Option (Fin r): index 0 is `none` (anchor), index
    i+1 is `some i`.
    staircaseF (i,b) none      = 0
    staircaseF (i,true)  (some a) = -1 if a <= i else 0
    staircaseF (i,false) (some a) =  1 if i = a else 0
    """
    idx = [(i, b) for i in range(r) for b in (False, True)]
    nact = r + 1
    vecs = []
    for (i, b) in idx:
        v = [0] * nact
        for a in range(r):
            if b:
                v[a + 1] = -1 if a <= i else 0
            else:
                v[a + 1] = 1 if i == a else 0
        vecs.append(tuple(v))
    return idx, vecs, nact


def stair_block(r, t, idx):
    """staircaseBlock t = {(t,true)} u {(i,false) : i <= t} as a bitmask."""
    m = 0
    for p, (i, b) in enumerate(idx):
        if (b and i == t) or ((not b) and i <= t):
            m |= 1 << p
    return m


def run_staircase(rmax):
    print("=" * 78)
    print("STAIRCASE FAMILY  F_r  (selectedRadius staircaseF), |I| = 2r")
    print("=" * 78)
    print(f"{'r':>2} {'|I|':>4} {'chi_exact':>10} {'Lean low r':>11} "
          f"{'Lean up 2r+1':>13} {'brute':>7}  unique-opt levels")
    rows = []
    for r in range(1, rmax + 1):
        idx, vecs, nact = staircase(r)
        n = 2 * r
        num = selected_radius_numerators(vecs, n, nact)  # 2*objective, integer
        chi, opt, best = chi_prefix(num, n)
        uniq = [k for k in range(n + 1) if len(opt[k]) == 1]
        brute = chi_prefix_bruteforce(num, n) if n <= 8 else None
        rows.append((r, n, chi, best, opt, idx))
        print(f"{r:>2} {n:>4} {chi:>10} {r:>11} {2*r+1:>13} "
              f"{str(brute):>7}  {uniq}")
        if brute is not None:
            assert brute == chi, f"DAG method and brute force disagree at r={r}"
    return rows


def verify_staircase_structure(rmax):
    """Check the closed-form description of OPT_k against brute force, and
    verify the explicit r-ranking menu really is a prefix cover."""
    print()
    print("-" * 78)
    print("closed form for OPT_k and the explicit r-ranking menu")
    print("-" * 78)
    for r in range(1, rmax + 1):
        idx, vecs, nact = staircase(r)
        n = 2 * r
        pos = {i: idx.index((i, False)) for i in range(r)}
        neg = {i: idx.index((i, True)) for i in range(r)}
        num = selected_radius_numerators(vecs, n, nact)
        opt, best = opt_levels(num, n)

        # predicted optimal values (as 2*objective = osc)
        ok_val = True
        for k in range(n + 1):
            m = n - k  # |T|, T = complement
            if m == 0:
                pred = 0
            elif m == 1:
                pred = 1
            elif m <= r + 1:
                pred = 0
            else:
                pred = m - r - 1
            if best[k] != pred:
                ok_val = False
                print(f"  r={r} k={k}: predicted osc {pred}, actual {best[k]}")

        # predicted OPT_k members
        ok_set = True
        for k in range(n + 1):
            m = n - k
            if 2 <= m <= r + 1:
                t = m - 2
                pred = {((1 << n) - 1) ^ stair_block(r, t, idx)}
            elif m == 0:
                pred = {(1 << n) - 1}
            elif m == 1:
                pred = {((1 << n) - 1) ^ (1 << p) for p in range(n)}
            else:  # m >= r+2: T = all positives + N, r-1 in N, |N| = m-r
                pred = set()
                from itertools import combinations
                nu = m - r
                for N in combinations(range(r), nu):
                    if r - 1 not in N:
                        continue
                    T = 0
                    for i in range(r):
                        T |= 1 << pos[i]
                    for t in N:
                        T |= 1 << neg[t]
                    pred.add(((1 << n) - 1) ^ T)
            if set(opt[k]) != pred:
                ok_set = False
                print(f"  r={r} k={k}: OPT mismatch "
                      f"(pred {len(pred)} vs actual {len(opt[k])})")

        # explicit menu of r rankings
        menu = []
        for t in range(r):
            low = [neg[a] for a in range(r) if a not in (t, r - 1)]
            Sblock = stair_block(r, t, idx)
            Sel = [p for p in range(n) if not (Sblock >> p) & 1]
            rest = [p for p in Sel if p not in low]
            blk = [p for p in range(n) if (Sblock >> p) & 1]
            menu.append(low + rest + blk)
        covered = set()
        for perm in menu:
            assert sorted(perm) == list(range(n)), "not a permutation"
            S = 0
            if 0 in opt[0]:
                covered.add(0)
            for k, j in enumerate(perm, start=1):
                S |= 1 << j
                if S in opt[k]:
                    covered.add(k)
        full = covered == set(range(n + 1))
        # antichain packing certificate: the r unique zero-radius optima
        blocks = [((1 << n) - 1) ^ stair_block(r, t, idx) for t in range(r)]
        anti = all(not (blocks[s] & blocks[t] == blocks[s])
                   for s in range(r) for t in range(r) if s != t)
        print(f"  r={r:>2}: OPT values match closed form: {ok_val};  "
              f"OPT sets match: {ok_set};  explicit {r}-menu covers all "
              f"{n+1} levels: {full};  packing antichain of size {r}: {anti}")
        assert ok_val and ok_set and full and anti


# ----------------------------------------------------------------------------
# the repo's own selectedRadius witnesses
# ----------------------------------------------------------------------------


def repo_witnesses():
    print()
    print("=" * 78)
    print("REPO selectedRadius WITNESSES (exact chi, not just the proved >=)")
    print("=" * 78)

    # chi3F : Fin 5 -> Fin 5 -> R   (LeanStructuralPrefixCoverChi3WitnessV1)
    chi3 = [[0] * 5 for _ in range(5)]
    for (j, a, v) in [(0, 3, -1), (0, 4, -1), (1, 2, -3), (1, 4, -3),
                      (2, 1, 3), (2, 3, 3), (3, 0, 3), (3, 2, 3), (3, 4, 3),
                      (4, 0, -3)]:
        chi3[j][a] = v
    # chi4F : Fin 6 -> Fin 5 -> R   (LeanStructuralActualChi4WitnessV1)
    chi4 = [[3, 4, 4, 1, -1], [-2, 5, 1, -1, 1], [-4, 2, -2, 4, -5],
            [5, -4, 4, -4, -5], [4, 0, -4, -5, 0], [-2, -2, 2, -3, -4]]
    # scalarF7 : Fin 7 -> Fin 2 -> R (LeanStructuralScalarChi5WitnessV1)
    w7 = [-32, 7, 29, -7, -8, -13, 18]
    scal = [[w, 0] for w in w7]

    for name, vecs, claim in [("chi3F  (n=5)", chi3, 3),
                              ("chi4F  (n=6)", chi4, 4),
                              ("scalarF7 (n=7)", scal, 5)]:
        n = len(vecs)
        nact = len(vecs[0])
        num = selected_radius_numerators([tuple(v) for v in vecs], n, nact)
        chi, opt, best = chi_prefix(num, n)
        brute = chi_prefix_bruteforce(num, n) if n <= 7 else None
        uniq = [k for k in range(n + 1) if len(opt[k]) == 1]
        print(f"{name}: exact chi_prefix = {chi}  (brute force {brute}; "
              f"repo proves >= {claim}; universal ceiling n-2 = {n-2})")
        print(f"    optimal values 2*obj per level: "
              f"{[best[k] for k in range(n+1)]}")
        print(f"    levels with a UNIQUE optimum: {uniq}")
        assert brute is None or brute == chi
        for k in range(n + 1):
            if len(opt[k]) == 1:
                S = opt[k][0]
                print(f"      k={k}: unique optimum "
                      f"{sorted(i for i in range(n) if (S >> i) & 1)}")


if __name__ == "__main__":
    rows = run_staircase(7)
    verify_staircase_structure(7)
    repo_witnesses()
    print()
    print("done.")
