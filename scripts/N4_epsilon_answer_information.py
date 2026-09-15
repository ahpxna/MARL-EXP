#!/usr/bin/env python3
"""N4 -- is an epsilon-GOOD decision informationally cheaper than recovering A?

Setting: the corner-reference construction of
work/p13_conjectures/LeanD6ThresholdConstructionV1.lean.  Ground set
I(n) = Fin(n+1) with n = 2q+1, a distinguished coordinate j, labels A with
|A| = q+1, j notin A, |others A j| = q.  Everything below re-implements the
Lean primitives (`world`, `gate`, `query`, `jointCorner`, `plainCorner`,
`productCompressionLoss`, `meanOffset`, `meanSlope`) from their source text and
CHECKS them against each other; nothing is taken on faith from a docstring.

Objects
-------
  Regret(A, S, mu)  = loss(S) - loss(A^c);   Lean `actual_regret` says it is
                      (2-mu)*|S cap A|/2.  Part A verifies that by brute force
                      over all 2^(n+1) corners, not by citing the theorem.
  answer B          <-> output S = B^c, so Regret = (2-mu)*|A \ B|/2.
  Ball_eps(A,mu)    = { B valid label : (2-mu)*|A \ B|/2 <= eps }.
  bad_eps(B)        = { (A',nu) valid, nu in [0,1] : (2-nu)*|A' \ B|/2 > eps }
                      -- STRICT >, and the alternative uses ITS OWN nu.
  Gamma_eps(A,mu)   = max_{B in Ball_eps} sup_w inf_{(A',nu) in bad_eps(B)}
                          sum_e w_e KL(P_{A,mu,e}, P_{A',nu,e}),
                      w a probability vector on the FULL legal measurement set
                      E_q, KL = (mean difference)^2/2 (Lean
                      `information_eq_mean`).
  Gamma_0           = the eps = 0 instance = sup_w allocationValue(A,j,mu,E,w)
                      of LeanD6AllocationRiskBridgeV1.

Traps that are handled explicitly (supervisor's list)
  (a) the bad set is empty exactly when eps >= q; every cell with eps >= q is
      SKIPPED and named, never silently read as an sInf of the empty set;
  (b) alternatives are (A', nu) with their own nu; the true mu is never reused;
  (c) the boundary is strict (>).  Part E2 measures how much that matters: the
      objective is a quadratic in nu, hence continuous, so the inf over the
      half-open nu-set equals the min over its closure.  That equality is
      CHECKED numerically (shrinking delta), not assumed;
  (d) Gamma_eps >= Gamma_0 is asserted in every computed cell.

Method.  For a fixed answer shell d = |A \ B| the stabiliser of (A,B,j) is
S_{A cap B} x S_{A\B} x S_{B\A} x S_{rest}; the objective is invariant and
concave in w, so a cell-symmetric w is optimal and the alternative A' only
matters through its cell profile.  Part B CHECKS both of those reductions
against unreduced evaluation.  The resulting max-min is solved exactly in
rational arithmetic by constraint generation over a simplex (Bland's rule);
each reported value carries a certificate: LP value over the generated subset
== the exact best-response value at the returned w.

SKIPPED / SHRUNK, stated not silent
  * q is limited to {2,3,4,5}; q = 6 was not run (measurement set grows like
    sum_{k<=q} C(2q+1,k), ~8k at q=6, and the per-(shell,class) accumulation
    then exceeds the 5 minute budget).
  * mu is taken from a small rational grid (0, 1/2, 3/4, 1); the mu-dependence
    is NOT swept finely.
  * eps grid is chosen around the thresholds 1/2, d/2, d, and the normalised
    point eps = c*(q+1).  It is a grid, not a proof of the phase law between
    grid points; Part E1 is the only statement proved for a continuum of eps
    (0 <= eps <= 1/2), and there it is proved structurally (set equality),
    with the numerics as a control.
  * the outer max over B is computed over answer SHELLS d = 0..q, which is
    exhaustive up to the symmetry verified in Part B, not over all C(2q+1,q+1)
    individual labels.

Run:  python3 scripts/N4_epsilon_answer_information.py
"""
from fractions import Fraction as Fr
from itertools import combinations
import json
import sys
import time

OUT = "/Users/phanan/cig-amf-main/research/high_risk_20260910/N4_epsilon_answer_information.json"

# --------------------------------------------------------------------------
# 0.  Lean primitives, re-implemented from source text
# --------------------------------------------------------------------------


def bit(b):
    return Fr(1) if b else Fr(0)


def gate(A, j, x, V):
    """LeanD6ThresholdConstructionV1.gate.  x is a set of true coordinates."""
    if j in x:
        return Fr(0)
    if any(i in x for i in A):
        return Fr(1)
    others = set(V) - set(A) - {j}
    if len(others & x) >= 2:
        return Fr(1)
    return Fr(0)


def coeff(A, j, mu, i):
    if i in A:
        return Fr(0)
    if i == j:
        return mu - 1
    return 1 - mu


def slope_lean(A, j, mu, i):
    """LeanD6ThresholdConstructionV1.slope."""
    if i in A:
        return Fr(1)
    if i == j:
        return mu - 1
    return 1 - mu


def world(A, j, mu, x, V):
    """LeanD6ThresholdConstructionV1.world = linear (coeff ..) + gate."""
    tot = Fr(0)
    for i in x:
        tot += coeff(A, j, mu, i)
    return tot + gate(A, j, x, V)


def joint_corner(G, j):
    return frozenset(set(G) | {j})


def plain_corner(G):
    return frozenset(G)


def query_x(G, j, h):
    """LeanD6AllocationFiniteBridgeV1.query."""
    return joint_corner(G, j) if h else plain_corner(G)


def legal_measurements(V, j, q):
    """LeanD6AllocationDualBridgeV1.Legal, over Measurement n = I n + (Finset x Bool)."""
    out = [("s", i) for i in V]
    pool = [i for i in V if i != j]
    for k in range(0, q + 1):
        for G in combinations(pool, k):
            out.append(("q", frozenset(G), True))
            if k >= 2:
                out.append(("q", frozenset(G), False))
    return out


def mean_affine(A, j, e, V):
    """(meanOffset, meanSlope) of LeanD6GaussianQueryDominanceV1."""
    if e[0] == "s":
        i = e[1]
        if i in A:
            return (Fr(1), Fr(0))
        if i == j:
            return (Fr(-1), Fr(1))
        return (Fr(1), Fr(-1))
    G, h = e[1], e[2]
    others = set(V) - set(A) - {j}
    c = Fr(len(set(G) & others)) - bit(h)
    return ((Fr(0) if h else Fr(1)) + c, -c)


def actual_mean(A, j, mu, e, V):
    """actualMean, evaluated through `world`, i.e. the primitive route."""
    if e[0] == "s":
        # productResponse corner (world A j mu) i true = world A j mu (update zero i true)
        return world(A, j, mu, frozenset({e[1]}), V)
    return world(A, j, mu, query_x(e[1], j, e[2]), V)


def compression_loss(A, j, mu, S, V):
    """productCompressionLoss H Q S = osc (x -> H x - sum_{i in S} Q i (x i))/2."""
    lo = None
    hi = None
    n = len(V)
    for mask in range(1 << n):
        x = frozenset(V[t] for t in range(n) if (mask >> t) & 1)
        val = world(A, j, mu, x, V)
        for i in S:
            if i in x:
                val -= slope_lean(A, j, mu, i)
        if lo is None or val < lo:
            lo = val
        if hi is None or val > hi:
            hi = val
    return (hi - lo) / 2


# --------------------------------------------------------------------------
# PART A.  primitive self-checks (these can, and must be able to, FAIL)
# --------------------------------------------------------------------------


def part_A():
    print("=" * 74)
    print("A. primitives: affine mean law, regret closed form, exchange ball")
    print("=" * 74)
    for q in (2, 3):
        V = list(range(2 * q + 2))
        j = 2 * q + 1
        A = frozenset(range(q + 1))
        E = legal_measurements(V, j, q)
        # A1 -- actual_mean == meanOffset + meanSlope*mu, on every legal e
        for mu in (Fr(0), Fr(1, 3), Fr(1, 2), Fr(1)):
            for e in E:
                off, sl = mean_affine(A, j, e, V)
                got = actual_mean(A, j, mu, e, V)
                if got != off + sl * mu:
                    raise AssertionError(
                        f"actual_mean_affine FAILS q={q} mu={mu} e={e}: "
                        f"{got} != {off}+{sl}*{mu}")
        print(f"   q={q}: affine mean law holds on all {len(E)} legal measurements")
        # A2 -- regret closed form, brute force over all 2^(n+1) corners
        labels = [frozenset(c) for c in combinations([i for i in V if i != j], q + 1)]
        for mu in (Fr(0), Fr(1, 2), Fr(1)):
            base = compression_loss(A, j, mu, frozenset(set(V) - set(A)), V)
            for B in labels[: 12 if q == 3 else len(labels)]:
                S = frozenset(set(V) - set(B))
                got = compression_loss(A, j, mu, S, V) - base
                want = (2 - mu) * len(A - B) / 2
                if got != want:
                    raise AssertionError(
                        f"actual_regret FAILS q={q} mu={mu} B={sorted(B)}: "
                        f"{got} != {want}")
        print(f"   q={q}: Regret(A,B^c) == (2-mu)|A\\B|/2 verified by brute force"
              f" over 2^{len(V)} corners"
              + ("  (12 labels sampled at q=3)" if q == 3 else ""))
        # A3 -- exchange-ball membership vs. direct regret, and trap (a)
        for mu in (Fr(0), Fr(1, 2), Fr(1)):
            for eps in (Fr(0), Fr(1, 4), Fr(1, 2), Fr(1), Fr(3, 2)):
                ball = [B for B in labels if (2 - mu) * len(A - B) <= 2 * eps]
                for B in ball:
                    if (2 - mu) * len(A - B) / 2 > eps:
                        raise AssertionError("ball membership inconsistent")
                # trap (a): the bad set is nonempty iff eps < q
                worst = max(len(Ap - B) for Ap in labels for B in ball)
                nonempty = (worst * Fr(2) / 2) > eps  # nu = 0 maximises (2-nu)d'/2
                if nonempty != (eps < q):
                    raise AssertionError(
                        f"empty-bad-set threshold wrong: q={q} eps={eps} "
                        f"nonempty={nonempty}")
        print(f"   q={q}: bad set nonempty  <=>  eps < q   (trap (a) boundary) OK")
    return True


# --------------------------------------------------------------------------
# 1.  cell decomposition, orbit accumulation
# --------------------------------------------------------------------------


def cells_for_shell(q, d):
    """C1 = A cap B, C2 = A \\ B, C3 = B \\ A, C4 = rest.  j excluded."""
    A = list(range(q + 1))
    others = list(range(q + 1, 2 * q + 1))
    C1 = A[: q + 1 - d]
    C2 = A[q + 1 - d:]
    C3 = others[:d]
    C4 = others[d:]
    return [C1, C2, C3, C4]


def alt_classes(cells, q):
    """Alternative labels A' up to the cell symmetry: profiles (k1..k4)."""
    sizes = [len(c) for c in cells]
    out = []
    for k1 in range(sizes[0] + 1):
        for k2 in range(sizes[1] + 1):
            for k3 in range(sizes[2] + 1):
                k4 = q + 1 - k1 - k2 - k3
                if 0 <= k4 <= sizes[3]:
                    out.append((k1, k2, k3, k4))
    return out


def accumulate(q, d, mu_free=True):
    """Integer orbit accumulators, independent of mu.

    For measurement e and alternative profile k:
       D_e(mu) = actualMean(A,mu,e) - meanOffset(A',e) = P_e + Q_e*mu
       s_e     = meanSlope(A',e)
    Returns  orbits (list of keys), and per class a dict
       key -> (count, sPP, sPQ, sQQ, sPs, sQs, sss)  (integers).
    """
    V = list(range(2 * q + 2))
    j = 2 * q + 1
    A = frozenset(range(q + 1))
    cells = cells_for_shell(q, d)
    cell_of = {}
    for ci, c in enumerate(cells):
        for i in c:
            cell_of[i] = ci
    cell_of[j] = 4
    E = legal_measurements(V, j, q)
    # orbit key of each measurement
    keys = []
    for e in E:
        if e[0] == "s":
            keys.append(("s", cell_of[e[1]]))
        else:
            g = [0, 0, 0, 0]
            for i in e[1]:
                g[cell_of[i]] += 1
            keys.append(("q", tuple(g), e[2]))
    orbit_index = {}
    for k in keys:
        if k not in orbit_index:
            orbit_index[k] = len(orbit_index)
    norb = len(orbit_index)
    # true-world affine data
    trueOS = [mean_affine(A, j, e, V) for e in E]
    res = {}
    for prof in alt_classes(cells, q):
        Ap = frozenset(sum([cells[t][: prof[t]] for t in range(4)], []))
        acc = [[0] * 7 for _ in range(norb)]
        for idx, e in enumerate(E):
            offA, slA = trueOS[idx]
            offB, slB = mean_affine(Ap, j, e, V)
            P = offA - offB
            Q = slA
            s = slB
            a = acc[orbit_index[keys[idx]]]
            a[0] += 1
            a[1] += P * P
            a[2] += P * Q
            a[3] += Q * Q
            a[4] += P * s
            a[5] += Q * s
            a[6] += s * s
        res[prof] = acc
    return orbit_index, res, E, keys


# --------------------------------------------------------------------------
# 2.  exact simplex and matrix-game value
# --------------------------------------------------------------------------


def simplex_max(N, b, c):
    """max c^T y s.t. N y <= b, y >= 0, b >= 0.  Exact, Bland's rule."""
    m = len(N)
    n = len(N[0])
    T = [list(N[i]) + [Fr(1) if k == i else Fr(0) for k in range(m)] + [b[i]]
         for i in range(m)]
    z = [-ci for ci in c] + [Fr(0)] * m + [Fr(0)]
    basis = [n + i for i in range(m)]
    for _ in range(200000):
        piv = -1
        for jj in range(n + m):
            if z[jj] < 0:
                piv = jj
                break
        if piv < 0:
            duals = [z[n + i] for i in range(m)]
            return z[-1], duals
        r = -1
        best = None
        for i in range(m):
            if T[i][piv] > 0:
                ratio = T[i][-1] / T[i][piv]
                if best is None or ratio < best or (ratio == best and basis[i] < basis[r]):
                    best = ratio
                    r = i
        if r < 0:
            raise AssertionError("unbounded LP -- game value would be 0")
        pv = T[r][piv]
        T[r] = [v / pv for v in T[r]]
        for i in range(m):
            if i != r and T[i][piv] != 0:
                f = T[i][piv]
                T[i] = [T[i][k] - f * T[r][k] for k in range(n + m + 1)]
        if z[piv] != 0:
            f = z[piv]
            z = [z[k] - f * T[r][k] for k in range(n + m + 1)]
        basis[r] = piv
    raise AssertionError("simplex iteration cap")


def game_value(M):
    """max_w min_k (M w)_k, w in simplex.  M >= 0, rows = minimiser."""
    K = len(M)
    O = len(M[0])
    for row in M:
        if all(v == 0 for v in row):
            return Fr(0), [Fr(0)] * O
    N = [[M[k][o] for k in range(K)] for o in range(O)]
    obj, duals = simplex_max(N, [Fr(1)] * O, [Fr(1)] * K)
    if obj <= 0:
        raise AssertionError("nonpositive LP objective with no zero row")
    v = 1 / obj
    w = [u * v for u in duals]
    if any(x < 0 for x in w) or sum(w) != 1:
        raise AssertionError(f"invalid w: sum={sum(w)}")
    if min(sum(M[k][o] * w[o] for o in range(O)) for k in range(K)) != v:
        raise AssertionError("game value does not match its own w")
    return v, w


def selftest_game():
    # rock-paper-scissors shifted to be nonnegative: value 1
    M = [[Fr(1), Fr(0), Fr(2)], [Fr(2), Fr(1), Fr(0)], [Fr(0), Fr(2), Fr(1)]]
    v, w = game_value(M)
    if v != 1 or w != [Fr(1, 3)] * 3:
        raise AssertionError(f"simplex self-test failed: v={v} w={w}")
    # a degenerate game with a dominant column
    M2 = [[Fr(3), Fr(1)], [Fr(3), Fr(0)]]
    v2, _ = game_value(M2)
    if v2 != 3:
        raise AssertionError(f"simplex self-test 2 failed: v={v2}")
    print("   simplex/game self-test OK (RPS value 1, dominance value 3)")


# --------------------------------------------------------------------------
# 3.  Gamma for one answer shell
# --------------------------------------------------------------------------


def quad_min(C, Z, Vv, cmax):
    """min over x in [0,cmax] of (C - 2Zx + Vv x^2)/2; returns (x*, value).

    Generalises CIGAMF.P13.QuadraticIntervalMinimum.minimizer, whose upper
    endpoint is hard-wired to 1.  Here the endpoint depends on the alternative's
    exchange distance, which is precisely why the existing Lean evaluator does
    not cover the eps > 0 case.
    """
    if Vv == 0:
        x = cmax if Z >= 0 else Fr(0)
    else:
        x = Z / Vv
        if x < 0:
            x = Fr(0)
        elif x > cmax:
            x = cmax
    return x, (C - 2 * Z * x + Vv * x * x) / 2


REL_TOL = Fr(1, 10 ** 12)
MAXIT = 160


def game_data(q, d, mu, eps, acc_cache, shrink=None):
    """The (class, exchange distance, nu-cap) data of the shell game.

    Two (mu,eps) cells with identical data define literally the same game, so
    their values are equal without solving anything.  Used for the eps <= 1/2
    equality claim, which is therefore exact and not a numerical coincidence.
    """
    if (q, d) not in acc_cache:
        acc_cache[(q, d)] = accumulate(q, d)
    _oi, res, _E, _k = acc_cache[(q, d)]
    out = []
    for prof in sorted(res):
        dp = prof[1] + prof[3]
        if Fr(dp) <= eps:
            continue
        cmax = min(Fr(1), 2 - 2 * eps / dp)
        if shrink is not None:
            cmax = max(Fr(0), cmax - shrink)
        out.append((prof, dp, cmax))
    return out


def shell_gamma(q, d, mu, eps, acc_cache, shrink=None):
    """sup_w inf_{bad} for the answer shell |A \\ B| = d, as a RIGOROUS BRACKET.

    The optimum is in general irrational (at q=3, mu=1/2 the least favourable
    nuisance is 2*sqrt(3)-3), so no finite rational cutting-plane run can end in
    exact equality.  What is returned is a two-sided certificate:
        lo = the exact best-response value at the returned w   (attained, so
             Gamma >= lo),
        hi = the LP value over the generated finite subset of alternatives
             (a relaxation, so Gamma <= hi).
    nu ranges over the CLOSURE of the bad nu-set; shrink=delta instead uses
    [0, cmax-delta], an inner approximation of the open (strict) set, which is
    the trap-(c) control.
    Returns dict(lo, hi, w, cert) or None if the bad set is empty.
    """
    if (q, d) not in acc_cache:
        acc_cache[(q, d)] = accumulate(q, d)
    orbit_index, res, E, keys = acc_cache[(q, d)]
    norb = len(orbit_index)
    # orbit sizes
    sizes = [0] * norb
    for k in keys:
        sizes[orbit_index[k]] += 1

    cls = []
    for prof, acc in res.items():
        dp = prof[1] + prof[3]          # |A' \ B| = |A' cap (A\B)| + |A' cap rest|
        if Fr(dp) <= eps:               # never bad: no legal nu makes it bad
            continue
        cmax = min(Fr(1), 2 - 2 * eps / dp)
        if shrink is not None:
            cmax = max(Fr(0), cmax - shrink)
        # per-orbit averaged (D^2, D s, s^2) at this mu
        co = []
        for o in range(norb):
            cnt, sPP, sPQ, sQQ, sPs, sQs, sss = acc[o]
            n = Fr(cnt)
            avgD2 = (Fr(sPP) + 2 * mu * Fr(sPQ) + mu * mu * Fr(sQQ)) / n
            avgDs = (Fr(sPs) + mu * Fr(sQs)) / n
            avgS2 = Fr(sss) / n
            co.append((avgD2, avgDs, avgS2))
        cls.append((prof, dp, cmax, co))
    if not cls:
        return None

    def row(ci, nu):
        co = cls[ci][3]
        r = [(a - 2 * nu * b + nu * nu * c) / 2 for (a, b, c) in co]
        if any(v < 0 for v in r):
            raise AssertionError("negative KL row -- averaging bug")
        return r

    cons = []
    seen = set()
    for ci, (_p, _dp, cmax, _co) in enumerate(cls):
        for nu in (Fr(0), cmax / 2, cmax):
            if (ci, nu) not in seen:
                seen.add((ci, nu))
                cons.append((ci, nu))
    best = None
    v = None
    for it in range(MAXIT):
        M = [row(ci, nu) for (ci, nu) in cons]
        v, w = game_value(M)
        best = None
        adds = []
        for ci, (_p, _dp, cmax, co) in enumerate(cls):
            C = sum(w[o] * co[o][0] for o in range(norb))
            Z = sum(w[o] * co[o][1] for o in range(norb))
            Vv = sum(w[o] * co[o][2] for o in range(norb))
            x, val = quad_min(C, Z, Vv, cmax)
            if best is None or val < best[0]:
                best = (val, ci, x)
            adds.append((ci, x, val))
        if best[0] > v:
            raise AssertionError("best response above LP value -- solver bug")
        if v - best[0] <= REL_TOL * v:
            cert = {"iterations": it + 1, "constraints": len(cons),
                    "exact": best[0] == v,
                    "rel_gap": float((v - best[0]) / v) if v > 0 else 0.0,
                    "binding_class": cls[best[1]][0],
                    "binding_d_prime": cls[best[1]][1],
                    "binding_nu": float(best[2]),
                    "binding_at_upper_endpoint": best[2] == cls[best[1]][2]}
            return {"lo": best[0], "hi": v, "w": w, "cert": cert}
        added = 0
        for ci, x, val in adds:
            if val < v and (ci, x) not in seen:
                seen.add((ci, x))
                cons.append((ci, x))
                added += 1
        if added == 0:
            raise AssertionError(
                f"stalled: LP={float(v)} best response={float(best[0])}, "
                f"no new cut (q={q} d={d} mu={mu} eps={eps})")
    raise AssertionError(
        f"no certificate after {MAXIT} cuts (q={q} d={d} mu={mu} eps={eps}); "
        f"bracket [{float(best[0])},{float(v)}]")


def gamma_eps(q, mu, eps, acc_cache, **kw):
    """max over answer shells d in Ball_eps of the shell value."""
    out = {}
    for d in range(0, q + 1):
        if (2 - mu) * d > 2 * eps:
            continue                      # B not eps-good
        r = shell_gamma(q, d, mu, eps, acc_cache, **kw)
        if r is None:
            out[d] = None                 # empty bad set for this answer
        else:
            out[d] = r
    live = {d: r for d, r in out.items() if r is not None}
    if not live:
        return None, out
    dstar = max(live, key=lambda d: live[d][0])
    return (live[dstar][0], dstar), out


# --------------------------------------------------------------------------
# PART B.  the two reductions are CHECKED, not assumed
# --------------------------------------------------------------------------


def part_B():
    print()
    print("=" * 74)
    print("B. symmetry reduction control (class invariance + orbit averaging)")
    print("=" * 74)
    q = 3
    V = list(range(2 * q + 2))
    j = 2 * q + 1
    A = frozenset(range(q + 1))
    E = legal_measurements(V, j, q)
    mu = Fr(1, 2)
    nu = Fr(1, 3)
    for d in (0, 1, 2):
        cells = cells_for_shell(q, d)
        cell_of = {}
        for ci, c in enumerate(cells):
            for i in c:
                cell_of[i] = ci
        cell_of[j] = 4
        # cell-symmetric w: uniform inside each orbit, orbit weights arbitrary
        keys = []
        for e in E:
            if e[0] == "s":
                keys.append(("s", cell_of[e[1]]))
            else:
                g = [0, 0, 0, 0]
                for i in e[1]:
                    g[cell_of[i]] += 1
                keys.append(("q", tuple(g), e[2]))
        okeys = sorted(set(keys), key=str)
        wt = {k: Fr(1 + (t % 5), 7 + t) for t, k in enumerate(okeys)}
        tot = sum(wt[k] for k in keys)
        w = {id(e): wt[keys[t]] / tot for t, e in enumerate(E)}
        # B1: f(w,A',nu) constant on cell classes
        byclass = {}
        allB = [frozenset(c) for c in combinations([i for i in V if i != j], q + 1)]
        for Ap in allB:
            prof = tuple(len(set(Ap) & set(cells[t])) for t in range(4))
            val = Fr(0)
            for t, e in enumerate(E):
                offA, slA = mean_affine(A, j, e, V)
                offB, slB = mean_affine(Ap, j, e, V)
                dif = (offA + slA * mu) - (offB + slB * nu)
                val += w[id(e)] * dif * dif / 2
            byclass.setdefault(prof, set()).add(val)
        bad = {p: s for p, s in byclass.items() if len(s) > 1}
        if bad:
            raise AssertionError(f"class invariance FAILS at d={d}: {list(bad)[:3]}")
        print(f"   d={d}: {len(byclass)} cell classes, each with a single value "
              f"over all {len(allB)} labels -- invariance holds")
        # B2: orbit-averaged accumulators reproduce the unreduced sum
        orbit_index, res, E2, keys2 = accumulate(q, d)
        norb = len(orbit_index)
        W = [Fr(0)] * norb
        for t, e in enumerate(E):
            W[orbit_index[keys[t]]] += w[id(e)]
        for prof, acc in res.items():
            tot2 = Fr(0)
            for o in range(norb):
                cnt, sPP, sPQ, sQQ, sPs, sQs, sss = acc[o]
                n = Fr(cnt)
                avgD2 = (Fr(sPP) + 2 * mu * Fr(sPQ) + mu * mu * Fr(sQQ)) / n
                avgDs = (Fr(sPs) + mu * Fr(sQs)) / n
                avgS2 = Fr(sss) / n
                tot2 += W[o] * (avgD2 - 2 * nu * avgDs + nu * nu * avgS2) / 2
            want = list(byclass[prof])[0]
            if tot2 != want:
                raise AssertionError(
                    f"orbit averaging FAILS d={d} prof={prof}: {tot2} != {want}")
        print(f"   d={d}: orbit-averaged objective == unreduced objective "
              f"for all {len(res)} classes")
    # B3: negative control -- a NON-symmetric w must break class invariance,
    #     otherwise B1 is a check that can never return False.
    d = 1
    cells = cells_for_shell(q, d)
    w2 = {id(e): (Fr(1) if t == 0 else Fr(0)) for t, e in enumerate(E)}
    byclass = {}
    for Ap in [frozenset(c) for c in combinations([i for i in V if i != j], q + 1)]:
        prof = tuple(len(set(Ap) & set(cells[t])) for t in range(4))
        val = Fr(0)
        for t, e in enumerate(E):
            offA, slA = mean_affine(A, j, e, V)
            offB, slB = mean_affine(Ap, j, e, V)
            dif = (offA + slA * mu) - (offB + slB * nu)
            val += w2[id(e)] * dif * dif / 2
        byclass.setdefault(prof, set()).add(val)
    if not any(len(s) > 1 for s in byclass.values()):
        raise AssertionError(
            "negative control failed: a point-mass w did not break class "
            "invariance, so B1 cannot discriminate")
    print("   negative control: a point-mass w DOES break class invariance "
          "(so B1 is a real check)")


# --------------------------------------------------------------------------
# PART C/D.  Gamma_0 vs Gamma_eps
# --------------------------------------------------------------------------


def fmt(x):
    return f"{float(x):.6f}"


def part_D(records):
    print()
    print("=" * 74)
    print("D. Gamma_0 and Gamma_eps  (exact rational, certificate per cell)")
    print("=" * 74)
    acc = {}
    mus = [Fr(0), Fr(1, 2), Fr(3, 4), Fr(1)]
    for q in (2, 3, 4, 5):
        epss = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1), Fr(5, 4), Fr(3, 2), Fr(2)]
        epss = [e for e in epss if e < q]
        print(f"\n   q={q}   (ground set {2*q+2}, "
              f"{len(legal_measurements(list(range(2*q+2)), 2*q+1, q))} legal measurements)")
        print(f"   {'mu':>6} {'eps':>6} {'Gamma_eps':>11} {'Gamma_0':>11} "
              f"{'ratio':>8} {'d*':>3} {'ball':>5} {'bind nu':>9} {'endpt':>6}")
        for mu in mus:
            g0 = None
            for eps in epss:
                t0 = time.time()
                r, shells = gamma_eps(q, mu, eps, acc)
                if r is None:
                    print(f"   {str(mu):>6} {str(eps):>6}   SKIPPED: bad set empty "
                          f"for every answer in the ball (trap (a))")
                    continue
                val, dstar = r
                if eps == 0:
                    g0 = val
                if g0 is None:
                    raise AssertionError("Gamma_0 missing")
                if val < g0:
                    raise AssertionError(
                        f"Gamma_eps < Gamma_0 at q={q} mu={mu} eps={eps}: "
                        f"{float(val)} < {float(g0)} -- trap (d) violated")
                cert = shells[dstar][2]
                ball = max(shells)
                print(f"   {str(mu):>6} {str(eps):>6} {fmt(val):>11} {fmt(g0):>11} "
                      f"{fmt(val/g0):>8} {dstar:>3} {ball:>5} "
                      f"{cert['binding_nu']:>9} "
                      f"{'yes' if cert['binding_at_upper_endpoint'] else 'no':>6}"
                      f"   [{time.time()-t0:.1f}s]")
                records.append(dict(q=q, mu=str(mu), eps=str(eps),
                                    gamma_eps=str(val), gamma_0=str(g0),
                                    ratio=float(val / g0), d_star=dstar,
                                    ball_radius=ball,
                                    shell_values={str(d): (str(s[0]) if s else None)
                                                  for d, s in shells.items()},
                                    cert=cert))
    return acc


# --------------------------------------------------------------------------
# PART E.  the claims, each as an assertion
# --------------------------------------------------------------------------


def part_E(acc, records):
    print()
    print("=" * 74)
    print("E. claim checks")
    print("=" * 74)
    # E1 -- structural: for eps <= 1/2 the bad set at B=A is the FULL admissible
    # set and every other answer in the ball has value 0, so Gamma_eps = Gamma_0.
    n_eq = 0
    for rec in records:
        if Fr(rec["eps"]) <= Fr(1, 2):
            if Fr(rec["gamma_eps"]) != Fr(rec["gamma_0"]):
                raise AssertionError(
                    f"E1 FAILS: eps={rec['eps']} q={rec['q']} mu={rec['mu']} "
                    f"Gamma_eps={rec['gamma_eps']} != Gamma_0={rec['gamma_0']}")
            n_eq += 1
    print(f"   E1: Gamma_eps == Gamma_0 in all {n_eq} computed cells with "
          f"eps <= 1/2 (exact rational equality)")
    # E1b -- the structural reason, checked directly: for eps <= 1/2 every
    # (A',nu) with A' != A is bad for B = A.
    for q in (2, 3, 4, 5):
        for dp in range(1, q + 1):
            for eps in (Fr(0), Fr(1, 4), Fr(1, 2)):
                cl = min(Fr(1), 2 - 2 * eps / dp)
                if cl != 1:
                    raise AssertionError(
                        f"E1b FAILS: nu-cap {cl} < 1 at eps={eps} d'={dp}")
    print("   E1b: for eps <= 1/2 the nu-cap min(1, 2-2eps/d') equals 1 for every "
          "d' >= 1, i.e. NO alternative is removed")
    # E1c -- sharpness of 1/2: the cap drops below 1 as soon as eps > 1/2
    for eps in (Fr(51, 100), Fr(3, 4), Fr(1)):
        if min(Fr(1), 2 - 2 * eps / 1) >= 1:
            raise AssertionError("E1c FAILS: cap did not drop past eps=1/2")
    print("   E1c: the d'=1 cap drops strictly below 1 for every eps > 1/2 "
          "(threshold is sharp at 1/2)")
    # E2 -- trap (c): strict vs closed boundary.  Inner approximations of the
    # OPEN bad set must converge to the closed value.
    print("   E2 (trap c): open-set inner approximation vs closed value")
    q, mu, eps = 3, Fr(1, 2), Fr(5, 4)
    base = shell_gamma(q, 0, mu, eps, acc)[0]
    prev = None
    for k in (1, 2, 3, 4):
        delta = Fr(1, 10 ** k)
        v = shell_gamma(q, 0, mu, eps, acc, shrink=delta)[0]
        gap = base - v
        if gap < 0:
            raise AssertionError("shrunken feasible set gave a LARGER inf")
        if prev is not None and gap > prev:
            raise AssertionError("inner approximation not monotone in delta")
        prev = gap
        print(f"      delta=1e-{k}: closed={fmt(base)} open-inner={fmt(v)} "
              f"gap={float(gap):.3e}")
    if prev > Fr(1, 10 ** 6):
        raise AssertionError(
            f"open/closed gap {float(prev)} does not vanish -- the strict "
            f"boundary cannot be replaced by its closure here")
    print("      -> inf over the strict (open) bad set == min over its closure")
    # E3 -- analytic upper bound for answers off the centre of the ball.
    # For an answer at shell d with d > eps, the true label A itself is a bad
    # alternative at nu -> 2-2eps/d, so the shell value is at most
    #      q^2 * (mu - (2-2eps/d))^2 / 2      (meanSlope^2 <= q^2).
    print("   E3: analytic bound  Gamma(shell d) <= q^2 (mu-(2-2eps/d))^2/2")
    nchecked = 0
    for rec in records:
        q = rec["q"]
        mu = Fr(rec["mu"])
        eps = Fr(rec["eps"])
        for ds, vs in rec["shell_values"].items():
            d = int(ds)
            if d == 0 or vs is None:
                continue
            if Fr(d) <= eps:
                continue
            nuc = 2 - 2 * eps / d
            bound = Fr(q) ** 2 * (mu - nuc) ** 2 / 2
            if Fr(vs) > bound:
                raise AssertionError(
                    f"E3 FAILS q={q} mu={mu} eps={eps} d={d}: "
                    f"{float(Fr(vs))} > {float(bound)}")
            nchecked += 1
    print(f"      holds in all {nchecked} off-centre shells checked")
    # E4 -- monotonicity in eps (a genuinely falsifiable consequence of the
    # bad set shrinking as eps grows)
    seen = {}
    for rec in records:
        key = (rec["q"], rec["mu"])
        seen.setdefault(key, []).append((Fr(rec["eps"]), Fr(rec["gamma_eps"])))
    for key, lst in seen.items():
        lst.sort()
        for a, b in zip(lst, lst[1:]):
            if b[1] < a[1]:
                raise AssertionError(
                    f"E4 FAILS: Gamma decreased with eps at {key}: {a} -> {b}")
    print(f"   E4: Gamma_eps nondecreasing in eps in all {len(seen)} (q,mu) rows")
    # E5 -- the honest question: is the inequality ever STRICT?
    strict = [r for r in records if Fr(r["gamma_eps"]) > Fr(r["gamma_0"])]
    print(f"   E5: cells with Gamma_eps STRICTLY > Gamma_0: {len(strict)} of "
          f"{len(records)}")
    if strict:
        best = max(strict, key=lambda r: r["ratio"])
        print(f"      largest ratio {best['ratio']:.4f} at q={best['q']} "
              f"mu={best['mu']} eps={best['eps']} (answer shell d*={best['d_star']})")
        smallest = min(Fr(r["eps"]) for r in strict)
        print(f"      smallest eps with a strict gain: {smallest}")
    else:
        print("      NEGATIVE RESULT: no strict gain anywhere on this grid.")


# --------------------------------------------------------------------------
# PART F.  normalised tolerance with growing q
# --------------------------------------------------------------------------


def part_F(acc, records):
    print()
    print("=" * 74)
    print("F. normalised tolerance eps = c*(q+1), growing q")
    print("=" * 74)
    print("   trap (a) bound: the bad set is empty once eps >= q, i.e. "
          "c >= q/(q+1).")
    rows = []
    for c in (Fr(1, 8), Fr(1, 4), Fr(1, 2)):
        print(f"\n   c={c}")
        print(f"   {'q':>3} {'eps':>7} {'mu':>5} {'Gamma_eps':>11} {'Gamma_0':>11} "
              f"{'ratio':>9} {'d*':>3} {'ball':>5}")
        for q in (2, 3, 4, 5):
            eps = c * (q + 1)
            if eps >= q:
                print(f"   {q:>3} {str(eps):>7}   SKIPPED: eps >= q, bad set empty "
                      f"for every answer (trap (a))")
                continue
            for mu in (Fr(1, 2), Fr(1)):
                r, shells = gamma_eps(q, mu, eps, acc)
                g0, _ = gamma_eps(q, mu, Fr(0), acc)
                val, dstar = r
                ball = max(shells)
                print(f"   {q:>3} {str(eps):>7} {str(mu):>5} {fmt(val):>11} "
                      f"{fmt(g0[0]):>11} {fmt(val/g0[0]):>9} {dstar:>3} {ball:>5}")
                rows.append(dict(c=str(c), q=q, eps=str(eps), mu=str(mu),
                                 gamma_eps=str(val), gamma_0=str(g0[0]),
                                 ratio=float(val / g0[0]), d_star=dstar,
                                 ball_radius=ball))
    records.extend([dict(normalised=True, **r) for r in rows])
    if rows:
        rs = [r["ratio"] for r in rows]
        print(f"\n   ratio range over the normalised grid: "
              f"[{min(rs):.4f}, {max(rs):.4f}]")
        # growth control: does the ratio grow with q at fixed c?
        for c in sorted({r["c"] for r in rows}):
            for mu in sorted({r["mu"] for r in rows}):
                seq = [(r["q"], r["ratio"]) for r in rows
                       if r["c"] == c and r["mu"] == mu]
                seq.sort()
                if len(seq) >= 2:
                    print(f"      c={c} mu={mu}: ratio by q = "
                          + ", ".join(f"q={a}:{b:.3f}" for a, b in seq))


def main():
    t0 = time.time()
    records = []
    part_A()
    selftest_game()
    part_B()
    acc = part_D(records)
    part_E(acc, records)
    part_F(acc, records)
    with open(OUT, "w") as f:
        json.dump({"records": records,
                   "generated": "N4_epsilon_answer_information.py"}, f, indent=1)
    print(f"\nwrote {OUT}")
    print(f"elapsed {time.time()-t0:.1f}s")


if __name__ == "__main__":
    main()
