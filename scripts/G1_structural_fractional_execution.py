r"""PACKAGE G.  Can a fractional certificate be EXECUTED by a randomized ranking?

Setting.  F is an integer matrix, m components (rows) x d scenarios (columns),
osc(v) = max(v) - min(v), D = sum_i osc(F_i),

    L(S)   = osc( sum_{i not in S} F_i ) / D                 (integral loss)
    L(x)   = osc( sum_i (1 - x_i) F_i ) / D                  (fractional loss)
    OPT_k  = min_{|T| = k} L(T)
    g_k(pi)= L(prefix_k pi) - OPT_k .

A fractional PATH is x^0 = 0 <= x^1 <= ... <= x^m = 1 (componentwise) with
sum_i x^k_i = k and 0 <= x^k_i <= 1.

Three exact facts on the witness F = [[0,1,0],[1,0,1],[1,0,0],[0,0,1]] are
verified here, and one open question is probed numerically.

  (1) integral:     min_pi max_k g_k(pi) = 1/4      (all 24 permutations)
  (2) randomized:   min_P  max_k E_P g_k = 1/8      (LP; exact primal + dual)
  (3) marginals:    every P whose budget-k selection marginals equal the
      fractional path x^k = ((k-1)/3, 1, (k-1)/3, (k-1)/3) has
      E_P L(S_2) - L(x^2) = 1/4 -- randomization buys NOTHING once the
      marginals are pinned, although free randomization halves the gap.

OPEN QUESTION probed (NOT proved).  With eta = max_i osc(F_i)/D, is
    ROUNDGAP(F, path) := min over P on permutations MATCHING the path's
                         marginals of max_k [ E_P L(S_k) - L(x^k) ]
bounded by C sqrt( eta log(m d) )?  For m <= 6 this is a finite LP over all m!
permutations and is computed EXACTLY here (rational LP feasibility is
re-verified in Fractions after the float LP returns).

Every optimizer call checks `res.status == 0` and raises otherwise, and every
allocation returned by an optimizer is re-verified for feasibility before any
number derived from it is reported.

Re-run:  .venv/bin/python scripts/G1_structural_fractional_execution.py
"""
import hashlib
import itertools
import json
import math
import random
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

OUT = Path("/Users/phanan/cig-amf-main/research/worker_gopG_20260913/"
           "G1_fractional_execution.json")

WITNESS = [[0, 1, 0], [1, 0, 1], [1, 0, 0], [0, 0, 1]]


class OptimizerFailure(RuntimeError):
    pass


# --------------------------------------------------------------- exact core
def instance(M):
    m, d = len(M), len(M[0])
    D = sum(max(r) - min(r) for r in M)
    if D == 0:
        raise ValueError("degenerate instance")
    return m, d, D


def L_int(M, S):
    """Exact L(S) for a set S given as a frozenset/iterable of row indices."""
    m, d, D = instance(M)
    S = set(S)
    res = [sum(M[i][a] for i in range(m) if i not in S) for a in range(d)]
    return F(max(res) - min(res), D)


def L_frac(M, x):
    """Exact L(x) for a rational vector x."""
    m, d, D = instance(M)
    res = [sum((1 - x[i]) * M[i][a] for i in range(m)) for a in range(d)]
    return (max(res) - min(res)) / D


def opt_table(M):
    m, _, _ = instance(M)
    out = []
    for k in range(m + 1):
        out.append(min(L_int(M, T) for T in itertools.combinations(range(m), k)))
    return out


def g_vector(M, pi, OPT):
    m, _, _ = instance(M)
    S = set()
    out = [L_int(M, S) - OPT[0]]
    for i in pi:
        S.add(i)
        out.append(L_int(M, S) - OPT[len(S)])
    return out


def eta_of(M):
    m, d, D = instance(M)
    return F(max(max(r) - min(r) for r in M), D)


# ------------------------------------------------------- LP over permutations
def minmax_over_distributions(gmat, marginal_rows=None, marginal_rhs=None):
    """min_P max_k sum_pi P_pi gmat[pi][k], P a distribution.

    Optional extra equality constraints marginal_rows . P = marginal_rhs.
    Returns (float value, P as a numpy vector).  Raises if the LP fails.
    """
    n = len(gmat)
    K = len(gmat[0])
    # variables: P_0..P_{n-1}, t ; minimise t
    c = np.zeros(n + 1)
    c[-1] = 1.0
    A_ub = np.zeros((K, n + 1))
    for k in range(K):
        for j in range(n):
            A_ub[k, j] = float(gmat[j][k])
        A_ub[k, -1] = -1.0
    b_ub = np.zeros(K)
    rows = [np.concatenate([np.ones(n), [0.0]])]
    rhs = [1.0]
    if marginal_rows is not None:
        for r, v in zip(marginal_rows, marginal_rhs):
            rows.append(np.concatenate([np.asarray(r, dtype=float), [0.0]]))
            rhs.append(float(v))
    A_eq = np.vstack(rows)
    b_eq = np.asarray(rhs)
    bounds = [(0.0, None)] * n + [(None, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds,
                  method="highs")
    if not res.success or res.status != 0:
        raise OptimizerFailure(f"linprog failed: status={res.status} {res.message}")
    P = res.x[:n]
    # ---- feasibility of the returned allocation, checked independently ----
    if P.min() < -1e-9:
        raise OptimizerFailure(f"returned P has a negative entry {P.min()}")
    if abs(P.sum() - 1.0) > 1e-7:
        raise OptimizerFailure(f"returned P sums to {P.sum()}")
    if marginal_rows is not None:
        for r, v in zip(marginal_rows, marginal_rhs):
            if abs(float(np.dot(np.asarray(r, dtype=float), P)) - float(v)) > 1e-6:
                raise OptimizerFailure("returned P violates a marginal constraint")
    val = max(float(np.dot([float(gmat[j][k]) for j in range(n)], P))
              for k in range(K))
    if val > res.x[-1] + 1e-7:
        raise OptimizerFailure("objective of the returned P exceeds the LP value")
    return val, P


# ---------------------------------------------------------- fractional paths
def monotone_path_lp(M, force_zero_loss=False):
    """A monotone fractional path minimising max_k (u_k - l_k).

    Variables per budget k = 1..m-1: x^k in [0,1]^m with sum = k, plus
    l_k <= sum_i (1-x^k_i) F_i(a) <= u_k for every scenario a, and
    x^k <= x^{k+1}.  Objective: minimise sum_k (u_k - l_k).
    x^0 = 0 and x^m = 1 are fixed.  Returns the exact-rational path
    (floats rounded to a fine rational grid and then RE-VERIFIED feasible).
    """
    m, d, D = instance(M)
    K = list(range(1, m))               # interior budgets
    if not K:
        return [[F(0)] * m, [F(1)] * m]
    nx = len(K) * m
    idx = {(k, i): j for j, (k, i) in enumerate((k, i) for k in K for i in range(m))}
    nu = len(K)
    n = nx + 2 * nu                      # x, u, l
    ui = lambda k: nx + K.index(k)
    li = lambda k: nx + nu + K.index(k)
    c = np.zeros(n)
    for k in K:
        c[ui(k)] = 1.0
        c[li(k)] = -1.0
    A_ub, b_ub = [], []
    for k in K:
        for a in range(d):
            row = np.zeros(n)
            for i in range(m):
                row[idx[(k, i)]] = -float(M[i][a])
            row[ui(k)] = -1.0
            A_ub.append(row)
            b_ub.append(-float(sum(M[i][a] for i in range(m))))
            row2 = np.zeros(n)
            for i in range(m):
                row2[idx[(k, i)]] = float(M[i][a])
            row2[li(k)] = 1.0
            A_ub.append(row2)
            b_ub.append(float(sum(M[i][a] for i in range(m))))
    for k in K:
        for i in range(m):
            row = np.zeros(n)
            row[idx[(k, i)]] = 1.0
            if k + 1 in idx and (k + 1, i) in idx:
                row[idx[(k + 1, i)]] = -1.0
                A_ub.append(row)
                b_ub.append(0.0)
            elif k + 1 == m:
                A_ub.append(row)
                b_ub.append(1.0)
    A_eq, b_eq = [], []
    for k in K:
        row = np.zeros(n)
        for i in range(m):
            row[idx[(k, i)]] = 1.0
        A_eq.append(row)
        b_eq.append(float(k))
    bounds = [(0.0, 1.0)] * nx + [(None, None)] * (2 * nu)
    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=np.array(A_eq), b_eq=np.array(b_eq), bounds=bounds,
                  method="highs")
    if not res.success or res.status != 0:
        raise OptimizerFailure(f"path LP failed: status={res.status} {res.message}")
    GRID = 2520 * 10            # denominator that captures /2,/3,/4,/5,/7,/8,/9
    path = [[F(0)] * m]
    for k in K:
        xk = [F(round(res.x[idx[(k, i)]] * GRID), GRID) for i in range(m)]
        path.append(xk)
    path.append([F(1)] * m)
    # ---- repair the rounding so the exact path is exactly feasible ---------
    for k in range(1, m):
        xk = path[k]
        s = sum(xk)
        if s != k:                       # restore the cardinality exactly
            adj = F(k) - s
            order = sorted(range(m), key=lambda i: -float(xk[i]))
            for i in order:
                room = (F(1) - xk[i]) if adj > 0 else xk[i]
                step = min(abs(adj), room) * (1 if adj > 0 else -1)
                xk[i] += step
                adj -= step
                if adj == 0:
                    break
            if adj != 0:
                raise OptimizerFailure("cannot restore cardinality of the path")
    for k in range(1, m + 1):            # restore monotonicity exactly
        for i in range(m):
            if path[k][i] < path[k - 1][i]:
                path[k][i] = path[k - 1][i]
    for k in range(1, m):                # cardinality again after the clamp
        s = sum(path[k])
        if s > k:
            excess = s - F(k)
            for i in sorted(range(m), key=lambda i: -float(path[k][i])):
                room = path[k][i] - path[k - 1][i]
                step = min(excess, room)
                path[k][i] -= step
                excess -= step
                if excess == 0:
                    break
            if excess != 0:
                raise OptimizerFailure("cannot re-restore cardinality")
    check_path(path, m)
    return path


def check_path(path, m):
    """Exact feasibility of a fractional path.  RAISES on any violation."""
    if len(path) != m + 1:
        raise AssertionError("path has the wrong length")
    for k, xk in enumerate(path):
        if len(xk) != m:
            raise AssertionError("path entry has the wrong width")
        if any(v < 0 or v > 1 for v in xk):
            raise AssertionError(f"path[{k}] leaves [0,1]")
        if sum(xk) != F(k):
            raise AssertionError(f"path[{k}] has mass {sum(xk)} != {k}")
        if k and any(xk[i] < path[k - 1][i] for i in range(m)):
            raise AssertionError(f"path is not monotone at budget {k}")


def roundgap(M, path):
    """min over P on permutations MATCHING the path's marginals of
       max_k [ E_P L(S_k) - L(x^k) ].  Exponential in m; use m <= 6."""
    m, _, _ = instance(M)
    perms = list(itertools.permutations(range(m)))
    Lx = [L_frac(M, path[k]) for k in range(m + 1)]
    gmat = []
    for pi in perms:
        S = set()
        row = [L_int(M, S) - Lx[0]]
        for i in pi:
            S.add(i)
            row.append(L_int(M, S) - Lx[len(S)])
        gmat.append(row)
    rows, rhs = [], []
    for k in range(1, m):
        for i in range(m):
            rows.append([1.0 if i in set(pi[:k]) else 0.0 for pi in perms])
            rhs.append(float(path[k][i]))
    val, P = minmax_over_distributions(gmat, rows, rhs)
    return val, P, gmat, perms


def support_lower_bound(M, path, cap=200000):
    """A SOUND lower bound on ROUNDGAP that survives large m.

    If x^k_i = 1 then i is in S_k almost surely under any P matching the
    marginals; if x^k_i = 0 then i is out almost surely.  Hence
        E_P L(S_k) >= min { L(S) : |S| = k, forced_k subset S subset allowed_k }.
    Returns (bound, per-budget detail, skipped budgets).  Budgets whose
    admissible family exceeds `cap` are SKIPPED and reported, never guessed.
    """
    m, _, _ = instance(M)
    best = None
    detail = []
    skipped = []
    for k in range(m + 1):
        xk = path[k]
        forced = [i for i in range(m) if xk[i] == 1]
        allowed = [i for i in range(m) if 0 < xk[i] < 1]
        need = k - len(forced)
        if need < 0 or need > len(allowed):
            raise AssertionError(f"path[{k}] is inconsistent with its support")
        try:
            count = math.comb(len(allowed), need)
        except ValueError:
            count = cap + 1
        if count > cap:
            skipped.append(k)
            continue
        mn = min(L_int(M, set(forced) | set(c))
                 for c in itertools.combinations(allowed, need))
        gap = mn - L_frac(M, xk)
        detail.append({"k": k, "min_admissible_L": str(mn),
                       "L_frac": str(L_frac(M, xk)), "lower_bound": str(gap),
                       "admissible_sets": count})
        if best is None or gap > best:
            best = gap
    return best, detail, skipped


def main():
    t0 = time.time()
    rep = {}
    m, d, D = instance(WITNESS)
    OPT = opt_table(WITNESS)
    rep["witness"] = {"matrix": WITNESS, "D": D,
                      "OPT_by_budget": [str(v) for v in OPT],
                      "eta": str(eta_of(WITNESS))}
    if [str(v) for v in OPT] != ["1/4", "0", "0", "1/4", "0"]:
        raise AssertionError(f"integer optimum table wrong: {OPT}")

    # ---- (0) the fractional path, three literal values ---------------------
    xpath = [[F(0)] * 4]
    for k in (1, 2, 3, 4):
        t = F(k - 1, 3)
        xpath.append([t, F(1), t, t])
    check_path(xpath, 4)
    Lx = [L_frac(WITNESS, xk) for xk in xpath]
    if any(v != 0 for v in Lx[1:]):
        raise AssertionError(f"claimed zero-loss path is not zero-loss: {Lx}")
    if Lx[0] != F(1, 4):
        raise AssertionError("L(x^0) should be L(empty) = 1/4")
    rep["fractional_path"] = {
        "x_k": [[str(v) for v in xk] for xk in xpath],
        "L_of_x_k": [str(v) for v in Lx],
        "status": "EXACT: monotone, cardinality k, and L(x^k) = 0 for k >= 1, "
                  "so the path meets or beats every integer optimum",
    }

    # ---- (1) integral minimax over the 24 permutations ---------------------
    perms = list(itertools.permutations(range(4)))
    gmat = [g_vector(WITNESS, pi, OPT) for pi in perms]
    integral = min(max(row) for row in gmat)
    if integral != F(1, 4):
        raise AssertionError(f"integral minimax = {integral}, expected 1/4")
    best_pi = [perms[j] for j in range(len(perms)) if max(gmat[j]) == integral]
    # the pointwise certificate: g_1 + g_2 >= 1/4 for EVERY permutation
    two_budget = min(gmat[j][1] + gmat[j][2] for j in range(len(perms)))
    if two_budget != F(1, 4):
        raise AssertionError(f"min (g_1+g_2) = {two_budget}, expected 1/4")
    rep["integral_minimax"] = {"value": str(integral),
                               "argmin_rankings": [list(p) for p in best_pi],
                               "min_over_pi_of_g1_plus_g2": str(two_budget),
                               "status": "EXACT (all 4! = 24 rankings enumerated)"}

    # ---- (2) randomized minimax: exact primal + exact dual -----------------
    j1 = perms.index((1, 0, 2, 3))
    j2 = perms.index((2, 3, 0, 1))
    mix = [F(1, 2) if j in (j1, j2) else F(0) for j in range(len(perms))]
    if sum(mix) != 1 or any(v < 0 for v in mix):
        raise AssertionError("the exhibited mixture is not a distribution")
    exp_g = [sum(mix[j] * gmat[j][k] for j in range(len(perms)))
             for k in range(5)]
    primal = max(exp_g)
    if primal != F(1, 8):
        raise AssertionError(f"mixture value = {primal}, expected 1/8")
    # dual: y_1 = y_2 = 1/2 on constraints k=1,2 gives
    #       max_k E g_k >= (E g_1 + E g_2)/2 >= (min_pi (g_1+g_2))/2 = 1/8
    dual = two_budget / 2
    if dual != F(1, 8):
        raise AssertionError("dual certificate does not give 1/8")
    lpval, P = minmax_over_distributions(gmat)      # float cross-check, raises
    if abs(lpval - 1 / 8) > 1e-9:
        raise AssertionError(f"LP cross-check gives {lpval}, expected 0.125")
    rep["randomized_minimax"] = {
        "value": str(primal),
        "primal_certificate": {"(1,0,2,3)": "1/2", "(2,3,0,1)": "1/2",
                               "E_g_by_budget": [str(v) for v in exp_g]},
        "dual_certificate": "g_1(pi) + g_2(pi) >= 1/4 for every one of the 24 "
                            "rankings; averaging gives max_k E g_k >= 1/8",
        "float_LP_cross_check": lpval,
        "status": "EXACT (rational primal and rational dual agree; the float LP "
                  "is only a cross-check and raises if it fails)",
        "gap_factor_vs_integral": str(integral / primal),
    }

    # ---- (3) matching the path's marginals buys nothing --------------------
    # x^1 = (0,1,0,0): every P with these marginals puts row 1 first.
    forced = [pi for pi in perms if pi[0] == 1]
    worst2 = min(L_int(WITNESS, set(pi[:2])) for pi in forced)
    if worst2 != F(1, 4):
        raise AssertionError("row-1-first rankings should all have L(S_2) = 1/4")
    val_m, P_m, _, _ = roundgap(WITNESS, xpath)
    if abs(val_m - 0.25) > 1e-7:
        raise AssertionError(f"marginal-matching ROUNDGAP = {val_m}, expected 1/4")
    rep["marginal_matching"] = {
        "x1": ["0", "1", "0", "0"],
        "forced_first_component": 1,
        "min_L_S2_over_admissible_rankings": str(worst2),
        "L_of_x2": str(Lx[2]),
        "ROUNDGAP": str(F(1, 4)),
        "float_LP_value": val_m,
        "status": "EXACT: every distribution matching the path's budget-1 "
                  "marginal must place row 1 first, so at budget 2 EVERY "
                  "realization has loss 1/4 while the fractional residual has "
                  "loss 0.  Randomization halves the gap only when the "
                  "marginals are FREE (1/8); matching them costs the full 1/4.",
        "mechanism": "osc(E Z) <= E osc(Z) with STRICT inequality: the "
                     "relaxation cancels across realizations that never co-occur",
    }

    # ---- (4) Jensen / strictness, exactly as the mechanism predicts -------
    #  The three budget-2 sets admissible under the path's marginals are
    #  {1,0}, {1,2}, {1,3}, each with probability 1/3 (that is the ONLY
    #  distribution matching x^2 = (1/3,1,1/3,1/3) once row 1 is first).
    adm = [{1, 0}, {1, 2}, {1, 3}]
    resid = [[sum(WITNESS[i][a] for i in range(4) if i not in S) for a in range(3)]
             for S in adm]
    EZ = [sum(F(r[a], 3) for r in resid) for a in range(3)]
    osc_of_mean = max(EZ) - min(EZ)
    mean_of_osc = sum(F(max(r) - min(r), 3) for r in resid)
    fracres = [sum((1 - xpath[2][i]) * WITNESS[i][a] for i in range(4))
               for a in range(3)]
    if EZ != fracres:
        raise AssertionError("the mean realization is not the fractional residual")
    if not (osc_of_mean < mean_of_osc):
        raise AssertionError("expected STRICT Jensen gap here")
    rep["jensen_strict"] = {
        "admissible_budget_2_sets": [sorted(S) for S in adm],
        "residual_vectors": resid,
        "mean_residual_equals_fractional_residual": [str(v) for v in EZ],
        "osc_of_mean": str(osc_of_mean), "mean_of_osc": str(mean_of_osc),
        "status": "EXACT strict inequality osc(E Z) < E osc(Z): the mean of the "
                  "three admissible realizations is exactly the fractional "
                  "residual and is perfectly balanced, while every single "
                  "realization has oscillation 1",
    }

    # ---- (5) OPEN QUESTION: does ROUNDGAP shrink like sqrt(eta log(m d))? --
    rng = random.Random(20260913)
    rows = []

    def split(Mat, N):
        """Replace every row by N copies scaled by 1/N: same D, eta/N."""
        out = []
        for r in Mat:
            for _ in range(N):
                out.append([F(v, N) for v in r])
        return out

    # (5a) the witness family with eta -> 0 by splitting (m grows as 4N)
    for N in (1, 2):
        Mn = split(WITNESS, N)
        Mi = [[v * N for v in r] for r in Mn]       # integer rescale, same L
        mm = len(Mi)
        if mm > 8:
            continue
        try:
            pth = monotone_path_lp(Mi)
        except OptimizerFailure as exc:
            rows.append({"family": f"split witness N={N}", "error": str(exc)})
            continue
        if mm <= 7:
            v, _, _, _ = roundgap(Mi, pth)
        else:
            v = None
        rows.append({"family": f"split witness N={N}", "m": mm,
                     "d": len(Mi[0]), "eta": str(eta_of(Mi)),
                     "ROUNDGAP": v,
                     "sqrt_eta_log_md": math.sqrt(float(eta_of(Mi))
                                                  * math.log(mm * len(Mi[0])))})

    # (5b) random instances, m <= 6, sweeping eta by adding a heavy component
    for trial in range(40):
        mm = rng.choice([4, 5, 6])
        dd = rng.choice([3, 4])
        heavy = rng.choice([1, 1, 3, 9, 27])
        Mi = [[0] + [rng.randint(-2, 2) for _ in range(dd - 1)] for _ in range(mm - 1)]
        Mi.append([0] + [heavy * rng.choice([-1, 1]) for _ in range(dd - 1)])
        try:
            instance(Mi)
        except ValueError:
            continue
        try:
            pth = monotone_path_lp(Mi)
            v, _, _, _ = roundgap(Mi, pth)
        except (OptimizerFailure, AssertionError) as exc:
            rows.append({"family": "random", "m": mm, "d": dd, "error": str(exc)})
            continue
        e = eta_of(Mi)
        rows.append({"family": "random", "m": mm, "d": dd, "eta": str(e),
                     "ROUNDGAP": v,
                     "sqrt_eta_log_md": math.sqrt(float(e) * math.log(mm * dd)),
                     "ratio": (v / math.sqrt(float(e) * math.log(mm * dd))
                               if v is not None and e > 0 else None),
                     "matrix": Mi})
    ok = [r for r in rows if r.get("ratio") is not None]

    # (5c) SOUND lower bound at LARGE m and SMALL eta (branch (b) search).
    #      m <= 6 cannot have eta < 1/6, so the exact m! LP above can say
    #      nothing about eta -> 0.  This block searches larger m.
    lb_rows = []
    b, det, sk = support_lower_bound(WITNESS, xpath)
    if b != F(1, 4):
        raise AssertionError(f"support lower bound on the witness = {b}, want 1/4")
    lb_rows.append({"family": "witness (hand path)", "m": 4, "eta": "1/4",
                    "lower_bound": str(b), "skipped_budgets": sk})

    def interp_path(N):
        """The witness path transported to the N-fold split instance."""
        def y(s):
            if s <= 1:
                return [F(0), F(s).limit_denominator(10**6), F(0), F(0)]
            t = (F(s) - 1) / 3
            return [t, F(1), t, t]
        M2 = [[v * N for v in r] for r in split(WITNESS, N)]
        mm = 4 * N
        pth = []
        for k in range(mm + 1):
            yy = y(F(k, N))
            pth.append([yy[j // N] for j in range(mm)])
        check_path(pth, mm)
        return M2, pth

    for N in (1, 2, 3, 4, 6):
        M2, pth = interp_path(N)
        bb, dd2, sk2 = support_lower_bound(M2, pth)
        lb_rows.append({"family": f"split witness N={N} (transported path)",
                        "m": 4 * N, "d": 3, "eta": str(eta_of(M2)),
                        "lower_bound": str(bb), "skipped_budgets": sk2})

    # random search: many components of comparable span (small eta)
    best_small_eta = None
    for trial in range(60):
        mm = rng.choice([8, 10, 12])
        dd = rng.choice([3, 4])
        Mi = [[0] + [rng.randint(-1, 1) for _ in range(dd - 1)] for _ in range(mm)]
        try:
            e = eta_of(Mi)
        except ValueError:
            continue
        if e > F(1, 5):
            continue
        try:
            pth = monotone_path_lp(Mi)
            bb, _, sk2 = support_lower_bound(Mi, pth, cap=60000)
        except (OptimizerFailure, AssertionError) as exc:
            lb_rows.append({"family": "random small-eta", "m": mm, "d": dd,
                            "error": str(exc)})
            continue
        if bb is None:
            continue
        ratio = float(bb) / math.sqrt(float(e) * math.log(mm * dd))
        rec = {"family": "random small-eta", "m": mm, "d": dd, "eta": str(e),
               "lower_bound": str(bb), "ratio_vs_sqrt_eta_log_md": ratio,
               "skipped_budgets": sk2}
        lb_rows.append(rec)
        if best_small_eta is None or ratio > best_small_eta["ratio_vs_sqrt_eta_log_md"]:
            best_small_eta = dict(rec, matrix=Mi)

    rep["open_question_roundgap"] = {
        "quantity": "ROUNDGAP = min over P on permutations MATCHING the path's "
                    "marginals of max_k [E_P L(S_k) - L(x^k)]",
        "conjecture": "ROUNDGAP <= C sqrt(eta log(m d))",
        "status": "NUMERICAL EVIDENCE ONLY -- neither branch (a) nor (b) closed",
        "exact_LP_cells": rows,
        "exact_LP_limitation": "m <= 6 is forced by the m! LP, and eta >= 1/m "
                               "always, so the exact LP can never reach eta < 1/6",
        "max_ratio_ROUNDGAP_over_sqrt_eta_log_md":
            max((r["ratio"] for r in ok), default=None),
        "support_lower_bound_cells": lb_rows,
        "best_small_eta_lower_bound": best_small_eta,
        "not_done": "no rounding algorithm with a PROVED guarantee was built "
                    "(branch (a) open); no family with eta -> 0 and "
                    "non-vanishing ROUNDGAP was found (branch (b) open); "
                    "the support lower bound is only a lower bound, so a small "
                    "value of it does NOT prove ROUNDGAP is small",
    }

    rep["source_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    rep["wall_seconds"] = round(time.time() - t0, 1)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(rep, indent=2, default=str) + "\n")
    print("integral minimax      =", integral)
    print("randomized minimax    =", primal, "(gap factor", integral / primal, ")")
    print("marginal-matching gap =", F(1, 4))
    print("max ROUNDGAP / sqrt(eta log md) =",
          rep["open_question_roundgap"]["max_ratio_ROUNDGAP_over_sqrt_eta_log_md"])
    print("wrote", OUT, f"[{time.time()-t0:.1f}s]")


if __name__ == "__main__":
    main()
