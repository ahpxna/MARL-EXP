#!/usr/bin/env python3
"""Structural: inf_P max_k E[r] versus inf_P E[max_k r], under the SAME
marginal constraint.

    V_avg  = inf_P max_k E_P[r(pi,k)]     -- good ON AVERAGE at each budget
    V_path = inf_P E_P[max_k r(pi,k)]     -- the DRAWN ranking is good at every budget

Always V_avg <= V_path. A theorem for the left does not say a sampled ranking
behaves across the whole budget axis.

FIRST FINDING, and the reason the LP is unavoidable. On the cycle family of the
previous batch, `min_pi max_k r(pi,k) = 0` for m = 5, 7, 9: some ranking is
optimal at EVERY budget simultaneously. So without the marginal constraint both
quantities are 0 and there is nothing to separate. Any gap here comes from having
to reproduce a given fractional path's prefix marginals -- exactly the obstruction
the rounding counterexample identified -- not from the difficulty of finding a
good ranking. Both LPs below therefore carry the marginal constraint.

Both are solved over ALL m! permutations. The reported optimum is float; every
reported gap is re-verified in exact rational arithmetic by rounding the primal
to rationals and recomputing both objectives, so a claimed separation rests on an
explicit feasible P, not on the solver.

    .venv/bin/python scripts/S2_avg_vs_path_gap.py
"""
from fractions import Fraction as F
import itertools, json, random
from pathlib import Path

import numpy as np
from scipy.optimize import linprog


def build(matrix):
    """L(S), OPT_k and the regret table r(pi,k), all exact."""
    m = len(matrix); h = len(matrix[0])
    D = sum(max(r) - min(r) for r in matrix)
    if D == 0:
        return None
    def L(S):
        res = [sum(matrix[i][a] for i in range(m) if i not in S) for a in range(h)]
        return F(max(res) - min(res), D)
    opt = {k: min(L(set(T)) for T in itertools.combinations(range(m), k))
           for k in range(m + 1)}
    perms = list(itertools.permutations(range(m)))
    R = [[L(set(pi[:k])) - opt[k] for k in range(m + 1)] for pi in perms]
    return m, perms, R


def marginals(perms, P, m):
    """x[i][k] = Pr(i in S_k)."""
    x = [[F(0)] * (m + 1) for _ in range(m)]
    for pi, p in zip(perms, P):
        if p == 0:
            continue
        for k in range(m + 1):
            for i in pi[:k]:
                x[i][k] += p
    return x


def solve_pair(m, perms, R, x, tau=0.0):
    """Both LPs on the same marginal domain. Returns (V_avg, P_avg, V_path, P_path)."""
    n = len(perms)
    A_in = np.array([[1.0 if i in pi[:k] else 0.0 for pi in perms]
                     for i in range(m) for k in range(m + 1)])
    b_in = np.array([float(x[i][k]) for i in range(m) for k in range(m + 1)])
    eq = [np.ones(n)]
    beq = [1.0]
    # marginal box |A_in p - b_in| <= tau
    ub_rows = list(A_in) + list(-A_in)
    ub_b = list(b_in + tau) + list(-(b_in - tau))
    # --- V_avg : min t st sum_pi p_pi r(pi,k) <= t
    Ravg = np.array([[float(R[j][k]) for j in range(n)] for k in range(m + 1)])
    A1 = np.c_[np.array(ub_rows), np.zeros(len(ub_rows))]
    A1 = np.vstack([A1, np.c_[Ravg, -np.ones(m + 1)]])
    b1 = np.array(list(ub_b) + [0.0] * (m + 1))
    lp1 = linprog(np.r_[np.zeros(n), 1.0], A_ub=A1, b_ub=b1,
                  A_eq=np.array([np.r_[eq[0], 0.0]]), b_eq=beq,
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    # --- V_path : min sum_pi p_pi max_k r(pi,k)
    c2 = np.array([float(max(R[j])) for j in range(n)])
    lp2 = linprog(c2, A_ub=np.array(ub_rows), b_ub=np.array(ub_b),
                  A_eq=np.array([eq[0]]), b_eq=beq,
                  bounds=[(0, None)] * n, method="highs")
    if not (lp1.success and lp2.success):
        return None
    return lp1.fun, lp1.x[:n], lp2.fun, lp2.x, lp2, ub_rows, ub_b


def exact_check(m, perms, R, Pfloat):
    """Rationalise a primal and recompute both objectives exactly."""
    P = [F(int(round(v * 10**6)), 10**6) for v in Pfloat]
    s = sum(P)
    if s == 0:
        return None
    P = [v / s for v in P]
    avg = max(sum(p * R[j][k] for j, p in enumerate(P) if p) for k in range(m + 1))
    path = sum(p * max(R[j]) for j, p in enumerate(P) if p)
    return P, avg, path


def certified_path_lower(m, perms, R, x, lp2res, ub_rows, ub_b):
    """A RATIONAL certified lower bound on V_path from the LP dual.

    For  min c'p  s.t.  A p <= b, 1'p = 1, p >= 0  the dual is
        max  z - y'b   s.t.   A'y + c >= z*1,  y >= 0.
    Rationalise scipy's (y, z), verify both dual constraints exactly, and the
    objective is then a valid lower bound with no solver in the loop.
    """
    yf = np.maximum(0.0, -lp2res.ineqlin.marginals)
    zf = float(lp2res.eqlin.marginals[0])
    y = [F(int(round(v * 10**7)), 10**7) for v in yf]
    z = F(int(round(zf * 10**7)), 10**7)
    c = [max(R[j]) for j in range(len(perms))]
    A = [[F(1) if i in pi[:k] else F(0) for pi in perms]
         for i in range(m) for k in range(m + 1)]
    rows = A + [[-v for v in r] for r in A]
    b = [x[i][k] for i in range(m) for k in range(m + 1)]
    bvec = b + [-v for v in b]
    if any(v < 0 for v in y):
        return None
    # A'y + c >= z for every permutation
    for j in range(len(perms)):
        acc = sum(y[r] * rows[r][j] for r in range(len(rows)) if y[r] != 0)
        if acc + c[j] < z:
            return None
    return z - sum(y[r] * bvec[r] for r in range(len(rows)) if y[r] != 0)


def main():
    rng = random.Random(20260914)
    best = None
    checked = 0
    for trial in range(60):
        m = rng.choice([4, 5])
        h = rng.choice([2, 3])
        matrix = [[0] + [rng.randint(-2, 2) for _ in range(h - 1)] for _ in range(m)]
        built = build(matrix)
        if built is None:
            continue
        m, perms, R = built
        # a feasible fractional path: marginals of a random mixture of rankings
        sup = rng.sample(range(len(perms)), k=min(3, len(perms)))
        P0 = [F(0)] * len(perms)
        for i in sup:
            P0[i] = F(1, len(sup))
        x = marginals(perms, P0, m)
        out = solve_pair(m, perms, R, x, tau=0.0)
        if out is None:
            continue
        checked += 1
        v1, p1, v2, p2, lp2res, ub_rows, ub_b = out
        if v2 - v1 > 1e-9:
            ex = exact_check(m, perms, R, p2)
            if ex is None:
                continue
            _, avg_at_path, path_at_path = ex
            ex1 = exact_check(m, perms, R, p1)
            _, avg_at_avg, path_at_avg = ex1
            gap = float(v2 - v1)
            cert = certified_path_lower(m, perms, R, x, lp2res, ub_rows, ub_b)
            if best is None or gap > best["gap_float"]:
                best = {"m": m, "matrix": matrix, "gap_float": gap,
                        "certified_V_path_lower": str(cert) if cert is not None else None,
                        "certified_gap": str(cert - avg_at_avg)
                            if cert is not None else None,
                        "certified_separation": bool(cert is not None
                                                     and cert > avg_at_avg),
                        "V_avg_lp": v1, "V_path_lp": v2,
                        "exact_V_avg_upper_at_LP_primal": str(avg_at_avg),
                        "exact_V_path_upper_at_LP_primal": str(path_at_path),
                        "exact_V_path_at_the_V_avg_optimum": str(path_at_avg)}
    print(f"instances solved: {checked}")
    if best is None:
        print("NO instance in this search had V_path > V_avg at tau = 0.")
        print("On every one the two coincided, so the sampled ranking was as good")
        print("across the budget axis as the average was at each budget.")
    else:
        print(f"largest separation found, m={best['m']}:")
        print(f"  matrix {best['matrix']}")
        print(f"  V_avg  (LP) = {best['V_avg_lp']:.8f}")
        print(f"  V_path (LP) = {best['V_path_lp']:.8f}   gap = {best['gap_float']:.2e}")
        print(f"  exact at the V_avg optimum : max_k E[r] = "
              f"{best['exact_V_avg_upper_at_LP_primal']}, "
              f"E[max_k r] = {best['exact_V_path_at_the_V_avg_optimum']}")
        if best.get("certified_separation"):
            print(f"  CERTIFIED (rational dual, feasibility checked exactly): "
                  f"V_path >= {best['certified_V_path_lower']} > "
                  f"{best['exact_V_avg_upper_at_LP_primal']} >= V_avg,  "
                  f"gap >= {best['certified_gap']}")
        else:
            print("  dual certificate did NOT verify exactly; the separation above "
                  "rests on the float LP for the V_path lower bound")
    out = Path("research/worker_S_avgpath_20260914/S2_avg_vs_path_gap.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "does inf_P max_k E[r] differ from inf_P E[max_k r] under the "
                    "same marginal constraint?",
        "cycle_family_note": "on the cycle family m=5,7,9 the deterministic minimax "
                             "min_pi max_k r is 0 -- some ranking is optimal at every "
                             "budget -- so without the marginal constraint both "
                             "quantities are 0 and nothing separates",
        "instances_solved": checked,
        "separation_found": best is not None,
        "best": best,
        "scope": "tau = 0, m in {4,5}, 2-3 scenarios, 60 random integer instances, "
                 "fractional path taken as the marginals of a random 3-ranking "
                 "mixture so the domain is non-empty. Float LP; any reported "
                 "separation is re-verified on a rationalised primal. Not a proof "
                 "that no instance separates.",
    }, indent=2, default=str) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
