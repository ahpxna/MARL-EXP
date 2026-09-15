#!/usr/bin/env python3
"""Structural: an INDEPENDENT exact checker for the V_avg / V_path separation.

`S2_avg_vs_path_gap.py` rationalised an LP primal and recomputed the objectives,
but never re-verified the MARGINALS after rationalisation, and its artifact did
not carry `x`, `P` and the duals, so the claim could not be checked without
rerunning the solver.

TWO DEFECTS OF THE FIRST VERSION OF THIS FILE, both fixed here.

  (1) It computed the marginals from `P` and then recomputed exactly the same
      quantity to compare against -- a check against itself, which passes for any
      `P` whatsoever. The target marginals are now FROZEN as literal data in
      `TARGET_X` below, and `marginals(P)` is checked against them.

  (2) It said "calls no optimizer" and then called `linprog` in the middle of the
      checking path. The certificates are now frozen too (`DUAL_PATH_*`,
      `DUAL_AVG_*`). The default run imports neither numpy nor scipy; the LP is
      reachable only through `--regenerate`, which PRODUCES the constants and is
      not part of any check.

  (3) The artifact carried no dual for V_avg, so 4/15 was only an upper bound
      attained at `P`. A dual for V_avg is included now, so both values are
      certified OPTIMA.

Instance (m = 5, two actions):  F = [[0,-2],[0,1],[0,1],[0,1],[0,0]].

The two programmes, both over couplings `P` with the SAME prescribed prefix
marginals `x` -- one policy, two ways of scoring it:

  V_path = min_P  E_P[max_k r]        dual: max  z + <y, x>
                                        s.t.  z + sum_{i,k} y_ik 1{i in pi[:k]}
                                              <= max_k R[pi][k]     for every pi

  V_avg  = min_P  max_k E_P[r_k]      dual: max  z + <y, x>
                                        s.t.  q >= 0, sum_k q_k = 1, and
                                              z + sum_{i,k} y_ik 1{i in pi[:k]}
                                              <= sum_k q_k R[pi][k] for every pi

Verified here, all in exact rational arithmetic:
  * P >= 0 and sum P = 1;
  * every prefix marginal of P equals the FROZEN target x;
  * max_k E_P[r] = 4/15   and   E_P[max_k r] = 7/15;
  * the V_path dual is feasible over all 120 permutations, objective 7/15;
  * the V_avg dual is feasible over all 120 permutations, objective 4/15;
  hence both are the exact OPTIMA, not merely bounds.

NEGATIVE CONTROLS.  A checker nobody has tried to break is not evidence.
`negative_controls()` damages the frozen data one number at a time -- a primal
weight (twice: once breaking sum-to-one, once keeping the sum at 1 but moving a
marginal, which are DIFFERENT failures), an entry of `TARGET_X`, a coefficient of
each dual `y`, and an entry of `DUAL_AVG_Q` -- and asserts that `check` REJECTS
every one of them.  `check` therefore takes the frozen constants as DEFAULT
arguments, so the default run is unchanged and the controls inject instead.

Then the dual l1 norms turn the point separation into a robust one: relaxing every
marginal equality into a box of half-width tau leaves P feasible, so V_avg cannot
rise above 4/15, while the V_path dual objective falls by at most tau*||y||_1:

    V_path(tau) - V_avg(tau) >= 1/5 - (17/5) tau,

positive for tau < 1/17.

    python3 scripts/S3_avg_path_certificate.py
    python3 scripts/S3_avg_path_certificate.py --controls-only
    python3 scripts/S3_avg_path_certificate.py --regenerate   # needs scipy
"""
from fractions import Fraction as F
import itertools, json, sys
from pathlib import Path

MATRIX = [[0, -2], [0, 1], [0, 1], [0, 1], [0, 0]]
SUPPORT = [(0, 2, 3, 1, 4), (1, 0, 4, 2, 3), (1, 4, 3, 2, 0)]

# ---- FROZEN DATA. Nothing below is recomputed from P before being compared. ----
TARGET_X = [['0', '1/3', '2/3', '2/3', '2/3', '1'],
            ['0', '2/3', '2/3', '2/3', '1', '1'],
            ['0', '0', '1/3', '1/3', '1', '1'],
            ['0', '0', '0', '2/3', '2/3', '1'],
            ['0', '0', '1/3', '2/3', '2/3', '1']]

DUAL_PATH_Y = [['0', '0', '0', '-1/5', '0', '0'],
               ['0', '-1/5', '-1/5', '-1/5', '1', '0'],
               ['0', '-1/5', '-1/5', '-1/5', '1/5', '0'],
               ['0', '-1/5', '-1/5', '0', '0', '0'],
               ['0', '-1/5', '-1/5', '0', '0', '0']]
DUAL_PATH_Z = '0'

DUAL_AVG_Q = ['0', '0', '1', '0', '0', '0']
DUAL_AVG_Y = [['0', '0', '0', '0', '0', '0'],
              ['0', '0', '0', '-1/5', '0', '0'],
              ['0', '0', '-1/5', '0', '3/5', '0'],
              ['0', '0', '-1/5', '0', '0', '0'],
              ['0', '0', '-2/5', '0', '0', '0']]
DUAL_AVG_Z = '0'


def _fr(table):
    return [[F(v) for v in row] for row in table]


def regret_table(matrix):
    m = len(matrix); h = len(matrix[0])
    D = sum(max(r) - min(r) for r in matrix)

    def L(S):
        res = [sum(matrix[i][a] for i in range(m) if i not in S) for a in range(h)]
        return F(max(res) - min(res), D)

    opt = {k: min(L(set(T)) for T in itertools.combinations(range(m), k))
           for k in range(m + 1)}
    perms = list(itertools.permutations(range(m)))
    R = {pi: [L(set(pi[:k])) - opt[k] for k in range(m + 1)] for pi in perms}
    return m, perms, R, D


def marginals(P, m):
    x = [[F(0)] * (m + 1) for _ in range(m)]
    for pi, p in P.items():
        for k in range(m + 1):
            for i in pi[:k]:
                x[i][k] += p
    return x


def dual_objective(y, z, x, m):
    return z + sum(y[i][k] * x[i][k] for i in range(m) for k in range(m + 1))


def dual_feasible(y, z, cost, perms, m):
    """z + sum_{i,k} y_ik 1{i in pi[:k]} <= cost(pi), for EVERY permutation."""
    worst = None
    for pi in perms:
        acc = z + sum(y[i][k] for k in range(m + 1) for i in pi[:k])
        slack = cost(pi) - acc
        if worst is None or slack < worst:
            worst = slack
    return worst >= 0, worst


def l1(y, m):
    return sum(abs(y[i][k]) for i in range(m) for k in range(m + 1))


def default_P():
    """The frozen primal: uniform on the three support permutations."""
    return {pi: F(1, len(SUPPORT)) for pi in SUPPORT}


def check(P=None, target_x=TARGET_X, dual_path_y=DUAL_PATH_Y,
          dual_path_z=DUAL_PATH_Z, dual_avg_q=DUAL_AVG_Q,
          dual_avg_y=DUAL_AVG_Y, dual_avg_z=DUAL_AVG_Z, verbose=True):
    """Verify the whole certificate in exact rational arithmetic.

    Every argument defaults to the frozen module-level constant, so calling
    `check()` with no arguments is exactly the original check.  The parameters
    exist so `negative_controls()` can INJECT damaged data and confirm that each
    damaged version is rejected.
    """
    if P is None:
        P = default_P()
    m, perms, R, D = regret_table(MATRIX)

    def say(*a):
        if verbose:
            print(*a)

    # --- primal feasibility, against FROZEN targets ---------------------------
    if any(v < 0 for v in P.values()):
        raise AssertionError("P has a negative weight")
    if sum(P.values()) != 1:
        raise AssertionError(f"P does not sum to 1 (sum = {sum(P.values())})")
    x_target = _fr(target_x)
    x = marginals(P, m)
    if x != x_target:
        bad = [(i, k) for i in range(m) for k in range(m + 1)
               if x[i][k] != x_target[i][k]]
        raise AssertionError(
            f"marginals of P do not match the frozen target x at {bad}: "
            f"got {[str(x[i][k]) for i, k in bad]}, "
            f"frozen {[str(x_target[i][k]) for i, k in bad]}")
    say(f"primal: P >= 0, sum P = 1, and all {m*(m+1)} prefix marginals of P "
        f"equal the FROZEN target x (not a recomputation of themselves)")

    v_avg_at_P = max(sum(p * R[pi][k] for pi, p in P.items()) for k in range(m + 1))
    v_path_at_P = sum(p * max(R[pi]) for pi, p in P.items())
    say(f"  max_k E_P[r]  = {v_avg_at_P}")
    say(f"  E_P[max_k r]  = {v_path_at_P}")
    if v_avg_at_P != F(4, 15) or v_path_at_P != F(7, 15):
        raise AssertionError(f"objectives are {v_avg_at_P}, {v_path_at_P}, "
                             f"expected 4/15 and 7/15")

    # --- V_path dual, frozen, verified over all 120 permutations --------------
    # the objective is formed against the FROZEN x, not against the marginals
    # recomputed from P (they were just proved equal).
    yp, zp = _fr(dual_path_y), F(dual_path_z)
    ok, worst = dual_feasible(yp, zp, lambda pi: max(R[pi]), perms, m)
    objp = dual_objective(yp, zp, x_target, m)
    l1p = l1(yp, m)
    if not ok:
        raise AssertionError(f"V_path dual infeasible, worst slack {worst}")
    say(f"dual for V_path: feasible EXACTLY over all {len(perms)} permutations "
        f"(worst slack {worst}), objective {objp}, ||y||_1 = {l1p}")
    if objp != F(7, 15):
        raise AssertionError(f"V_path dual objective is {objp}, not 7/15")
    say("  equals the primal, so V_path = 7/15 is the OPTIMUM")

    # --- V_avg dual, frozen, verified over all 120 permutations ---------------
    ya, za, q = _fr(dual_avg_y), F(dual_avg_z), [F(v) for v in dual_avg_q]
    if any(v < 0 for v in q) or sum(q) != 1:
        raise AssertionError(
            f"the V_avg dual weight q is not a distribution: "
            f"q = {[str(v) for v in q]}, sum = {sum(q)}")
    ok, worst = dual_feasible(
        ya, za, lambda pi: sum(q[k] * R[pi][k] for k in range(m + 1)), perms, m)
    obja = dual_objective(ya, za, x_target, m)
    l1a = l1(ya, m)
    if not ok:
        raise AssertionError(f"V_avg dual infeasible, worst slack {worst}")
    say(f"dual for V_avg : feasible EXACTLY over all {len(perms)} permutations "
        f"(worst slack {worst}), objective {obja}, ||y||_1 = {l1a}")
    if obja != F(4, 15):
        raise AssertionError(f"V_avg dual objective is {obja}, not 4/15")
    say("  equals the primal, so V_avg = 4/15 is the OPTIMUM")

    gap0 = objp - obja
    tau_max = gap0 / l1p
    say(f"\nrobust separation: V_path(tau) - V_avg(tau) >= {gap0} - {l1p} tau, "
        f"positive for tau < {tau_max} = {float(tau_max):.6f}")
    say("  reason: P stays feasible when each marginal equality is widened into "
        "a box of half-width tau, so V_avg(tau) <= 4/15; and widening lowers the "
        "V_path dual objective by at most tau*||y||_1, so V_path(tau) >= 7/15 - "
        f"{l1p} tau.")

    return {"matrix": MATRIX, "support": [list(s) for s in SUPPORT],
            "P": {str(k): str(v) for k, v in P.items()},
            "x_frozen": target_x,
            "V_avg": str(obja), "V_path": str(objp),
            "V_avg_at_P": str(v_avg_at_P), "V_path_at_P": str(v_path_at_P),
            "dual_path_y": dual_path_y, "dual_path_z": dual_path_z,
            "dual_path_l1": str(l1p),
            "dual_avg_q": dual_avg_q, "dual_avg_y": dual_avg_y,
            "dual_avg_z": dual_avg_z, "dual_avg_l1": str(l1a),
            "permutations_checked": len(perms),
            "separation_law": f"V_path(tau) - V_avg(tau) >= {gap0} - {l1p}*tau",
            "tau_max": str(tau_max)}


def _copy(table):
    return [list(row) for row in table]


def negative_controls():
    """Damage the frozen data one number at a time; `check` must REJECT each.

    Nothing here is a float comparison and nothing here calls an optimizer: each
    case rebuilds the exact rational check on injected data and demands an
    AssertionError.  A case that is ACCEPTED is itself a failure of this script.
    """
    base = default_P()
    cases = []

    # (a) PRIMAL WEIGHT -- two genuinely different failures.
    #     (a1) the weights stop summing to 1.
    P = dict(base); P[SUPPORT[0]] = F(1, 2)
    cases.append(("a1  P[(0,2,3,1,4)] : 1/3 -> 1/2, so sum P = 7/6 != 1",
                  {"P": P}))
    #     (a2) the weights still sum to 1, but a prefix marginal moves.  This is
    #     the failure the FIRST version of this file could not see, because it
    #     compared the marginals with a recomputation of themselves.
    P = dict(base)
    P[SUPPORT[0]] = F(1, 3) + F(1, 30)
    P[SUPPORT[1]] = F(1, 3) - F(1, 30)
    cases.append(("a2  1/30 of mass moved between two support permutations; "
                  "sum P is still 1 but the marginals move", {"P": P}))

    # (b) one entry of the frozen target marginals.
    X = _copy(TARGET_X); X[2][3] = '2/3'
    cases.append(("b   TARGET_X[2][3] : 1/3 -> 2/3", {"target_x": X}))

    # (c) one coefficient of each dual y (both entries sit on a marginal with
    #     x != 0, so the damage cannot hide in the dual's non-uniqueness).
    Y = _copy(DUAL_PATH_Y); Y[1][4] = '6/5'
    cases.append(("c1  DUAL_PATH_Y[1][4] : 1 -> 6/5", {"dual_path_y": Y}))
    Y = _copy(DUAL_PATH_Y); Y[1][4] = '4/5'
    cases.append(("c1' DUAL_PATH_Y[1][4] : 1 -> 4/5 (stays feasible, "
                  "objective drops)", {"dual_path_y": Y}))
    Y = _copy(DUAL_AVG_Y); Y[2][4] = '4/5'
    cases.append(("c2  DUAL_AVG_Y[2][4] : 3/5 -> 4/5", {"dual_avg_y": Y}))
    Y = _copy(DUAL_AVG_Y); Y[2][4] = '2/5'
    cases.append(("c2' DUAL_AVG_Y[2][4] : 3/5 -> 2/5 (stays feasible, "
                  "objective drops)", {"dual_avg_y": Y}))

    # (d) one entry of q, so q is no longer a distribution.
    q = list(DUAL_AVG_Q); q[0] = '-1/5'
    cases.append(("d   DUAL_AVG_Q[0] : 0 -> -1/5, so q is not a distribution",
                  {"dual_avg_q": q}))
    q = list(DUAL_AVG_Q); q[2] = '1/2'
    cases.append(("d'  DUAL_AVG_Q[2] : 1 -> 1/2, so sum q = 1/2 != 1",
                  {"dual_avg_q": q}))

    print(f"negative controls: {len(cases)} perturbations of the frozen data, "
          f"each must be REJECTED")
    log = []
    for name, kw in cases:
        try:
            check(verbose=False, **kw)
        except AssertionError as e:
            msg = str(e)
            msg = msg if len(msg) <= 150 else msg[:147] + "..."
            print(f"  REJECTED  {name}")
            print(f"            reason: {msg}")
            log.append({"perturbation": name, "rejected": True, "reason": str(e)})
        else:
            raise AssertionError(
                f"NEGATIVE CONTROL FAILED: the checker ACCEPTED the damaged "
                f"data '{name}'. The checker is not checking that quantity.")
    print(f"  all {len(cases)} perturbations rejected")
    return log


def regenerate():
    """PRODUCES the frozen constants. Not part of any check; needs scipy."""
    import numpy as np
    from scipy.optimize import linprog
    m, perms, R, D = regret_table(MATRIX)
    P = {pi: F(1, len(SUPPORT)) for pi in SUPPORT}
    x = marginals(P, m)
    idx = [(i, k) for i in range(m) for k in range(m + 1)]
    A_eq = np.array([[1.0 if i in pi[:k] else 0.0 for pi in perms] for i, k in idx]
                    + [np.ones(len(perms))])
    b_eq = np.array([float(x[i][k]) for i, k in idx] + [1.0])

    def rat(v, den):
        return F(round(v * den), den)

    print("TARGET_X =", [[str(v) for v in row] for row in x])
    lp = linprog(np.array([float(max(R[pi])) for pi in perms]), A_eq=A_eq,
                 b_eq=b_eq, bounds=[(0, None)] * len(perms), method="highs")
    du = lp.eqlin.marginals
    Y = [[F(0)] * (m + 1) for _ in range(m)]
    for t, (i, k) in enumerate(idx):
        Y[i][k] = rat(du[t], 15)
    print("DUAL_PATH_Y =", [[str(v) for v in row] for row in Y])
    print("DUAL_PATH_Z =", str(rat(du[-1], 15)))

    nP = len(perms)
    c2 = np.zeros(nP + 1); c2[-1] = 1.0
    A_ub = [[float(R[pi][k]) for pi in perms] + [-1.0] for k in range(m + 1)]
    lp2 = linprog(c2, A_ub=np.array(A_ub), b_ub=np.zeros(m + 1),
                  A_eq=np.hstack([A_eq, np.zeros((A_eq.shape[0], 1))]), b_eq=b_eq,
                  bounds=[(0, None)] * nP + [(None, None)], method="highs")
    q = -lp2.ineqlin.marginals; duy = lp2.eqlin.marginals
    Y = [[F(0)] * (m + 1) for _ in range(m)]
    for t, (i, k) in enumerate(idx):
        Y[i][k] = rat(duy[t], 15)
    print("DUAL_AVG_Q =", [str(rat(q[k], 15)) for k in range(m + 1)])
    print("DUAL_AVG_Y =", [[str(v) for v in row] for row in Y])
    print("DUAL_AVG_Z =", str(rat(duy[-1], 15)))


def main():
    if "--regenerate" in sys.argv:
        regenerate()
        return
    data = check()
    out = Path("research/worker_S_avgpath_20260914/S3_avg_path_certificate.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "checker": "independent; the default run imports neither numpy nor scipy, "
                   "and verifies every condition in exact rational arithmetic "
                   "against constants frozen in the source",
        "verified": ["P >= 0 and sums to 1",
                     "all prefix marginals of P equal the FROZEN target x",
                     "max_k E_P[r] = 4/15", "E_P[max_k r] = 7/15",
                     "V_path dual feasible over all 120 permutations, objective 7/15",
                     "V_avg dual feasible over all 120 permutations, objective 4/15",
                     "hence both values are OPTIMA"],
        "defects_fixed": [
            "the marginals were previously computed from P and then compared with "
            "the same computation -- a check against itself that passes for any P. "
            "The target marginals are now frozen data.",
            "the checker previously called linprog while claiming to call no "
            "optimizer. The LP now lives behind --regenerate and produces the "
            "constants; it is not reachable from the checking path.",
            "the artifact previously carried no dual for V_avg, so 4/15 was only an "
            "upper bound attained at P. A dual is included and verified.",
        ],
        "data": data,
        "phrasing_correction": "the ratio 7/4 says the EXPECTED WORST-BUDGET regret "
                               "is 75% higher than the WORST-BUDGET EXPECTED regret. "
                               "It does NOT say every drawn ranking is 75% worse.",
        "scope": "one instance, m = 5, two actions. No claim about how the gap "
                 "scales with m, and the tau law is an argument from the checked "
                 "certificates, not a Lean theorem.",
    }, indent=2) + "\n")
    print(f"-> {out}")


if __name__ == "__main__":
    main()
