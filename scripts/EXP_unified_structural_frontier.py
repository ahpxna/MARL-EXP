#!/usr/bin/env python3
"""Does the uniform-retention price survive when the marginals are relaxed?

Setting (sec 7 of the unified batch).  The structural family for m >= 5 is

    g_m = (-3, (-1)^p, (+1)^q, 3),  p = ceil((m-2)/2), q = floor((m-2)/2),
    D   = m + 4,

    S_k(pi) = sum_{j<=k} g_{pi(j)},  d_k(pi) = |S_k(pi)| - (k mod 2),
    r_k     = d_k / D.

The EXACT uniform-retention optimum is already proved:

    V_avg^unif(m) = 4/(m(m+4))     m even,
                    (m+3)/(m(m+4)) m odd,

against the free optimum V_avg^free(m) = 2/((m+4)(m-1)).  The question here is
whether the linear-in-m relative price is an artefact of demanding EXACT
uniformity.  Relax it to

    |Pr(i in first k) - k/m| <= eta/m   for every labelled i and every k,

and call the optimum V_avg^(eta).  The claim to test is the lower bound

    V_avg^(eta) >= (m + 3 - (m+1) eta) / (m(m+4))   for odd m,

whose proof centres the last-position loss coefficients at 2 and uses that
their total absolute deviation is exactly m+1.

The LP is solved in PATTERN space.  This is legitimate: the objective depends
on labels not at all, and averaging a feasible distribution over relabellings
inside a weight type leaves the objective fixed and can only shrink each
marginal deviation, so an optimal symmetric solution always exists.

Self-checks: eta = 0 must reproduce the proved value; the frontier must lie
between the eta-bound and V^unif everywhere; and a vacuous eta must reproduce
the free value.
"""

import json
import math
import sys
from fractions import Fraction as Fr
from itertools import permutations, combinations

import numpy as np
from scipy.optimize import linprog

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def family(m):
    p = -(-(m - 2) // 2)
    q = (m - 2) // 2
    return [-3] + [-1] * p + [1] * q + [3], p, q


def types_of(g):
    """Distinct weights, and the multiplicity of each."""
    order = sorted(set(g))
    return order, [g.count(t) for t in order]


def patterns(g):
    """Distinct weight sequences (multiset permutations)."""
    return sorted(set(permutations(g)))


def defects(pat):
    """d_k for k = 1..m-1, exact integers."""
    m = len(pat)
    out, s = [], 0
    for k in range(1, m):
        s += pat[k - 1]
        out.append(abs(s) - (k % 2))
    return out


def solve(m, eta, free=False):
    """Minimise max_k E d_k subject to the relaxed retained-marginal band.
    Returns (value of V = t/D, the floating-point LP object).
    No rational primal/dual certificate is produced."""
    g, p, q = family(m)
    D = m + 4
    pats = patterns(g)
    tps, mult = types_of(g)
    n = len(pats)

    dmat = np.array([defects(P) for P in pats], dtype=float)     # n x (m-1)

    # variables: x_1..x_n, t     -> minimise t
    c = np.zeros(n + 1)
    c[-1] = 1.0

    A_ub, b_ub = [], []
    # E d_k <= t   for every budget k
    for kk in range(m - 1):
        row = np.zeros(n + 1)
        row[:n] = dmat[:, kk]
        row[-1] = -1.0
        A_ub.append(row)
        b_ub.append(0.0)

    if not free:
        # For each type tau and each prefix k:
        #   | E[N_tau(k)]/n_tau - k/m | <= eta/m
        for ti, tval in enumerate(tps):
            ntau = mult[ti]
            for k in range(1, m):
                cnt = np.array([sum(1 for j in range(k) if P[j] == tval)
                                for P in pats], dtype=float)
                base = k / m
                hi = base + eta / m
                lo = base - eta / m
                r1 = np.zeros(n + 1); r1[:n] = cnt / ntau
                A_ub.append(r1); b_ub.append(hi)
                r2 = np.zeros(n + 1); r2[:n] = -cnt / ntau
                A_ub.append(r2); b_ub.append(-lo)

    A_eq = np.zeros((1, n + 1)); A_eq[0, :n] = 1.0
    b_eq = np.array([1.0])
    bounds = [(0, None)] * n + [(None, None)]

    res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs")
    if not res.success:
        return None, res
    return res.fun / D, res


def main():
    print("=" * 76)
    print("Structural: the uniform-retention price under relaxed marginals")
    print("=" * 76)

    ms = [5, 6, 7, 8, 9]
    etas = [0.0, 0.1, 0.25, 0.5, 0.75, 1.0, 1.25, 1.5, 2.0, 3.0]

    exact_unif = {}
    for m in ms:
        exact_unif[m] = (Fr(4, m * (m + 4)) if m % 2 == 0
                         else Fr(m + 3, m * (m + 4)))
    free_val = {m: Fr(2, (m + 4) * (m - 1)) for m in ms}

    print("\n  anchor: eta = 0 must reproduce the proved uniform value")
    print("  " + "-" * 70)
    anchor_ok = True
    for m in ms:
        v, _ = solve(m, 0.0)
        want = float(exact_unif[m])
        ok = v is not None and abs(v - want) < 1e-9
        anchor_ok = anchor_ok and ok
        print(f"      m={m}: LP V^(0) = {v:.10f}   proved = {want:.10f} "
              f"({exact_unif[m]})   {'match' if ok else 'MISMATCH'}")
    check("eta = 0 reproduces the proved V_avg^unif at every m", anchor_ok)

    print("\n  anchor: a vacuous band must reproduce the free value")
    print("  " + "-" * 70)
    free_ok = True
    for m in ms:
        v, _ = solve(m, 0.0, free=True)
        want = float(free_val[m])
        ok = v is not None and abs(v - want) < 1e-9
        free_ok = free_ok and ok
        print(f"      m={m}: LP V^free = {v:.10f}   known = {want:.10f} "
              f"({free_val[m]})   {'match' if ok else 'MISMATCH'}")
    check("the unconstrained LP reproduces the known free value", free_ok)

    print("\n  the frontier in eta")
    print("  " + "-" * 70)
    frontier, bound_ok, mono_ok = {}, True, True
    for m in ms:
        row = []
        for eta in etas:
            v, _ = solve(m, eta)
            row.append(None if v is None else float(v))
        frontier[m] = row
        vals = " ".join(f"{x:.5f}" if x is not None else "  --  " for x in row)
        print(f"      m={m}: {vals}")
        # monotone non-increasing in eta
        seq = [x for x in row if x is not None]
        if any(seq[i + 1] > seq[i] + 1e-9 for i in range(len(seq) - 1)):
            mono_ok = False
        # the odd-m lower bound
        if m % 2 == 1:
            for eta, v in zip(etas, row):
                if v is None:
                    continue
                lb = (m + 3 - (m + 1) * eta) / (m * (m + 4))
                if v < lb - 1e-9:
                    bound_ok = False
    print(f"      {'eta =':>9} " + " ".join(f"{e:7.2f}" for e in etas))

    check("the frontier is non-increasing in eta", mono_ok)
    check("odd-m lower bound (m+3-(m+1)eta)/(m(m+4)) holds at every tested eta",
          bound_ok)
    check("every frontier value is at most V^unif",
          all(all(v is None or v <= float(exact_unif[m]) + 1e-9
                  for v in frontier[m]) for m in ms))
    check("every frontier value is at least V^free",
          all(all(v is None or v >= float(free_val[m]) - 1e-9
                  for v in frontier[m]) for m in ms))

    print("\n  the Theta(1/m) vs Theta(1/m^2) separation, at fixed eta")
    print("  " + "-" * 70)
    sep_rows = []
    for eta0 in [0.0, 0.25, 0.5, 0.75]:
        ratios = []
        for m in ms:
            v, _ = solve(m, eta0)
            ratios.append(v / float(free_val[m]))
        sep_rows.append({"eta": eta0, "ratios": ratios})
        print(f"      eta={eta0:4.2f}:  V^(eta)/V^free = "
              + "  ".join(f"m={m}:{r:6.3f}" for m, r in zip(ms, ratios)))
    check("the relative price still grows with m at every fixed eta < 1",
          all(r["ratios"][-1] > r["ratios"][0] for r in sep_rows))

    # Where does the odd-m lower bound go non-positive?  NOT a sharpness claim.
    print("\n  where the LOWER BOUND degrades (not a sharpness claim)")
    print("  " + "-" * 70)
    for m in [5, 7, 9]:
        eta_zero = (m + 3) / (m + 1)
        print(f"      m={m}: the bound (m+3-(m+1)eta) hits zero at "
              f"eta = {eta_zero:.4f}; the LP value there is still "
              f"{solve(m, eta_zero)[0]:.6f}")
    check("the LP optimum stays strictly positive where the bound goes to zero",
          all(solve(m, (m + 3) / (m + 1))[0] > 1e-9 for m in [5, 7, 9]),
          "so eta = 1 is NOT established as a sharp threshold")

    # Stability of V under weight perturbation.
    print("\n  stability under weight perturbation")
    print("  " + "-" * 70)
    rng = np.random.default_rng(7)
    stab_ok, worst = True, 0.0
    for m in [5, 6, 7]:
        g, _, _ = family(m)
        D = m + 4
        v0, _ = solve(m, 0.0)
        for _ in range(6):
            pert = rng.uniform(-0.25, 0.25, size=m)
            gp = [g[i] + pert[i] for i in range(m)]
            l1 = float(np.abs(pert).sum())
            # re-solve with perturbed weights, same band and same D
            pats = sorted(set(permutations(range(m))))
            # Recompute each budget's TRUE optimum after perturbing weights.
            # The parity baseline belongs only to the original integer family.
            budget_opt = {
                k: min(abs(sum(gp[j] for j in subset))
                       for subset in combinations(range(m), k))
                for k in range(1, m)
            }
            dm = []
            for P in pats:
                s, row = 0.0, []
                for k in range(1, m):
                    s += gp[P[k - 1]]
                    row.append(abs(s) - budget_opt[k])
                dm.append(row)
            dm = np.array(dm)
            n = len(pats)
            c = np.zeros(n + 1); c[-1] = 1.0
            A, b = [], []
            for kk in range(m - 1):
                r = np.zeros(n + 1); r[:n] = dm[:, kk]; r[-1] = -1.0
                A.append(r); b.append(0.0)
            for i in range(m):
                for k in range(1, m):
                    cnt = np.array([1.0 if i in P[:k] else 0.0 for P in pats])
                    r1 = np.zeros(n + 1); r1[:n] = cnt
                    A.append(r1); b.append(k / m)
                    r2 = np.zeros(n + 1); r2[:n] = -cnt
                    A.append(r2); b.append(-k / m)
            Aeq = np.zeros((1, n + 1)); Aeq[0, :n] = 1.0
            r = linprog(c, A_ub=np.array(A), b_ub=np.array(b), A_eq=Aeq,
                        b_eq=np.array([1.0]),
                        bounds=[(0, None)] * n + [(None, None)], method="highs")
            if not r.success:
                raise RuntimeError(f"Perturbed LP failed for m={m}: {r.message}")
            v1 = r.fun / D
            gap = abs(v1 - v0)
            allowed = 2 * l1 / D
            worst = max(worst, gap / max(allowed, 1e-12))
            if gap > allowed + 1e-9:
                stab_ok = False
    check("|V(g) - V(g')| <= 2 ||g-g'||_1 / D on random perturbations",
          stab_ok, f"worst ratio to the bound = {worst:.3f}")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 76)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 76)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_unified_structural_frontier.py").read_bytes()).hexdigest(),"evidence_class": "NUMERICAL_FLOAT_LP",
           "stability_objective": "true_budget_optimum_same_D_v2",
           "rational_primal_dual_certificate": False,
           "breakpoint_certificate": False, "etas": etas, "frontier": {str(k): v for k, v in frontier.items()},
           "V_unif": {str(m): str(exact_unif[m]) for m in ms},
           "V_free": {str(m): str(free_val[m]) for m in ms},
           "separation": sep_rows, "checks": CHECKS, "all_passed": nfail == 0}
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    with open("research/unified_20260919/structural_frontier_corrected_v2.json", "w") as f:
        json.dump(out, f, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())
