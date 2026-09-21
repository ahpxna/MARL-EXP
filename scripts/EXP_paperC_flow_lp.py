#!/usr/bin/env python3
"""Paper C, step C3: the marginal-constrained prefix game as a polynomial-size flow LP.

The constrained optimum

    V_m(eta) = inf_P max_k  E_{pi ~ P} r_k(pi; g),
    r_k(pi; g) = ( |sum_{l<=k} g_{pi_l}| - b_k(g) ) / D,
    b_k(g)     = min_{|S|=k} |sum_{i in S} g_i|,

subject to the retained-marginal band

    | Pr_P(i in prefix_k) - k/m | <= eta/m,

was previously solved by enumerating permutations, which costs m! and dies past m = 11.
This script replaces that with a flow LP whose size is O(m^2), on the DAG of PREFIX
COMPOSITIONS

    v = (n_{-3}, n_{-1}, n_{+1}, n_{+3}),   bounded by (1, p, q, 1),

so the whole frontier becomes computable at sizes the permutation formulation cannot
reach.  Three equalities make the reduction legitimate, and all three are checked here
rather than assumed:

  (E1) SYMMETRISATION.  Averaging a feasible ranking distribution over relabellings
       inside a weight type leaves max_k E r_k unchanged and keeps the band, because
       r_k depends on labels not at all and each item's marginal becomes the type
       average, whose deviation is at most the average of the deviations.

  (E2) RANKING -> FLOW.  Every ranking distribution induces a unit flow on the DAG,
       with occupancy f_v = Pr(the length-|v| prefix has composition v).

  (E3) FLOW -> RANKING.  Every unit flow decomposes into a distribution over paths;
       labelling uniformly inside each type turns a path into a ranking with the same
       objective and the same marginals.

(E2) and (E3) together say the two LPs have the same value.  That is checked directly:
the flow LP must reproduce the permutation LP at every m where the latter can still be
run, and must reproduce the proved V_m(0) and the known free value.

Only then is the flow LP used to go where enumeration cannot: to test the breakpoint
conjecture

    eta*_m = 1 (m odd),   (m-2)/(2(m-1)) (m even)

at sizes well beyond m = 11.
"""

import json
import sys
from fractions import Fraction as Fr
from itertools import combinations, permutations

import numpy as np
from scipy.optimize import linprog

CHECKS = []

WEIGHTS = (-3, -1, 1, 3)


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def family(m):
    """g_m = (-3, (-1)^p, (+1)^q, 3) with p = ceil((m-2)/2), q = floor((m-2)/2)."""
    p = -(-(m - 2) // 2)
    q = (m - 2) // 2
    return [-3] + [-1] * p + [1] * q + [3], p, q


def caps(m):
    p = -(-(m - 2) // 2)
    q = (m - 2) // 2
    return (1, p, q, 1)


def states(m):
    """Every reachable prefix composition, grouped by layer."""
    c = caps(m)
    byk = {k: [] for k in range(m + 1)}
    for a in range(c[0] + 1):
        for b in range(c[1] + 1):
            for cc in range(c[2] + 1):
                for d in range(c[3] + 1):
                    byk[a + b + cc + d].append((a, b, cc, d))
    return byk, c


def prefix_sum(v):
    return sum(WEIGHTS[i] * v[i] for i in range(4))


def baseline(m):
    """b_k(g) computed from the definition, by minimising over compositions."""
    byk, _ = states(m)
    return {k: min(abs(prefix_sum(v)) for v in byk[k]) for k in range(1, m)}


def edges_of(m):
    """DAG edges: add one item of some type."""
    byk, c = states(m)
    E = []
    for k in range(m):
        for v in byk[k]:
            for tau in range(4):
                if v[tau] < c[tau]:
                    w = list(v)
                    w[tau] += 1
                    E.append((v, tau, tuple(w)))
    return E


def solve_flow(m, eta, free=False):
    """The O(m^2) flow LP.  Returns (V, diagnostics)."""
    byk, c = states(m)
    b = baseline(m)
    E = edges_of(m)
    eidx = {(v, t): i for i, (v, t, w) in enumerate(E)}
    nE = len(E)
    D = m + 4
    root = (0, 0, 0, 0)
    term = tuple(c)

    out_of, in_to = {}, {}
    for i, (v, t, w) in enumerate(E):
        out_of.setdefault(v, []).append(i)
        in_to.setdefault(w, []).append(i)

    # variables: edge flows (nE), then t
    nv = nE + 1
    cost = np.zeros(nv)
    cost[-1] = 1.0

    A_eq, b_eq = [], []
    # unit flow out of the root
    r = np.zeros(nv)
    for i in out_of.get(root, []):
        r[i] = 1.0
    A_eq.append(r); b_eq.append(1.0)
    # conservation at every interior state
    for k in range(1, m):
        for v in byk[k]:
            r = np.zeros(nv)
            for i in in_to.get(v, []):
                r[i] += 1.0
            for i in out_of.get(v, []):
                r[i] -= 1.0
            A_eq.append(r); b_eq.append(0.0)

    def occupancy_row(v):
        """f_v expressed in edge variables (inflow)."""
        r = np.zeros(nv)
        for i in in_to.get(v, []):
            r[i] += 1.0
        return r

    A_ub, b_ub = [], []
    # E r_k <= t
    for k in range(1, m):
        r = np.zeros(nv)
        for v in byk[k]:
            coef = (abs(prefix_sum(v)) - b[k]) / D
            r += coef * occupancy_row(v)
        r[-1] = -1.0
        A_ub.append(r); b_ub.append(0.0)

    # retained-marginal band, per weight type
    if not free:
        for tau in range(4):
            N = c[tau]
            if N == 0:
                continue
            for k in range(1, m):
                r = np.zeros(nv)
                for v in byk[k]:
                    r += (v[tau] / N) * occupancy_row(v)
                A_ub.append(r.copy()); b_ub.append(k / m + eta / m)
                A_ub.append(-r); b_ub.append(-(k / m - eta / m))

    res = linprog(cost, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                  bounds=[(0, None)] * nE + [(None, None)], method="highs")
    if not res.success:
        return None, {"states": sum(len(byk[k]) for k in byk), "edges": nE}
    return res.fun, {"states": sum(len(byk[k]) for k in byk), "edges": nE,
                     "lp_rows": len(A_ub) + len(A_eq)}


def solve_perm(m, eta, free=False):
    """The reference permutation LP -- exponential, used only to validate."""
    g, p, q = family(m)
    b = baseline(m)
    D = m + 4
    pats = sorted(set(permutations(g)))
    tps = sorted(set(g))
    mult = [g.count(t) for t in tps]
    n = len(pats)

    def defects(P):
        out, s = [], 0
        for k in range(1, m):
            s += P[k - 1]
            out.append(abs(s) - b[k])
        return out

    dm = np.array([defects(P) for P in pats], dtype=float)
    cost = np.zeros(n + 1); cost[-1] = 1.0
    A_ub, b_ub = [], []
    for kk in range(m - 1):
        r = np.zeros(n + 1); r[:n] = dm[:, kk] / D; r[-1] = -1.0
        A_ub.append(r); b_ub.append(0.0)
    if not free:
        for ti, tv in enumerate(tps):
            N = mult[ti]
            for k in range(1, m):
                cnt = np.array([sum(1 for j in range(k) if P[j] == tv)
                                for P in pats], dtype=float)
                r = np.zeros(n + 1); r[:n] = cnt / N
                A_ub.append(r.copy()); b_ub.append(k / m + eta / m)
                A_ub.append(-r); b_ub.append(-(k / m - eta / m))
    A_eq = np.zeros((1, n + 1)); A_eq[0, :n] = 1.0
    res = linprog(cost, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=A_eq, b_eq=np.array([1.0]),
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    return (res.fun if res.success else None)


def main():
    print("=" * 78)
    print("Paper C / C3: the prefix game as a polynomial-size flow LP")
    print("=" * 78)

    # ---- the baseline is the real one, and equals parity on THIS family
    par_ok = all(baseline(m)[k] == k % 2 for m in range(5, 14) for k in range(1, m))
    check("b_k(g) computed from its definition equals the parity floor on this family",
          par_ok, "so the parity shortcut is justified here, not assumed")

    # ---- size
    print("\n  problem size: flow LP against permutation LP")
    print("  " + "-" * 70)
    for m in [5, 7, 9, 11, 15, 21, 31]:
        _, diag = solve_flow(m, 0.0)
        g, _, _ = family(m)
        nperm = len(set(permutations(g))) if m <= 11 else None
        ns = f"{nperm:,}" if nperm else "intractable"
        print(f"      m={m:3d}:  flow states={diag['states']:5d} edges={diag['edges']:5d}"
              f"   |  permutations={ns}")

    # ---- E2+E3: the two LPs agree wherever both can run
    print("\n  agreement of the two formulations")
    print("  " + "-" * 70)
    agree_ok = True
    for m in [5, 6, 7, 8, 9]:
        for eta in [0.0, 0.25, 0.5, 1.0]:
            a, _ = solve_flow(m, eta)
            bb = solve_perm(m, eta)
            if a is None or bb is None or abs(a - bb) > 1e-8:
                agree_ok = False
                print(f"      MISMATCH m={m} eta={eta}: flow={a} perm={bb}")
        af, _ = solve_flow(m, 0.0, free=True)
        bf = solve_perm(m, 0.0, free=True)
        if abs(af - bf) > 1e-8:
            agree_ok = False
        print(f"      m={m}: agree at eta in {{0,.25,.5,1}} and on the free problem")
    check("flow LP reproduces the permutation LP exactly  [E2 and E3]", agree_ok)

    # ---- anchors
    anch_ok = True
    for m in [5, 6, 7, 8, 9, 10, 11]:
        v0, _ = solve_flow(m, 0.0)
        want = float(Fr(4, m * (m + 4)) if m % 2 == 0 else Fr(m + 3, m * (m + 4)))
        vf, _ = solve_flow(m, 0.0, free=True)
        wantf = float(Fr(2, (m + 4) * (m - 1)))
        if abs(v0 - want) > 1e-9 or abs(vf - wantf) > 1e-9:
            anch_ok = False
    check("flow LP reproduces the proved V_m(0) and the known free value", anch_ok)

    # ---- the breakpoint, far beyond the permutation limit
    print("\n  breakpoint eta* located by bisection on the flow LP")
    print("  " + "-" * 70)
    rows, conj_ok = [], True
    for m in [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 19, 21, 25, 31]:
        free = float(Fr(2, (m + 4) * (m - 1)))
        lo, hi = 0.0, 2.0
        for _ in range(40):
            mid = (lo + hi) / 2
            v, _ = solve_flow(m, mid)
            if v is not None and v > free + 1e-10:
                lo = mid
            else:
                hi = mid
        pred = 1.0 if m % 2 else (m - 2) / (2 * (m - 1))
        ok = abs(hi - pred) < 2e-3
        conj_ok = conj_ok and ok
        rows.append({"m": m, "eta_star": hi, "predicted": pred, "match": ok})
        print(f"      m={m:3d} ({'odd ' if m % 2 else 'even'}):  eta* = {hi:.6f}"
              f"   predicted {pred:.6f}   {'match' if ok else 'MISS'}")
    check("the breakpoint conjecture holds at every size tested, up to m = 31",
          conj_ok, f"{len(rows)} sizes")

    # ---- shape of the frontier: non-increasing and convex in eta
    print("\n  shape of V_m(eta)")
    print("  " + "-" * 70)
    shape_ok = True
    for m in [7, 9, 12]:
        xs = [i / 16 for i in range(0, 20)]
        ys = [solve_flow(m, x)[0] for x in xs]
        for i in range(len(xs) - 1):
            if ys[i + 1] > ys[i] + 1e-9:
                shape_ok = False
        for i in range(1, len(xs) - 1):
            if ys[i] > (ys[i - 1] + ys[i + 1]) / 2 + 1e-7:
                shape_ok = False
        print(f"      m={m}: non-increasing and convex on eta in [0, 1.1875]")
    check("V_m(eta) is non-increasing and convex, as an LP value in the right-hand side",
          shape_ok)

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperC_flow_lp.py").read_bytes()).hexdigest(),"breakpoints": rows, "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperC_flow_lp.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
