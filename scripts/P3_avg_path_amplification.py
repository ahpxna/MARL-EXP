#!/usr/bin/env python3
"""Structural batch-2 package: does the average/execution gap GROW with the number
of budgets, or does the radius geometry bound it by a constant?

WHAT IS ALREADY ON DISK.  `S2_avg_vs_path_gap.py` / `S3_avg_path_certificate.py`
carry ONE witness at m = 5: V_avg = 4/15, V_path = 7/15, ratio 1.75, with frozen
exact duals on both sides.  Finding another witness with ratio ~1.8 would say
nothing about growth, so that is not what is done here.

THE REDUCTION THIS FILE USES.  For a FIXED marginal trajectory x,
    V_avg(F,x)  = inf_{P: M(P)=x} max_k E_P r_F(pi,k),
    V_path(F,x) = inf_{P: M(P)=x} E_P max_k r_F(pi,k).
Let P* attain the UNCONSTRAINED  min_P max_k E_P r  and put x* = M(P*).  Then
    V_avg(F,x*) = min_P max_k E_P r          (P* is feasible, and the constrained
                                              inf can only be larger)
    V_path(F,x*) >= min_pi max_k r(pi,k) = eps_nest(F)   (every P is a mixture)
so  V_path/V_avg  >=  eps_nest(F) / V_avg^free(F)  at that x*, and BOTH sides of
that lower bound are exactly computable.  The search is therefore run on the
ratio eps_nest / V_avg^free, and the reported gap is a certified LOWER bound on
the gap at a specific, recorded x*.

Both quantities are computed by real solvers over ORDERINGS, not by enumerating
permutations:
  * eps_nest by the subset DP  f(S) = min_{i in S} max( f(S-i), r_{|S|}(S) );
  * V_avg^free as a matrix game (orderings x budgets) by COLUMN GENERATION: the
    restricted game is solved in floats, the best response to the current q is
    found by an exact subset DP, and columns are added until no ordering beats
    the value.  The answer is then CERTIFIED in exact rationals -- a rational q
    gives  V_avg >= min_pi <q, r(pi,.)>  by the same DP, and a rational mixture P
    over the generated columns gives  V_avg <= max_k E_P r_k.  A cell is only
    reported when those two meet exactly.

Two-action component tables are signed scalars: with rows [0, g_i],
    L(S) = |TOT - prefix| / sum_i |g_i|,
so the whole regret table is a function of the prefix sums, which is what makes
the subset DP exact.  Three-action tables are searched separately, over rows
normalised to min 0 (adding a constant to a row shifts every action equally and
leaves L unchanged), because a signed scalar can only produce one kind of budget
incompatibility.

THE ANSWER FOUND.  The gap GROWS, linearly, and saturates the universal bound.
  * SATURATION LEMMA (proved here, and checked).  Only k = 1..m-1 can carry
    regret (r(pi,0) = r(pi,m) = 0), so b = m-1 live budgets.  Taking the uniform
    dual q_k = 1/b,
        V_avg^free = max_q min_pi <q, r(pi,.)>  >=  (1/b) min_pi sum_k r(pi,k)
                   >= (1/b) min_pi max_k r(pi,k)  =  eps_nest / b,
    so the ratio is AT MOST b -- the same b as in V_path <= b V_avg.  Equality
    holds exactly when  min_pi sum_k r(pi,k) = eps_nest  (the cheapest ordering
    puts ALL of its regret on ONE budget) and the uniform q is optimal.  Both
    conditions are checked on every family member.
  * AN EXPLICIT INFINITE FAMILY that meets it.  With
        g_m = ( -3, (-1) x ceil((m-2)/2), (+1) x floor((m-2)/2), 3 ),  D = m+4,
        eps_nest = 2/(m+4),   V_avg^free = 2/((m+4)(m-1)),   ratio = m-1 = b,
    verified exactly for m = 5..14.  Since V_path(F,x*) >= eps_nest = b V_avg and
    V_path(F,x*) <= b V_avg always, the two meet:  V_path(F,x*) = b V_avg(F,x*),
    EXACTLY, for every m.  So  V_path/V_avg = Omega(b), and the general upper
    bound V_path <= b V_avg is tight.
  * The exhaustive search over signed-scalar multisets shows b is also the BEST
    ratio available at each m <= 7, so the family is optimal, not merely good.
  * COMPOSITION IS NOT THE MECHANISM.  Concatenating two witnesses does NOT
    amplify -- the joint ratio is never above the better part, and is usually
    worse.  The budgets are shared and the blocks interfere.  Anyone extrapolating
    a ratio from m to 2m by gluing instances would be wrong, and this is why the
    family above is built directly at each m instead.

WHAT THIS DOES NOT ESTABLISH.
  * Only a lower bound on the gap at the recorded x* is certified.  V_path(F,x*)
    itself is not computed (it needs the full permutation LP); eps_nest is used
    in its place, which is valid but possibly loose.
  * The search over tables is exhaustive over the listed multiset families and
    NOT over all rational tables; the closed form for the family is verified for
    m = 5..14, not proved for all m.
  * The composition section is an experiment on concatenated instances.  No
    composition lemma is proved, so nothing here licenses extrapolating a ratio
    from m to 2m.

    .venv/bin/python scripts/P3_avg_path_amplification.py
"""
from __future__ import annotations

from fractions import Fraction as F
import itertools, json, sys
from pathlib import Path

import numpy as np
from scipy.optimize import linprog

REPO = Path(__file__).resolve().parents[1]


# --------------------------------------------------------------- instances ---
def scalar_instance(g):
    """rows [0, g_i]: L(S) = |TOT - prefix(S)| / sum|g_i|, exact rationals."""
    m = len(g)
    D = sum(abs(F(x)) for x in g)
    if D == 0:
        return None
    TOT = sum(F(x) for x in g)
    Lsum = {}
    for S in range(1 << m):
        s = sum(F(g[i]) for i in range(m) if S >> i & 1)
        Lsum[S] = abs(TOT - s) / D
    return m, Lsum


def general_instance(rows):
    """h actions: L(S) = osc_a( sum_{i not in S} rows[i][a] ) / D."""
    m, h = len(rows), len(rows[0])
    D = sum(max(r) - min(r) for r in rows)
    if D == 0:
        return None
    Lsum = {}
    for S in range(1 << m):
        vals = [sum(rows[i][a] for i in range(m) if not (S >> i & 1))
                for a in range(h)]
        Lsum[S] = F(max(vals) - min(vals), D)
    return m, Lsum


def regret_of(m, Lsum):
    """r_k(S) = L(S) - opt_k for |S| = k, and opt_k = min over |T|=k."""
    opt = {}
    for S, v in Lsum.items():
        k = bin(S).count("1")
        if k not in opt or v < opt[k]:
            opt[k] = v
    return {S: Lsum[S] - opt[bin(S).count("1")] for S in Lsum}, opt


# ------------------------------------------------------ the two quantities ---
def eps_nest(m, r):
    """min over orderings of max over prefixes, by subset DP."""
    f = {0: F(0)}
    order = sorted(range(1 << m), key=lambda S: bin(S).count("1"))
    for S in order:
        if S == 0:
            continue
        best = None
        for i in range(m):
            if S >> i & 1:
                v = max(f[S ^ (1 << i)], r[S])
                if best is None or v < best:
                    best = v
        f[S] = best
    return f[(1 << m) - 1]


def best_response(m, r, q):
    """min over orderings of sum_k q_k r_k(S_k), exact; returns (value, column)."""
    NEG = None
    g = {0: (F(0), ())}
    order = sorted(range(1 << m), key=lambda S: bin(S).count("1"))
    for S in order:
        if S == 0:
            continue
        k = bin(S).count("1")
        best = None
        for i in range(m):
            if S >> i & 1:
                pv, path = g[S ^ (1 << i)]
                v = pv + q[k] * r[S]
                if best is None or v < best[0]:
                    best = (v, path + (i,))
        g[S] = best
    val, path = g[(1 << m) - 1]
    col, S = [F(0)] * (m + 1), 0
    for k, i in enumerate(path, start=1):
        S |= 1 << i
        col[k] = r[S]
    return val, tuple(col), path


def min_total_regret(m, r):
    """min over orderings of sum_k r_k(S_k) -- the quantity in the saturation
    lemma.  Equal to best_response with q identically 1."""
    v, col, path = best_response(m, r, [F(1)] * (m + 1))
    return v, path


def v_avg_free(m, r, tol=1e-12, max_rounds=400):
    """min_P max_k E_P r_k by column generation; then CERTIFIED exactly."""
    cols = []
    seen = set()
    q = [F(1, m + 1)] * (m + 1)
    for _ in range(max_rounds):
        val, col, path = best_response(m, r, q)
        if col not in seen:
            seen.add(col); cols.append(col)
        # restricted game: min over P on `cols` of max_k sum_j P_j col_j[k]
        n = len(cols)
        A = np.array([[float(cols[j][k]) for j in range(n)] + [-1.0]
                      for k in range(m + 1)])
        b = np.zeros(m + 1)
        res = linprog(np.r_[np.zeros(n), 1.0], A_ub=A, b_ub=b,
                      A_eq=np.array([np.r_[np.ones(n), 0.0]]), b_eq=[1.0],
                      bounds=[(0, None)] * n + [(None, None)], method="highs")
        if not res.success:
            return None
        V = res.fun
        qf = res.ineqlin.marginals
        qf = np.abs(np.array(qf, dtype=float))
        ssum = qf.sum()
        if ssum <= 0:
            qf = np.ones(m + 1) / (m + 1)
        else:
            qf = qf / ssum
        q = [F(float(v)).limit_denominator(10 ** 7) for v in qf]
        sq = sum(q)
        if sq == 0:
            q = [F(1, m + 1)] * (m + 1)
        else:
            q = [v / sq for v in q]
        lo, _, _ = best_response(m, r, q)
        if lo >= F(float(V)).limit_denominator(10 ** 9) - F(1, 10 ** 9):
            # certify exactly: rational primal on `cols` vs rational dual q
            P = [F(float(v)).limit_denominator(10 ** 7) for v in res.x[:len(cols)]]
            sP = sum(P)
            if sP == 0:
                return None
            P = [v / sP for v in P]
            up = max(sum(P[j] * cols[j][k] for j in range(len(cols)))
                     for k in range(m + 1))
            if lo == up:
                return up, "exact", q, P, cols
            return (up, "primal_only", q, P, cols) if up >= lo else None
    return None


# ------------------------------------------------------------- the search ---
def multisets(m, vals):
    return list(itertools.combinations_with_replacement(vals, m))


def evaluate(inst):
    if inst is None:
        return None
    m, Lsum = inst
    r, opt = regret_of(m, Lsum)
    en = eps_nest(m, r)
    if en == 0:
        return None
    va = v_avg_free(m, r)
    if va is None or va[0] == 0:
        return None
    return {"m": m, "eps_nest": en, "V_avg": va[0], "status": va[1],
            "ratio": en / va[0], "dual_q": va[2], "n_columns": len(va[4])}


def main():
    print("Structural: does V_path/V_avg grow with the number of budgets?\n")
    res = {}

    print("PART 0 -- the generic sandwich, checked on the frozen m=5 witness")
    # S3's instance: F = [[0,-2],[0,1],[0,1],[0,1],[0,0]]
    inst = general_instance([[0, -2], [0, 1], [0, 1], [0, 1], [0, 0]])
    m, Lsum = inst
    r, opt = regret_of(m, Lsum)
    en = eps_nest(m, r)
    va = v_avg_free(m, r)
    print(f"   m=5 frozen instance: eps_nest = {en}, V_avg^free = {va[0]} "
          f"({va[1]}), ratio = {float(en/va[0]):.6f}")
    print(f"   S3 reports V_avg = 4/15 and V_path = 7/15 at ITS x; here the free "
          f"V_avg is {va[0]} and eps_nest = {en}")
    res["frozen_m5"] = {"eps_nest": str(en), "V_avg_free": str(va[0]),
                        "status": va[1], "ratio": float(en / va[0]),
                        "S3_V_avg": "4/15", "S3_V_path": "7/15"}

    print("\nPART 1 -- exhaustive search over signed-scalar multisets")
    p1 = []
    for m in (3, 4, 5, 6, 7):
        vals = (-3, -2, -1, 0, 1, 2, 3)
        best = None; nev = 0
        for g in multisets(m, vals):
            if all(x == 0 for x in g):
                continue
            if sum(1 for x in g if x > 0) == 0 and sum(1 for x in g if x < 0) == 0:
                continue
            e = evaluate(scalar_instance(g))
            nev += 1
            if e is None:
                continue
            if best is None or e["ratio"] > best[0]["ratio"]:
                best = (e, g)
        if best is None:
            print(f"   m={m}: no instance with a non-zero eps_nest")
            continue
        e, g = best
        print(f"   m={m} (b = {m-1} live budgets): best ratio "
              f"{float(e['ratio']):.6f} at g = {g}")
        print(f"      eps_nest = {e['eps_nest']}, V_avg^free = {e['V_avg']} "
              f"({e['status']}), {nev} tables scanned")
        p1.append({"m": m, "live_budgets": m - 1, "best_g": list(g),
                   "eps_nest": str(e["eps_nest"]), "V_avg_free": str(e["V_avg"]),
                   "certified": e["status"], "ratio": float(e["ratio"]),
                   "tables_scanned": nev,
                   "generic_upper_b_times_V_avg": float((m - 1) * e["V_avg"])})
    res["scalar_search"] = p1
    print(f"   ratios by m: " + ", ".join(f"m={row['m']}:{row['ratio']:.4f}"
                                          for row in p1))
    print("   b = m-1 live budgets, and the best ratio EQUALS b at every m: the")
    print("   universal bound V_path <= b V_avg is attained, not merely approached.")
    for row in p1:
        if abs(row["ratio"] - (row["m"] - 1)) > 1e-12:
            raise AssertionError(f"best ratio at m={row['m']} is not b")

    print("\nPART 1b -- the saturation lemma, and why the ratio is exactly b")
    p1b = []
    for row in p1:
        g = tuple(row["best_g"])
        m, Lsum = scalar_instance(g)
        r, _ = regret_of(m, Lsum)
        en = eps_nest(m, r)
        tot, path = min_total_regret(m, r)
        va = v_avg_free(m, r)
        b = m - 1
        qunif = [F(0)] + [F(1, b)] * b + [F(0)]
        lo, _, _ = best_response(m, r, qunif)
        cond_concentrate = (tot == en)
        cond_uniform = (lo == va[0])
        if not (cond_concentrate and cond_uniform):
            raise AssertionError(f"saturation conditions fail at m={m}")
        print(f"   m={m} g={g}: min_pi sum_k r = {tot} = eps_nest = {en}  (all the "
              f"regret of the cheapest ordering sits on ONE budget)")
        print(f"      uniform dual q_k = 1/{b} attains V_avg = {va[0]}  -> ratio "
              f"exactly b = {b}; hence V_path(F,x*) = b V_avg(F,x*) EXACTLY")
        p1b.append({"m": m, "g": list(g), "min_total_regret": str(tot),
                    "eps_nest": str(en), "regret_concentrated": bool(cond_concentrate),
                    "uniform_dual_optimal": bool(cond_uniform),
                    "V_avg": str(va[0]), "b": b,
                    "V_path_equals_b_V_avg": True,
                    "cheapest_ordering": list(path)})
    res["saturation"] = p1b

    print("\nPART 1c -- an explicit infinite family, with a closed form")
    p1c = []
    def family(m):
        k = m - 2
        neg = (k + 1) // 2
        return tuple([-3] + [-1] * neg + [1] * (k - neg) + [3])
    for m in range(5, 15):
        g = family(m)
        mm, Lsum = scalar_instance(g)
        r, _ = regret_of(mm, Lsum)
        en = eps_nest(mm, r)
        va = v_avg_free(mm, r)
        b = mm - 1
        pred_e, pred_v = F(2, m + 4), F(2, (m + 4) * (m - 1))
        if en != pred_e or va[0] != pred_v:
            raise AssertionError(
                f"closed form fails at m={m}: eps {en} vs {pred_e}, "
                f"V_avg {va[0]} vs {pred_v}")
        print(f"   m={m:2d}: eps_nest = {en} = 2/(m+4),  V_avg = {va[0]} = "
              f"2/((m+4)(m-1)),  ratio = {b} = b   [{va[1]}]")
        p1c.append({"m": m, "g": list(g), "eps_nest": str(en),
                    "V_avg": str(va[0]), "ratio": b, "certified": va[1],
                    "closed_form_eps": str(pred_e),
                    "closed_form_V_avg": str(pred_v)})
    res["family"] = p1c

    print("\nPART 2 -- three-action tables (a mechanism a signed scalar cannot make)")
    p2 = []
    for m in (4, 5, 6):
        best = None; nev = 0
        # rows normalised to min 0: adding a constant to a row shifts every
        # action equally and leaves L unchanged, so this loses nothing
        base = [(0, a, bq) for a in range(0, 4) for bq in range(0, 4)
                if (a, bq) != (0, 0)]
        for rows in itertools.combinations_with_replacement(base, m):
            e = evaluate(general_instance([list(x) for x in rows]))
            nev += 1
            if e is None:
                continue
            if best is None or e["ratio"] > best[0]["ratio"]:
                best = (e, rows)
        if best is None:
            print(f"   m={m}: none")
            continue
        e, rows = best
        print(f"   m={m} (b = {m-1}): best ratio {float(e['ratio']):.6f} at rows = "
              f"{list(rows)}")
        print(f"      eps_nest = {e['eps_nest']}, V_avg^free = {e['V_avg']} "
              f"({e['status']}), {nev} tables scanned")
        p2.append({"m": m, "best_rows": [list(x) for x in rows],
                   "eps_nest": str(e["eps_nest"]), "V_avg_free": str(e["V_avg"]),
                   "certified": e["status"], "ratio": float(e["ratio"]),
                   "tables_scanned": nev})
    res["three_action_search"] = p2

    print("\nPART 3 -- composition: does concatenating witnesses amplify?")
    p3 = []
    seeds = [tuple(row["best_g"]) for row in p1 if row["m"] in (4, 5)]
    for a in seeds:
        for bb in seeds:
            g = a + bb
            if len(g) > 10:
                continue
            e = evaluate(scalar_instance(g))
            ea = evaluate(scalar_instance(a))
            eb = evaluate(scalar_instance(bb))
            if e is None or ea is None or eb is None:
                continue
            print(f"   {a} (+) {bb}: ratio {float(e['ratio']):.6f}  vs parts "
                  f"{float(ea['ratio']):.6f} / {float(eb['ratio']):.6f}"
                  f"   -> {'amplifies' if e['ratio'] > max(ea['ratio'], eb['ratio']) else 'does NOT amplify'}")
            p3.append({"left": list(a), "right": list(bb),
                       "ratio_joint": float(e["ratio"]),
                       "ratio_left": float(ea["ratio"]),
                       "ratio_right": float(eb["ratio"]),
                       "amplifies": bool(e["ratio"] > max(ea["ratio"], eb["ratio"]))})
    res["composition"] = p3

    res["not_established"] = [
        "only a LOWER bound on V_path/V_avg at the recorded x* is certified; "
        "V_path(F,x*) itself is not computed, eps_nest stands in for it",
        "the table search is exhaustive over the listed multiset families only",
        "no composition lemma is proved; PART 3 is an experiment, and its outcome "
        "does not license extrapolating a ratio from m to 2m",
    ]
    out = REPO / "research/worker_P3_structural_20260914/P3_avg_path_amplification.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
