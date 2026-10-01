#!/usr/bin/env python3
"""Paper C: the value of knowing the budget, and the value of R exchanges (NUMERICAL).

Questions (and nothing more):
* A_g(eta) = U_g(eta) - B_g(eta): where does knowing the budget start to help on g_m and on the
  two-magnitude families, beyond the ranges where Lean proves A = 0?
* V_g^(R)(eta): how many exchanges after the budget is revealed reach B_g?

Models.
* U_g: the count-flow LP of `typed_flow_equivalence` (LeanPaperCTypedFlowV1), solved by
  `frontier_value` of scripts/EXP_paperC_typed_frontier.py.
* B_g: per budget k, a law on count vectors of size k with the type-marginal band
  (LeanPaperCBudgetAwareV1.SubFeasible, symmetrised within types), maximised over k.
* V_g^(R): the count flow of U_g plus, at each interior budget, a transport z_k(v, u) from the
  base count vector v to a final count vector u with |v - u|_1 / 2 <= R, the band on the final
  law, and the regret of the final law. The lift of a count transport to item exchanges
  (uniform relabelling within types) is NOT formalized; these values are for the typed model.
Solver: HiGHS through scipy. Floating point: every value is NUMERICAL.

SELF-CHECKS (refuse to write on failure), each a transcription of a compiled Lean theorem:
* g = (a,-a,b,-b): B = c max((1-eta)/2, 0) (aware_twoMag), U = c max((1-eta)/2, 1/3)
  (twoMag_frontier), V^(1) = B (recourse_one_twoMag), V^(0) = U (recourse_zero), with
  c = (a-b)/(2(a+b)).
* g_m, even m, 0 <= eta <= (m-2)/(2(m-1)): B = U = 4(1-eta)/(m(m+4)) (aware_even).
* g_m, odd m, 0 <= eta <= 1 - 2/(m(m-1)): B = U = (m+3-(m+1)eta)/(m(m+4)) (aware_odd).
* B <= V^(R+1) <= V^(R) <= U (aware_le_recourse, recourse_mono, recourse_le_true), and
  V^(floor(m/2)) = B (recourse_full).

Usage:
    python -u scripts/EXP_paperC_budget_recourse.py --smoke
    python -u scripts/EXP_paperC_budget_recourse.py
Output (new file; refuses to overwrite): research/unified_20260919/paperC_budget_recourse.json
(smoke: paperC_budget_recourse_smoke.json)
"""

import hashlib
import importlib.util
import itertools
import json
import pathlib
import sys
import time

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("typed_frontier", HERE / "EXP_paperC_typed_frontier.py")
tf = importlib.util.module_from_spec(spec)
spec.loader.exec_module(tf)

OUTDIR = pathlib.Path("research/unified_20260919")
TOL = 1e-7


def layers_of(n):
    m = sum(n)
    return [[u for u in itertools.product(*[range(nt + 1) for nt in n]) if sum(u) == k]
            for k in range(m + 1)]


def cost(w, v, bk, D):
    return (abs(sum(wt * vt for wt, vt in zip(w, v))) - bk) / D


def aware_value(w, n, eta):
    """B_g(eta) = max over interior k of the layer LP."""
    m = sum(n)
    D = sum(abs(wt) * nt for wt, nt in zip(w, n))
    L = layers_of(n)
    best = 0.0
    per = []
    for k in range(1, m):
        V = L[k]
        bk = tf.baseline(w, n, k)
        c = np.array([cost(w, v, bk, D) for v in V])
        Aeq = np.ones((1, len(V)))
        rows, rhs = [], []
        for t in range(len(n)):
            if n[t] == 0:
                continue
            r = np.array([v[t] / n[t] for v in V])
            rows.append(r); rhs.append(k / m + eta / m)
            rows.append(-r); rhs.append(-(k / m - eta / m))
        res = linprog(c, A_ub=np.array(rows), b_ub=np.array(rhs), A_eq=Aeq, b_eq=[1.0],
                      bounds=[(0, None)] * len(V), method="highs")
        if res.status != 0:
            raise RuntimeError(f"layer LP failed at k={k}: {res.message}")
        per.append(res.fun)
        best = max(best, res.fun)
    return best, per


def recourse_value(w, n, eta, R):
    """V_g^(R)(eta) on the typed model: base count flow with the band, then a transport of
    radius R at each interior budget, the band and the regret on the final law."""
    d = len(w)
    m = sum(n)
    D = sum(abs(wt) * nt for wt, nt in zip(w, n))
    L = layers_of(n)
    b = [tf.baseline(w, n, k) for k in range(m + 1)]
    idx = 0
    xi, fi, zi = {}, {}, {}
    for k, Lk in enumerate(L):
        for v in Lk:
            xi[(k, v)] = idx; idx += 1
    for k in range(m):
        for v in L[k]:
            for t in range(d):
                if v[t] < n[t]:
                    fi[(k, v, t)] = idx; idx += 1
    for k in range(1, m):
        for v in L[k]:
            for u in L[k]:
                if sum(abs(a - c) for a, c in zip(v, u)) // 2 <= R:
                    zi[(k, v, u)] = idx; idx += 1
    ti = idx
    nvar = idx + 1
    Aeq, beq, Aub, bub = [], [], [], []
    Aeq.append({xi[(0, L[0][0])]: 1.0}); beq.append(1.0)
    for k in range(m):
        for v in L[k]:
            row = {xi[(k, v)]: -1.0}
            for t in range(d):
                if (k, v, t) in fi:
                    row[fi[(k, v, t)]] = 1.0
            Aeq.append(row); beq.append(0.0)
        for v2 in L[k + 1]:
            row = {xi[(k + 1, v2)]: -1.0}
            for t in range(d):
                if v2[t] >= 1:
                    v = tuple(v2[j] - (1 if j == t else 0) for j in range(d))
                    if (k, v, t) in fi:
                        row[fi[(k, v, t)]] = 1.0
            Aeq.append(row); beq.append(0.0)
    # base band at every budget
    for k in range(m + 1):
        for t in range(d):
            if n[t] == 0:
                continue
            row = {xi[(k, v)]: v[t] / n[t] for v in L[k] if v[t] != 0}
            Aub.append(dict(row)); bub.append(k / m + eta / m)
            Aub.append({a: -c for a, c in row.items()}); bub.append(-(k / m - eta / m))
    for k in range(1, m):
        # transport marginals
        for v in L[k]:
            row = {xi[(k, v)]: -1.0}
            for u in L[k]:
                if (k, v, u) in zi:
                    row[zi[(k, v, u)]] = 1.0
            Aeq.append(row); beq.append(0.0)
        # final band
        for t in range(d):
            if n[t] == 0:
                continue
            row = {}
            for (kk, v, u), j in zi.items():
                if kk == k and u[t] != 0:
                    row[j] = u[t] / n[t]
            Aub.append(dict(row)); bub.append(k / m + eta / m)
            Aub.append({a: -c for a, c in row.items()}); bub.append(-(k / m - eta / m))
        # final regret
        row = {ti: -1.0}
        for (kk, v, u), j in zi.items():
            if kk == k:
                c = cost(w, u, b[k], D)
                if c != 0:
                    row[j] = c
        Aub.append(row); bub.append(0.0)

    def mat(rows):
        M = lil_matrix((len(rows), nvar))
        for i, r in enumerate(rows):
            for j, val in r.items():
                M[i, j] = val
        return M.tocsr()
    cobj = np.zeros(nvar); cobj[ti] = 1.0
    res = linprog(cobj, A_ub=mat(Aub), b_ub=np.array(bub), A_eq=mat(Aeq), b_eq=np.array(beq),
                  bounds=[(0, None)] * nvar, method="highs")
    if res.status != 0:
        raise RuntimeError(f"recourse LP failed: {res.message}")
    return res.fun


def main():
    smoke = "--smoke" in sys.argv
    out = OUTDIR / ("paperC_budget_recourse_smoke.json" if smoke else "paperC_budget_recourse.json")
    if out.exists():
        print(f"refusing to overwrite {out}", file=sys.stderr)
        return 2
    checks = []

    def check(name, ok, detail=""):
        checks.append({"name": name, "ok": bool(ok), "detail": detail})
        print(f"  [{'OK  ' if ok else 'FAIL'}] {name}   {detail}", flush=True)
        return ok

    t0 = time.time()
    etas = [round(0.05 * i, 4) for i in range(0, 25)] if smoke else \
        [round(0.01 * i, 4) for i in range(0, 121)]
    ratios = [2.0, 3.0] if smoke else [1.5, 2.0, 2.6, 3.0, 5.0]
    ms = [4, 5] if smoke else [4, 5, 6, 7, 8, 9, 10]

    # 1. the four-item family
    four = {}
    worst = 0.0
    for r in ratios:
        w, n = [r, -r, 1.0, -1.0], [1, 1, 1, 1]
        c = (r - 1) / (2 * (r + 1))
        rows = []
        for eta in etas:
            B, _ = aware_value(w, n, eta)
            U = tf.frontier_value(w, n, eta)
            V1 = recourse_value(w, n, eta, 1)
            V0 = recourse_value(w, n, eta, 0)
            eB = abs(B - c * max((1 - eta) / 2, 0))
            eU = abs(U - c * max((1 - eta) / 2, 1 / 3))
            worst = max(worst, eB, eU, abs(V1 - B), abs(V0 - U))
            rows.append({"eta": eta, "U": U, "B": B, "V0": V0, "V1": V1})
        four[str(r)] = rows
        print(f"  four-item a/b={r} done ({time.time()-t0:.0f}s)", flush=True)
    check("four-item: B, U, V1 = B, V0 = U match the Lean formulas", worst < 1e-7,
          f"max err {worst:.2e}")

    # 2. g_m: B vs U, and the first eta with a positive gap
    gm = {}
    worst_even, worst_odd, worst_mono, worst_full = 0.0, 0.0, 0.0, 0.0
    for m in ms:
        w, n = tf.family(m)
        thr = (m - 2) / (2 * (m - 1)) if m % 2 == 0 else 1 - 2 / (m * (m - 1))
        rows, first_gap = [], None
        Rs = list(range(0, m // 2 + 1))
        for eta in etas:
            B, per = aware_value(w, n, eta)
            U = tf.frontier_value(w, n, eta)
            V = {R: recourse_value(w, n, eta, R) for R in Rs}
            if eta <= thr + 1e-12:
                closed = 4 * (1 - eta) / (m * (m + 4)) if m % 2 == 0 else \
                    (m + 3 - (m + 1) * eta) / (m * (m + 4))
                err = max(abs(B - closed), abs(U - closed))
                if m % 2 == 0:
                    worst_even = max(worst_even, err)
                else:
                    worst_odd = max(worst_odd, err)
            chain = [B] + [V[R] for R in reversed(Rs)] + [U]
            for x, y in zip(chain, chain[1:]):
                worst_mono = max(worst_mono, x - y)
            worst_full = max(worst_full, abs(V[m // 2] - B))
            if first_gap is None and U - B > 1e-6:
                first_gap = eta
            Rmin = next((R for R in Rs if V[R] - B <= 1e-7), None)
            rows.append({"eta": eta, "U": U, "B": B, "layers": per,
                         "V": {str(R): V[R] for R in Rs}, "Rmin": Rmin})
        gm[str(m)] = {"threshold_proved": thr, "first_gap_eta": first_gap, "rows": rows}
        print(f"  g_{m}: proved zero gap up to {thr:.4f}, first gap on grid at {first_gap} "
              f"({time.time()-t0:.0f}s)", flush=True)
    check("g_m even: B = U = 4(1-eta)/(mD) on the proved range", worst_even < 1e-7,
          f"max err {worst_even:.2e}")
    check("g_m odd: B = U = (m+3-(m+1)eta)/(mD) on the proved range", worst_odd < 1e-7,
          f"max err {worst_odd:.2e}")
    check("B <= V(R+1) <= V(R) <= U", worst_mono < 1e-7, f"max violation {worst_mono:.2e}")
    check("V(floor(m/2)) = B", worst_full < 1e-7, f"max err {worst_full:.2e}")

    # 3. two-magnitude families with repeated types
    rep = {}
    for counts in ([1, 1, 2, 2], [2, 2, 2, 2]):
        for r in ratios:
            w = [r, -r, 1.0, -1.0]
            m = sum(counts)
            Rs = list(range(0, m // 2 + 1))
            rows = []
            for eta in etas:
                B, per = aware_value(w, counts, eta)
                U = tf.frontier_value(w, counts, eta)
                V = {R: recourse_value(w, counts, eta, R) for R in Rs}
                chain = [B] + [V[R] for R in reversed(Rs)] + [U]
                for x, y in zip(chain, chain[1:]):
                    worst_mono = max(worst_mono, x - y)
                Rmin = next((R for R in Rs if V[R] - B <= 1e-7), None)
                rows.append({"eta": eta, "U": U, "B": B, "V": {str(R): V[R] for R in Rs},
                             "Rmin": Rmin})
            rep[f"{tuple(counts)}@{r}"] = rows
            print(f"  counts {counts} a/b={r} done ({time.time()-t0:.0f}s)", flush=True)
    check("repeated types: B <= V(R+1) <= V(R) <= U", worst_mono < 1e-7,
          f"max violation {worst_mono:.2e}")

    if not all(c["ok"] for c in checks):
        print("SELF-CHECK FAILED; refusing to write", file=sys.stderr)
        return 1
    rec = {"producer": "scripts/EXP_paperC_budget_recourse.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "solver_source_sha256": hashlib.sha256((HERE / "EXP_paperC_typed_frontier.py").read_bytes()).hexdigest(),
           "status": "NUMERICAL (HiGHS); recourse values are for the typed model",
           "eta_grid": etas, "checks": checks, "four_item": four, "g_m": gm, "repeated": rep,
           "seconds": time.time() - t0}
    out.write_text(json.dumps(rec, indent=1))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
