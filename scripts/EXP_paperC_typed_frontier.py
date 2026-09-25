#!/usr/bin/env python3
"""Paper C, direction C-1/C-3: the ex-ante frontier V_g(eta) of a TWO-MAGNITUDE family (NUMERICAL).

    g = ( a^{n_{+a}}, (-a)^{n_{-a}}, b^{n_{+b}}, (-b)^{n_{-b}} ),   a > b > 0.

Model: the count flow of `typed_flow_equivalence` (LeanPaperCTypedFlowV1).
* States are the prefix compositions v in prod_t [0, n_t] with |v| = k at layer k.
* Flows move one item of one type per layer.
* The band is per type: |E v_t(k)/n_t - k/m| <= eta/m.
* The objective is max over interior budgets 0<k<m of E (|sum_t w_t v_t| - b_k(g)) / ||g||_1,
  with the per-budget optimum b_k(g) = min over compositions u, |u| = k, of |sum_t w_t u_t|.
By the Lean equivalence this LP value IS V_g(eta) over all m! rankings. The solver is floating
point (HiGHS), so every value is NUMERICAL and a cross-check only.

SELF-CHECKS (refuse to write on failure):
* on the paper's family g_m (types -3,-1,1,3), m = 4..9, the LP reproduces the proved closed
  forms: even `even_frontier_all`, odd `odd_frontier`, to 1e-7, on an eta grid;
* at eta >= m the band is vacuous and the LP equals the free value computed without the band;
* V_g(eta) is nonincreasing in eta.

Question answered (and nothing more): for which (a/b, counts) the frontier has one kink,
several kinks, or none, and whether parity of m still decides the free/zero-band gap.
Breakpoints are located by second differences on the eta grid. They are conjectures for the
proof stage, not results.

Usage:
    python -u scripts/EXP_paperC_typed_frontier.py --smoke   # self-checks + 2 families
    python -u scripts/EXP_paperC_typed_frontier.py           # the grid
Output (new file; refuses to overwrite): research/unified_20260919/paperC_typed_frontier.json
(smoke: paperC_typed_frontier_smoke.json)
"""

import hashlib
import itertools
import json
import pathlib
import sys
import time
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

OUTDIR = pathlib.Path("research/unified_20260919")


def baseline(w, n, k):
    """b_k = min over compositions u (sum u = k, u_t <= n_t) of |sum_t w_t u_t|."""
    best = None
    for u in itertools.product(*[range(nt + 1) for nt in n]):
        if sum(u) != k:
            continue
        val = abs(sum(wt * ut for wt, ut in zip(w, u)))
        best = val if best is None or val < best else best
    return best


def frontier_value(w, n, eta, band=True):
    """The flow LP: min t s.t. E_k cost <= t for interior k, band per type."""
    d = len(w)
    m = sum(n)
    D = sum(abs(wt) * nt for wt, nt in zip(w, n))
    layers = []
    for k in range(m + 1):
        layers.append([u for u in itertools.product(*[range(nt + 1) for nt in n]) if sum(u) == k])
    # variables: x_k(v) for every layer and state, f_k(v -> v+e_t), and t
    xi = {}
    idx = 0
    for k, L in enumerate(layers):
        for v in L:
            xi[(k, v)] = idx
            idx += 1
    fi = {}
    for k in range(m):
        for v in layers[k]:
            for t in range(d):
                if v[t] < n[t]:
                    v2 = tuple(v[j] + (1 if j == t else 0) for j in range(d))
                    fi[(k, v, t)] = idx
                    idx += 1
    ti = idx
    nvar = idx + 1
    b = [baseline(w, n, k) for k in range(m + 1)]
    Aeq_rows, beq = [], []
    # start
    row = {xi[(0, layers[0][0])]: 1.0}
    Aeq_rows.append(row); beq.append(1.0)
    for k in range(m):
        for v in layers[k]:
            row = {xi[(k, v)]: -1.0}
            for t in range(d):
                if (k, v, t) in fi:
                    row[fi[(k, v, t)]] = 1.0
            Aeq_rows.append(row); beq.append(0.0)
        for v2 in layers[k + 1]:
            row = {xi[(k + 1, v2)]: -1.0}
            for t in range(d):
                if v2[t] >= 1:
                    v = tuple(v2[j] - (1 if j == t else 0) for j in range(d))
                    if (k, v, t) in fi:
                        row[fi[(k, v, t)]] = 1.0
            Aeq_rows.append(row); beq.append(0.0)
    Aub_rows, bub = [], []
    for k in range(1, m):
        row = {ti: -1.0}
        for v in layers[k]:
            c = (abs(sum(wt * vt for wt, vt in zip(w, v))) - b[k]) / D
            if c != 0:
                row[xi[(k, v)]] = c
        Aub_rows.append(row); bub.append(0.0)
    if band:
        for k in range(m + 1):
            for t in range(d):
                if n[t] == 0:
                    continue
                row = {xi[(k, v)]: v[t] / n[t] for v in layers[k] if v[t] != 0}
                Aub_rows.append(dict(row)); bub.append(k / m + eta / m)
                Aub_rows.append({key: -val for key, val in row.items()}); bub.append(-(k / m - eta / m))

    def mat(rows):
        M = lil_matrix((len(rows), nvar))
        for i, r in enumerate(rows):
            for j, val in r.items():
                M[i, j] = val
        return M.tocsr()
    cobj = np.zeros(nvar); cobj[ti] = 1.0
    res = linprog(cobj, A_ub=mat(Aub_rows), b_ub=np.array(bub), A_eq=mat(Aeq_rows),
                  b_eq=np.array(beq), bounds=[(0, None)] * nvar, method="highs")
    if res.status != 0:
        raise RuntimeError(f"LP failed: {res.message}")
    return res.fun


def family(m):
    p, q = (m - 2 + 1) // 2, (m - 2) // 2
    return [-3, -1, 1, 3], [1, p, q, 1]


def closed_form(m, eta):
    D = m + 4
    free = 2 / (D * (m - 1))
    if m % 2 == 0:
        return max(free, 4 * (1 - eta) / (m * D))
    return max((m + 3 - (m + 1) * eta) / (m * D), free + max(0.0, 1 - eta) / (m * D))


def kinks(etas, vals, tol=1e-7):
    """Grid points where the second difference is nonzero: candidate breakpoints."""
    out = []
    for i in range(1, len(etas) - 1):
        d2 = (vals[i + 1] - vals[i]) - (vals[i] - vals[i - 1])
        if abs(d2) > tol:
            out.append(etas[i])
    return out


def main():
    smoke = "--smoke" in sys.argv
    out = OUTDIR / ("paperC_typed_frontier_smoke.json" if smoke else "paperC_typed_frontier.json")
    if out.exists():
        print(f"refusing to overwrite {out}", file=sys.stderr)
        return 2
    checks = []

    def check(name, ok, detail=""):
        checks.append({"name": name, "ok": bool(ok), "detail": detail})
        print(f"  [{'OK  ' if ok else 'FAIL'}] {name}   {detail}", flush=True)
        return ok

    t0 = time.time()
    # self-check 1: the proved closed forms on g_m
    grid = [i / 20 for i in range(0, 25)]
    worst = 0.0
    for m in (range(4, 8) if smoke else range(4, 10)):
        w, n = family(m)
        for eta in grid:
            v = frontier_value(w, n, eta)
            worst = max(worst, abs(v - closed_form(m, eta)))
        print(f"  family m={m} done [{time.time()-t0:5.0f}s]", flush=True)
    ok1 = check("the LP reproduces even_frontier_all / odd_frontier on g_m", worst < 1e-7,
                f"largest gap {worst:.2e}")
    # self-check 2: eta >= m is the free value
    w, n = family(5)
    ok2 = check("eta = m gives the unbanded value",
                abs(frontier_value(w, n, 5.0) - frontier_value(w, n, 0.0, band=False)) < 1e-9)
    # the exploration
    ratios = [Fr(3, 2), Fr(2), Fr(3), Fr(5)]
    counts = ([(1, 1, 1, 1), (1, 2, 2, 1)] if smoke else
              [c for c in itertools.product(range(0, 3), repeat=4)
               if sum(c) >= 3 and c[0] + c[1] >= 1 and c[2] + c[3] >= 1])
    if smoke:
        ratios = [Fr(3)]
    egrid = [i / 20 for i in range(0, 41)]
    rows = []
    ok3 = True
    for ab in ratios:
        for c in counts:
            w = [float(ab), -float(ab), 1.0, -1.0]
            vals = [frontier_value(w, list(c), e) for e in egrid]
            free = frontier_value(w, list(c), 0.0, band=False)
            ok3 &= all(v2 <= v1 + 1e-9 for v1, v2 in zip(vals, vals[1:]))
            ks = kinks(egrid, vals)
            free_at = next((e for e, v in zip(egrid, vals) if abs(v - free) < 1e-9), None)
            rows.append({"a_over_b": str(ab), "counts_+a_-a_+b_-b": list(c), "m": sum(c),
                         "V0": vals[0], "Vfree": free,
                         "price_V0_over_free": (vals[0] / free) if free > 1e-12 else None,
                         "kinks_on_grid": ks, "free_from_eta": free_at,
                         "values": vals})
        print(f"  a/b={ab} done ({len(counts)} count vectors) [{time.time()-t0:5.0f}s]",
              flush=True)
    check("every frontier is nonincreasing in eta", ok3)
    allok = all(c["ok"] for c in checks)
    if not allok:
        print("self-checks failed; not writing", file=sys.stderr)
        return 1
    rec = {"producer": "scripts/EXP_paperC_typed_frontier.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "model": "count flow of typed_flow_equivalence (LeanPaperCTypedFlowV1); HiGHS floats",
           "status": "NUMERICAL exploration; kinks are grid conjectures, not results",
           "eta_grid": egrid, "rows": rows, "checks": checks, "all_passed": allok,
           "wall_seconds": time.time() - t0}
    out.write_text(json.dumps(rec, indent=1))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
