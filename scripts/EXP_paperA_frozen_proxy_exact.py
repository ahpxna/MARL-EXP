#!/usr/bin/env python3
"""Paper A, the two heteroscedastic families, certified in EXACT rational arithmetic.

`EXP_paperA_frozen_proxy.py` computes `J_full` as a minimum over the 81 extremum-assignment
regions and certifies each region by a FLOATING-POINT KKT check.  This script repeats the same
computation with every region settled exactly.

Each region is `min (1/2) sum_i (x_i - theta_i)^2 / var_i` over a polyhedron `A x <= b`.
The quadratic is strictly convex (all variances positive) and every region is feasible (a
constant vector satisfies every constraint with equality), so each region has a unique
minimiser, and the KKT conditions are necessary and sufficient
(`LeanPaperAOracleCertificateV1.kkt_region_minimum` proves sufficiency).

EXACT CERTIFICATE, per region.  A set `S` of constraint rows that is linearly independent
(checked by exact row reduction) defines the candidate

    mu_S = (A_S V A_S^T)^{-1} (A_S theta - b_S),    x_S = theta - V A_S^T mu_S,    V = diag(var).

`S` certifies the region when, in exact rationals, `mu_S >= 0`, every constraint holds at
`x_S`, and complementary slackness holds (the rows of `S` are tight by construction).  The
float solution proposes `S` (its active set, reduced to an independent subset); if that does
not certify, every independent subset of the region's rows is tried.  A region with no
certifying subset would be UNRESOLVED and fail the self-check.  None is.

J_frozen is exact by its closed form `gap^2 / (2 (sum of the four cells' variances))`.

SELF-CHECKS: all 81 regions of both families certify exactly at every M; `J_frozen` equals its
closed forms `1/128` (family 1) and `1/(8(M+3))` (family 2); family 1's ratio is at most
`16/M`; family 2's ratio is at least `(M+3)/24`; family 2's `J_full >= 1/192`; and every exact
value agrees with the floating-point artifact `paperA_frozen_proxy.json` to 1e-9.

Output (new file; refuses to overwrite): research/unified_20260919/paperA_frozen_proxy_exact.json
"""

import hashlib
import json
import pathlib
import sys
from fractions import Fraction as Fr
from itertools import combinations, product

import numpy as np

sys.path.insert(0, "scripts")
import EXP_paperA_frozen_proxy as P  # noqa: E402  (float solver, reused only to propose S)

OUT = pathlib.Path("research/unified_20260919/paperA_frozen_proxy_exact.json")
FLOAT_IN = pathlib.Path("research/unified_20260919/paperA_frozen_proxy.json")
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""), flush=True)
    return ok


def region_rows(nA, nB, iM, im, jM, jm):
    """The same rows as `P.region_constraints`, as exact integer vectors (rhs 0)."""
    n = nA + nB
    rows = []
    for i in range(nA):
        if i != iM:
            r = [0] * n; r[i] += 1; r[iM] -= 1; rows.append(r)
    for i in range(nA):
        if i != im:
            r = [0] * n; r[im] += 1; r[i] -= 1; rows.append(r)
    for j in range(nB):
        if j != jM:
            r = [0] * n; r[nA + j] += 1; r[nA + jM] -= 1; rows.append(r)
    for j in range(nB):
        if j != jm:
            r = [0] * n; r[nA + jm] += 1; r[nA + j] -= 1; rows.append(r)
    r = [0] * n
    r[iM] += 1; r[im] -= 1; r[nA + jM] -= 1; r[nA + jm] += 1
    rows.append(r)
    return [[Fr(x) for x in row] for row in rows]


def rank(rows):
    m = [row[:] for row in rows]
    rk, ncol = 0, (len(m[0]) if m else 0)
    for c in range(ncol):
        piv = next((i for i in range(rk, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[rk], m[piv] = m[piv], m[rk]
        for i in range(len(m)):
            if i != rk and m[i][c] != 0:
                f = m[i][c] / m[rk][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[rk])]
        rk += 1
    return rk


def solve(Mx, rhs):
    """Exact Gauss-Jordan solve of a nonsingular square system."""
    n = len(Mx)
    a = [row[:] + [rhs[i]] for i, row in enumerate(Mx)]
    for c in range(n):
        piv = next(i for i in range(c, n) if a[i][c] != 0)
        a[c], a[piv] = a[piv], a[c]
        pv = a[c][c]
        a[c] = [x / pv for x in a[c]]
        for i in range(n):
            if i != c and a[i][c] != 0:
                f = a[i][c]
                a[i] = [x - f * y for x, y in zip(a[i], a[c])]
    return [a[i][n] for i in range(n)]


def candidate(rows, S, theta, var):
    """The KKT candidate for the independent active set `S` (all rhs are 0)."""
    n = len(theta)
    AS = [rows[k] for k in S]
    if not AS:
        return theta[:], []
    G = [[sum(AS[p][i] * var[i] * AS[q][i] for i in range(n)) for q in range(len(S))]
         for p in range(len(S))]
    rhs = [sum(AS[p][i] * theta[i] for i in range(n)) for p in range(len(S))]
    mu = solve(G, rhs)
    x = [theta[i] - var[i] * sum(AS[p][i] * mu[p] for p in range(len(S))) for i in range(n)]
    return x, mu


def certifies(rows, S, theta, var):
    x, mu = candidate(rows, S, theta, var)
    if any(m < 0 for m in mu):
        return None
    if any(sum(r[i] * x[i] for i in range(len(x))) > 0 for r in rows):
        return None
    val = sum((x[i] - theta[i]) ** 2 / (2 * var[i]) for i in range(len(x)))
    return {"x": x, "mu": mu, "S": list(S), "value": val}


def independent_subset(rows, idx):
    chosen = []
    for k in idx:
        if rank([rows[j] for j in chosen + [k]]) == len(chosen) + 1:
            chosen.append(k)
    return chosen


def settle_region(theta_f, var_f, theta, var, reg):
    nA = nB = 3
    rows = region_rows(nA, nB, *reg)
    # the float solver proposes the active set
    Amat, bvec = P.region_constraints(nA, nB, *reg)
    Hdiag = 1.0 / np.array(var_f)
    res = P.solve_region(np.array(theta_f), Hdiag, Amat, bvec)
    tried = 0
    if res is not None:
        slack = bvec - Amat @ res.x
        act = [int(k) for k in np.where(slack < 1e-7)[0]]
        S = independent_subset(rows, act)
        tried += 1
        c = certifies(rows, S, theta, var)
        if c is not None:
            c["route"] = "float-proposed"
            c["tried"] = tried
            return c
    # exact fallback: every independent subset
    for size in range(0, 7):
        for S in combinations(range(len(rows)), size):
            if rank([rows[k] for k in S]) != size:
                continue
            tried += 1
            c = certifies(rows, S, theta, var)
            if c is not None:
                c["route"] = "exact-search"
                c["tried"] = tried
                return c
    return None


def J_frozen_exact(a, b, varA, varB):
    iM = max(range(3), key=lambda i: a[i]); im = min(range(3), key=lambda i: a[i])
    jM = max(range(3), key=lambda j: b[j]); jm = min(range(3), key=lambda j: b[j])
    gap = (a[iM] - a[im]) - (b[jM] - b[jm])
    return gap * gap / (2 * (varA[iM] + varA[im] + varB[jM] + varB[jm]))


def run_family(name, a, b, var_of):
    rows_out, all_cert = [], True
    for Mi in [1, 4, 16, 64, 256, 1024]:
        M = Fr(Mi)
        varA, varB = var_of(M)
        theta = a + b
        var = varA + varB
        theta_f = [float(t) for t in theta]
        var_f = [float(v) for v in var]
        regs, best = [], None
        for reg in product(range(3), range(3), range(3), range(3)):
            c = settle_region(theta_f, var_f, theta, var, reg)
            if c is None:
                all_cert = False
                regs.append({"region": list(reg), "certified": False})
                continue
            regs.append({"region": list(reg), "certified": True, "route": c["route"],
                         "value": str(c["value"]), "active": c["S"],
                         "mu": [str(m) for m in c["mu"]]})
            if best is None or c["value"] < best[0]:
                best = (c["value"], list(reg), c)
        jf = J_frozen_exact(a, b, varA, varB)
        ju = best[0]
        rows_out.append({"M": Mi, "J_frozen": str(jf), "J_full": str(ju), "ratio": str(ju / jf),
                         "ratio_float": float(ju / jf), "argmin_region": best[1],
                         "argmin_x": [str(v) for v in best[2]["x"]],
                         "regions": len(regs),
                         "certified": sum(1 for r in regs if r["certified"]),
                         "exact_search_regions": sum(1 for r in regs
                                                     if r.get("route") == "exact-search"),
                         "region_certificates": regs})
        print(f"  {name} M={Mi:5d}: J_frozen={jf}  J_full={ju}  ratio={float(ju / jf):.6f}"
              f"  {rows_out[-1]['certified']}/81 exact"
              f" ({rows_out[-1]['exact_search_regions']} by exact search)", flush=True)
    return rows_out, all_cert


def main():
    if OUT.exists():
        print(f"refusing to overwrite existing {OUT}", file=sys.stderr)
        return 2
    print("Paper A: the two families, every region certified in exact rationals", flush=True)
    a1, b1 = [Fr(0), Fr(1), Fr(1, 2)], [Fr(0), Fr(3, 4), Fr(1, 2)]
    fam1, ok1 = run_family("family 1", a1, b1,
                           lambda M: ([Fr(1), Fr(1), Fr(1)], [Fr(1), Fr(1), M]))
    a2, b2 = [Fr(0), Fr(1), Fr(3, 4)], [Fr(0), Fr(1, 2), Fr(1, 4)]
    fam2, ok2 = run_family("family 2", a2, b2,
                           lambda M: ([Fr(1), M, Fr(1)], [Fr(1), Fr(1), Fr(1)]))
    check("every one of the 81 regions certifies EXACTLY, both families, every M", ok1 and ok2)
    check("family 1: J_frozen = 1/128 exactly at every M",
          all(Fr(r["J_frozen"]) == Fr(1, 128) for r in fam1))
    check("family 2: J_frozen = 1/(8(M+3)) exactly at every M",
          all(Fr(r["J_frozen"]) == Fr(1, 8 * (r["M"] + 3)) for r in fam2))
    check("family 1: ratio <= 16/M exactly at every M",
          all(Fr(r["ratio"]) <= Fr(16, r["M"]) for r in fam1))
    check("family 2: ratio >= (M+3)/24 exactly at every M",
          all(Fr(r["ratio"]) >= Fr(r["M"] + 3, 24) for r in fam2))
    check("family 2: J_full >= 1/192 exactly at every M",
          all(Fr(r["J_full"]) >= Fr(1, 192) for r in fam2))
    fl = json.load(open(FLOAT_IN))
    agree = all(abs(float(Fr(e["J_full"])) - f["J_full"]) <= 1e-9 * max(1.0, f["J_full"])
                and abs(float(Fr(e["J_frozen"])) - f["J_frozen"]) <= 1e-12
                for fam_e, fam_f in ((fam1, fl["family1"]), (fam2, fl["family2"]))
                for e, f in zip(fam_e, fam_f))
    check("every exact value agrees with the floating-point artifact to 1e-9", agree,
          f"float artifact sha256 {hashlib.sha256(FLOAT_IN.read_bytes()).hexdigest()[:16]}")
    out = {"producer": "scripts/EXP_paperA_frozen_proxy_exact.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "float_proposer_sha256": hashlib.sha256(
               pathlib.Path("scripts/EXP_paperA_frozen_proxy.py").read_bytes()).hexdigest(),
           "float_artifact_sha256": hashlib.sha256(FLOAT_IN.read_bytes()).hexdigest(),
           "evidence_class": "CERT (exact rational KKT certificate per region)",
           "family1": fam1, "family2": fam2, "checks": CHECKS,
           "all_passed": all(c["ok"] for c in CHECKS)}
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    OUT.write_text(json.dumps(out))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed; wrote {OUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
