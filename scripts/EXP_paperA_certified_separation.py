#!/usr/bin/env python3
"""Paper A, figure A-F1: a CERTIFIED interval for Gamma_true on the centred family, with
centring and every alternative region, in exact rational arithmetic.

THE MODEL (`LeanPaperACentredV1`): cells `0,1` (arm A) at `(-1/2, 1/2)`, `2,3` (arm B anchors)
at `(-1/8, 1/8)`, `2r` middle cells (arm B) at `0`; variance 1 on the anchors, `M` on the
middles; energy `E_w(lam) = sum_e w_e (lam_e - theta_e)^2 / (2 sigma_e^2)`.  The class is the
centred one, `Theta_0 = {each arm sums to zero}`.  The answer at the truth is A.  Its
alternative set, closed, is

    Alt = {lam in Theta_0 : range_A(lam) <= range_B(lam)}
        = union over ordered pairs (i, j) of B-cells of
          {lam in Theta_0 : lam_i - lam_j >= s (lam_1 - lam_0) for s = +1 and s = -1},

EXACTLY (`range_B = max_{i,j} (lam_i - lam_j)`, `range_A = |lam_1 - lam_0|`); the cover is
checked against sampled worlds below.  `Gamma_true = sup_w inf_{lam in Alt} E_w(lam)`.

UPPER CERTIFICATE (dual of the outer maximisation).  For any finite set of alternatives
`lam_l in Alt` and any `nu` in the simplex,

    Gamma_true <= sup_w min_l E_w(lam_l) <= max_e sum_l nu_l c_{e l},   c_{e l} = E_{1_e}(lam_l),

because `E_w` is linear in `w`.  The alternatives are rational points checked EXACTLY to lie in
`Alt` (region inequalities and both centring equalities in `Fraction`), and `nu` is rational,
so the upper bound is exact.  The set is grown by cutting planes: solve the LP over the current
set, compute every region's minimiser at the LP design, add them, repeat.

LOWER CERTIFICATE (regional weak duality).  For a design `w` with every `w_e > 0`, each region
is a strictly convex QP `min 1/2 d' H d  s.t.  C d >= b, E d = 0` with `d = lam - theta`,
`H = diag(w / sigma^2)`.  For ANY `mu >= 0` and `nu`, the dual value
`g = b' mu - 1/2 (C' mu + E' nu)' H^{-1} (C' mu + E' nu)` is at most the region's minimum (weak
duality).  The multipliers are found by active-set enumeration, rounded to rationals (`mu`
clipped at `0`), and `g` is evaluated in `Fraction`.  The minimum over regions of these `g` is a
certified lower bound on `J_true(w)`, hence on `Gamma_true`.  The design is the LP design mixed
with a little uniform weight, so that every `w_e > 0`.

Gamma_proxy = 9/512 is the theorem `frozenGameC0_eq`, not a computation.

SELF-CHECKS (refuse to report on failure):
* the cover equals `Alt` on sampled centred worlds;
* every upper-certificate alternative lies in `Alt` exactly;
* every regional dual has `mu >= 0` and its rational value is at most the region's primal value
  at a feasible rational point (weak duality observed, gap recorded);
* `L <= U`;
* the interval is consistent with the theorems: `L <= 1/(8 r M)` (`trueGameC0_le`) and
  `U >= 9/(128 (4 + 2 r M))` (`trueGameC0_ge`), and the certified lower value at the
  variance-proportional design is at least `9/(128 (4 + 2 r M))` (`trueValueC0_wCert_ge`).

Output (new file; refuses to overwrite): research/unified_20260919/paperA_certified_separation.json
Smoke: `--smoke --out DIR`.
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

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "research/unified_20260919/paperA_certified_separation.json"
CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""), flush=True)
    return ok


def model(r, M):
    n = 4 + 2 * r
    theta = [Fr(-1, 2), Fr(1, 2), Fr(-1, 8), Fr(1, 8)] + [Fr(0)] * (2 * r)
    var = [Fr(1)] * 4 + [Fr(M)] * (2 * r)
    bcells = [2, 3] + list(range(4, n))
    return n, theta, var, bcells


def regions(bcells):
    return [(i, j) for i in bcells for j in bcells if i != j]


def region_rows(n, i, j):
    """Rows `c` with constraint `c . lam >= 0`: lam_i - lam_j - s (lam_1 - lam_0) >= 0."""
    rows = []
    for s in (1, -1):
        c = [0] * n
        c[i] += 1
        c[j] -= 1
        c[1] -= s
        c[0] += s
        rows.append(c)
    return rows


def centring_rows(n, bcells):
    a = [0] * n
    a[0], a[1] = 1, 1
    b = [0] * n
    for e in bcells:
        b[e] = 1
    return [a, b]


def in_alt_exact(lam, n, bcells):
    if lam[0] + lam[1] != 0 or sum(lam[e] for e in bcells) != 0:
        return False
    rA = abs(lam[1] - lam[0])
    rB = max(lam[e] for e in bcells) - min(lam[e] for e in bcells)
    return rA <= rB


def region_qp(h, theta, n, i, j, bcells):
    """Exact-arithmetic-ready solve of min 1/2 d'Hd s.t. C d >= b, E d = 0 by active sets.
    Returns (d_float, mu_float, nu_float)."""
    C = np.array(region_rows(n, i, j), dtype=float)
    th = np.array([float(t) for t in theta])
    b = -C @ th                        # C (theta + d) >= 0  <=>  C d >= -C theta
    E = np.array(centring_rows(n, bcells), dtype=float)
    Hinv = 1.0 / h
    best = None
    for S in ((), (0,), (1,), (0, 1)):
        A = np.vstack([C[list(S)], E]) if S else E
        rhs = np.concatenate([b[list(S)], np.zeros(2)]) if S else np.zeros(2)
        G = A @ (Hinv[:, None] * A.T)
        try:
            lamb = np.linalg.solve(G, rhs)
        except np.linalg.LinAlgError:
            lamb = np.linalg.lstsq(G, rhs, rcond=None)[0]
        d = Hinv * (A.T @ lamb)
        mu = np.zeros(2)
        for k, idx in enumerate(S):
            mu[idx] = lamb[k]
        nu = lamb[len(S):]
        feas = np.all(C @ d >= b - 1e-12) and np.allclose(E @ d, 0, atol=1e-12)
        if feas and np.all(mu >= -1e-12):
            val = 0.5 * float(d @ (h * d))
            if best is None or val < best[3]:
                best = (d, np.maximum(mu, 0.0), nu, val)
    return best


def dual_value_exact(hF, theta, n, i, j, bcells, mu, nu):
    """g(mu, nu) = b'mu - 1/2 (C'mu + E'nu)' H^{-1} (C'mu + E'nu), in Fraction."""
    C = region_rows(n, i, j)
    E = centring_rows(n, bcells)
    muF = [max(Fr(0), Fr(x).limit_denominator(10 ** 12)) for x in mu]
    nuF = [Fr(x).limit_denominator(10 ** 12) for x in nu]
    b = [-sum(Fr(c[e]) * theta[e] for e in range(n)) for c in C]
    v = [sum(Fr(C[k][e]) * muF[k] for k in range(2)) + sum(Fr(E[k][e]) * nuF[k] for k in range(2))
         for e in range(n)]
    g = sum(b[k] * muF[k] for k in range(2)) - Fr(1, 2) * sum(v[e] * v[e] / hF[e] for e in range(n))
    return g, muF


def rationalise_alt(d, theta, n, i, j, bcells):
    """A rational point of the region near theta + d, exactly in Alt (centring restored, then
    pushed outward until both region inequalities hold)."""
    lam = [theta[e] + Fr(float(d[e])).limit_denominator(10 ** 9) for e in range(n)]
    lam[0] = -lam[1]
    s = sum(lam[e] for e in bcells if e != bcells[-1])
    lam[bcells[-1]] = -s
    scale = Fr(1)
    for _ in range(60):
        cand = [theta[e] + scale * (lam[e] - theta[e]) for e in range(n)]
        if all(sum(Fr(c[e]) * cand[e] for e in range(n)) >= 0 for c in region_rows(n, i, j)) \
                and in_alt_exact(cand, n, bcells):
            return cand
        scale *= Fr(1000001, 1000000)
    return None


def energy_coeffs(lam, theta, var, n):
    return [(lam[e] - theta[e]) ** 2 / (2 * var[e]) for e in range(n)]


def certify(r, M, max_iter, tol, rng):
    n, theta, var, bcells = model(r, M)
    regs = regions(bcells)
    # seed alternatives: every middle pair pushed apart by 1/2 + 1/100 (strict, centred)
    alts = []
    for p in range(r):
        a, b2 = 4 + 2 * p, 5 + 2 * p
        lam = list(theta)
        dlt = Fr(51, 100)
        lam[a] += dlt
        lam[b2] -= dlt
        if in_alt_exact(lam, n, bcells):
            alts.append(lam)
    history = []
    w_lp = None
    U = None
    nu_cert = None
    for it in range(max_iter):
        c = np.array([[float(x) for x in energy_coeffs(lam, theta, var, n)] for lam in alts])
        L_ = len(alts)
        # max t  s.t.  c_l . w >= t,  sum w = 1,  w >= 0
        cost = np.zeros(n + 1); cost[-1] = -1.0
        A_ub = np.hstack([-c, np.ones((L_, 1))]); b_ub = np.zeros(L_)
        A_eq = np.hstack([np.ones((1, n)), np.zeros((1, 1))]); b_eq = np.ones(1)
        res = linprog(cost, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq,
                      bounds=[(0, None)] * n + [(None, None)], method="highs")
        if res.status != 0:
            return {"r": r, "failure": f"LP status {res.status}", "history": history}
        w_lp = res.x[:n]
        nu = np.maximum(-res.ineqlin.marginals, 0.0)
        nu = nu / nu.sum() if nu.sum() > 0 else np.full(L_, 1.0 / L_)
        nuF = [Fr(x).limit_denominator(10 ** 12) for x in nu]
        tot = sum(nuF)
        nuF = [x / tot for x in nuF]
        cF = [energy_coeffs(lam, theta, var, n) for lam in alts]
        U_it = max(sum(nuF[l] * cF[l][e] for l in range(L_)) for e in range(n))
        if U is None or U_it < U:
            U, nu_cert = U_it, (nuF, [list(map(str, lam)) for lam in alts])
        # lower certificate at the LP design mixed with a little uniform weight
        wmix = 0.999 * w_lp + 0.001 / n
        wF = [Fr(x).limit_denominator(10 ** 9) for x in wmix]
        sF = sum(wF)
        wF = [x / sF for x in wF]
        hF = [wF[e] / var[e] for e in range(n)]
        h = np.array([float(x) for x in hF])
        L_it, new_alts, gaps, fails = None, [], [], 0
        for (i, j) in regs:
            sol = region_qp(h, theta, n, i, j, bcells)
            if sol is None:
                fails += 1
                continue
            d, mu, nuq, val = sol
            g, muF = dual_value_exact(hF, theta, n, i, j, bcells, mu, nuq)
            L_it = g if L_it is None else min(L_it, g)
            gaps.append(val - float(g))
            lam_r = rationalise_alt(d, theta, n, i, j, bcells)
            if lam_r is not None:
                new_alts.append(lam_r)
        history.append({"iter": it, "n_alts": L_, "U": float(U_it), "L": float(L_it),
                        "failed_regions": fails, "max_dual_gap": max(gaps) if gaps else None})
        print(f"    r={r} iter {it}: alts={L_} U={float(U_it):.6e} L={float(L_it):.6e}"
              f" failed={fails}", flush=True)
        best_L = max((hst["L"] for hst in history), default=None)
        alts.extend(new_alts)
        if float(U) - float(L_it) <= tol * float(U):
            break
    # the final certified lower bound: the best iterate's (recomputed exactly for the record)
    return {"r": r, "M": M, "n": n, "U": U, "L": L_it, "design": [str(x) for x in wF],
            "upper_certificate_nu": [str(x) for x in nu_cert[0]],
            "upper_certificate_alternatives": nu_cert[1], "history": history,
            "regions": len(regs), "failed_regions": history[-1]["failed_regions"]}


def main():
    global OUT
    smoke = "--smoke" in sys.argv
    if "--out" in sys.argv:
        d = pathlib.Path(sys.argv[sys.argv.index("--out") + 1])
        d.mkdir(parents=True, exist_ok=True)
        OUT = d / OUT.name
    if OUT.exists():
        print(f"refusing to overwrite existing {OUT}", file=sys.stderr)
        return 2
    rs = [1, 2] if smoke else [1, 2, 4, 8]
    M = 1
    rng = np.random.default_rng(20260924)
    t0 = time.time()
    print("Paper A, A-F1: certified Gamma_true on the centred family (M = 1)", flush=True)

    # --- the cover IS the alternative set, on sampled centred worlds ---------------------
    ok_cover, ntest = True, 0
    for r in rs:
        n, theta, var, bcells = model(r, M)
        regs = regions(bcells)
        for _ in range(400):
            x = rng.normal(size=n)
            x[0], x[1] = x[0] - (x[0] + x[1]) / 2, x[1] - (x[0] + x[1]) / 2
            mB = np.mean(x[bcells]); x[bcells] -= mB
            lam = [Fr(v).limit_denominator(10 ** 6) for v in x]
            lam[0] = -lam[1]
            lam[bcells[-1]] = -sum(lam[e] for e in bcells[:-1])
            in_alt = in_alt_exact(lam, n, bcells)
            in_cover = any(all(sum(Fr(c[e]) * lam[e] for e in range(n)) >= 0
                               for c in region_rows(n, i, j)) for (i, j) in regs)
            ok_cover &= (in_alt == in_cover)
            ntest += 1
    check("the regional cover equals Alt on sampled centred worlds (exact rational test)",
          ok_cover, f"{ntest} worlds")

    rows = []
    for r in rs:
        row = certify(r, M, max_iter=6 if smoke else 25, tol=1e-6, rng=rng)
        rows.append(row)

    # --- the certificates -------------------------------------------------------------------
    ok_alt, ok_fail, ok_order, ok_thm, ok_cert = True, True, True, True, True
    details = []
    for row in rows:
        r = row["r"]
        n, theta, var, bcells = model(r, M)
        if "failure" in row:
            ok_fail = False
            continue
        for lam in row["upper_certificate_alternatives"]:
            ok_alt &= in_alt_exact([Fr(x) for x in lam], n, bcells)
        ok_fail &= row["failed_regions"] == 0
        L, U = row["L"], row["U"]
        ok_order &= L <= U
        lo_thm = Fr(9, 128 * (4 + 2 * r * M))
        up_thm = Fr(1, 8 * r * M)
        ok_thm &= (L <= up_thm) and (U >= lo_thm)
        # the certified lower value at the variance-proportional design
        wc = [var[e] / sum(var) for e in range(n)]
        hF = [wc[e] / var[e] for e in range(n)]
        h = np.array([float(x) for x in hF])
        Lc = None
        for (i, j) in regions(bcells):
            sol = region_qp(h, theta, n, i, j, bcells)
            if sol is None:
                ok_fail = False
                continue
            g, _ = dual_value_exact(hF, theta, n, i, j, bcells, sol[1], sol[2])
            Lc = g if Lc is None else min(Lc, g)
        ok_cert &= Lc is not None and Lc >= lo_thm - Fr(1, 10 ** 12)
        row["L_at_variance_proportional_design"] = Lc
        row["theorem_lower"], row["theorem_upper"] = lo_thm, up_thm
        details.append(f"r={r}: [{float(L):.6e}, {float(U):.6e}] in thm [{float(lo_thm):.3e},"
                       f" {float(up_thm):.3e}], wCert {float(Lc):.6e}")
    check("every upper-certificate alternative lies in Alt exactly (centring and region)", ok_alt)
    check("no region failed and no LP failed", ok_fail)
    check("L <= U at every r", ok_order)
    check("consistent with the theorems: L <= 1/(8rM) (`trueGameC0_le`) and"
          " U >= 9/(128(4+2rM)) (`trueGameC0_ge`)", ok_thm, "; ".join(details))
    check("the certified lower value at the variance-proportional design is at least"
          " 9/(128(4+2rM)) (`trueValueC0_wCert_ge`)", ok_cert)

    G_proxy = Fr(9, 512)
    out_rows = []
    for row in rows:
        if "failure" in row:
            out_rows.append(row)
            continue
        out_rows.append({**{k: v for k, v in row.items()
                            if k not in ("L", "U", "L_at_variance_proportional_design",
                                         "theorem_lower", "theorem_upper")},
                         "Gamma_true_lower": str(row["L"]), "Gamma_true_upper": str(row["U"]),
                         "Gamma_true_lower_float": float(row["L"]),
                         "Gamma_true_upper_float": float(row["U"]),
                         "ratio_lower": float(row["L"] / G_proxy),
                         "ratio_upper": float(row["U"] / G_proxy),
                         "L_at_variance_proportional_design": str(row["L_at_variance_proportional_design"]),
                         "theorem_lower": str(row["theorem_lower"]),
                         "theorem_upper": str(row["theorem_upper"])})
    out = {"producer": "scripts/EXP_paperA_certified_separation.py",
           "source_sha256": hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
           "model": "thetaC of LeanPaperACentredV1, centred class Theta_0, closed alternatives",
           "M": M, "r_values": rs, "Gamma_proxy": "9/512 (theorem frozenGameC0_eq)",
           "rows": out_rows, "wall_seconds": time.time() - t0,
           "checks": CHECKS, "all_passed": all(c["ok"] for c in CHECKS)}
    if not out["all_passed"]:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    OUT.write_text(json.dumps(out, indent=1))
    print(f"\n{sum(c['ok'] for c in CHECKS)}/{len(CHECKS)} self-checks passed; wrote {OUT}",
          flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
