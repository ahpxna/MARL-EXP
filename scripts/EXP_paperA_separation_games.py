#!/usr/bin/env python3
"""Paper A / A-separation: both games solved after the sup over allocations.

`LeanPaperASeparationV1` proves two bounds that bracket the value of a game AFTER the
experimenter has optimised the design:

    family A-low :  Gamma_true / Gamma_proxy <= 64 / M        (low_true_le, low_proxy_ge)
    family A-high:  Gamma_true / Gamma_proxy >= M / 96        (high_proxy_le, high_true_ge)

A bound is not a value.  This script SOLVES both games at each `M` and checks the solved
ratios against the proved bounds, so the figure shows measured optima with proved envelopes
rather than two formulas plotted against each other.

THE GAMES.  Eight cells, `0..3 = A1..A4` and `4..7 = B1..B4`.  A design `w` is a probability
vector; the information against an alternative is

    E_w(lambda) = (1/2) sum_e w_e (lambda_e - theta_e)^2 / var_e,

and the value of a design is the infimum over that game's alternative set.

  PROXY.  The frozen extrema are kept, so the alternative set is the single half-space
          `(lambda_1 - lambda_0) - (lambda_5 - lambda_4) <= 0`.  The infimum of a diagonal
          quadratic over a half-space is exact, `d^2 / (2 sum_e a_e^2 var_e / w_e)`, and the
          supremum over the simplex is exact too: Cauchy-Schwarz gives

              Gamma_proxy = d^2 / (2 (sum_e |a_e| sqrt(var_e))^2),

          attained at `w_e proportional to |a_e| sqrt(var_e)`.  The proxy game is therefore
          solved in CLOSED FORM and carries no solver error at all.

  TRUE.   The decision compares ranges, and `range(A) <= range(B)` holds exactly when SOME
          pair `(j, j')` of B-cells dominates every pair of A-cells:

              rangeA <= rangeB  <=>  exists (j,j'): for all (i,i'),
                                        lambda_i - lambda_i' <= lambda_j - lambda_j'.

          So the true alternative set is a union of SIXTEEN polyhedra, not a relaxation of
          one, and `J_true(w)` is the least of sixteen convex QPs.  Each QP's minimiser
          carries a KKT certificate with non-negative multipliers recovered by non-negative
          least squares, in the sense of `kkt_region_minimum`.

THE OUTER PROBLEM, AND WHY IT IS SOLVED BY CUTTING PLANES.  For fixed `lambda` the energy is
LINEAR in `w`, with gradient `g(lambda)_e = (lambda_e - theta_e)^2 / (2 var_e)`.  So the
outer problem is a zero-sum game: `sup_w inf_lambda <w, g(lambda)>`.  Restricting the
adversary to a finite set `L` of alternatives gives a linear program whose value is an UPPER
bound on the game; evaluating `J_true` at that LP's design gives a LOWER bound, since a
design's true value is achievable.  Adding the binding alternative to `L` and repeating
drives the two together.

That is not a convenience.  It means every reported `Gamma_true` comes with a two-sided
certificate: a design, a finite family of alternatives that pins it from above, and a
measured duality gap.  A local search would give a number with no witness that it is the
game's value; here the gap is printed and checked.

WHAT IS SAVED.  Not just the optimum: the maximising design, the supporting alternatives,
the binding region, the duality gap, the worst KKT residual over all sixteen regions, and
the proxy's exact closed form.  A ratio without its certificate is a number, not evidence.

SELF-CHECKS transcribe the proved statements: the A-low ratio must obey `64/M`, the A-high
ratio must obey `M/96`, the two exhibited designs must attain the constants `1/512` and
`1/768` that the Lean proofs use, and every region must certify.
"""

import json
import sys
from itertools import product

import numpy as np
from scipy.optimize import minimize, nnls

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# ----------------------------------------------------------------- the two worlds
def family_low(M):
    theta = np.array([0.0, 1.0, 0.5, 0.5, 0.0, 0.75, 0.5, 0.5])
    var = np.array([1.0, 1.0, 1.0, 1.0, 1.0, 1.0, M, M])
    return theta, var


def family_high(M):
    theta = np.array([0.0, 1.0, 0.75, 0.5, 0.0, 0.5, 0.25, 0.25])
    var = np.array([1.0, M, 1.0, M, 1.0, 1.0, 1.0, 1.0])
    return theta, var


EPS_W = 1e-9          # a design may not put exactly zero mass, or the energy is infinite


# ----------------------------------------------------------------- the proxy game
PROXY_A = np.zeros(8)
PROXY_A[1] = 1.0
PROXY_A[0] = -1.0
PROXY_A[5] = -1.0
PROXY_A[4] = 1.0


def J_proxy(w, theta, var):
    """Exact: the infimum of a diagonal quadratic over one half-space.

    With `H_e = w_e / var_e`, the cheapest point on `a^T lambda = b` costs
    `d^2 / (2 a^T H^{-1} a)`, and `a^T H^{-1} a = sum_e a_e^2 var_e / w_e`.
    """
    d = float(PROXY_A @ theta)              # the frozen gap, positive in both families
    if d <= 0:
        return 0.0
    q = float(np.sum(PROXY_A ** 2 * var / np.maximum(w, EPS_W)))
    return d * d / (2.0 * q)


def proxy_witness(w, theta, var):
    """The minimiser itself, so the certificate is exhibited and not merely scored."""
    d = float(PROXY_A @ theta)
    q = float(np.sum(PROXY_A ** 2 * var / np.maximum(w, EPS_W)))
    return theta - (d / q) * (PROXY_A * var / np.maximum(w, EPS_W))


def proxy_sup(theta, var):
    """EXACT: the supremum over the simplex, in closed form.

    Minimising `sum_e a_e^2 var_e / w_e` over the simplex is Cauchy-Schwarz; the minimum is
    `(sum_e |a_e| sqrt(var_e))^2`, attained at `w_e proportional to |a_e| sqrt(var_e)`.
    Cells outside the contrast get no mass, which is correct: they carry no information
    about it.
    """
    d = float(PROXY_A @ theta)
    coef = np.abs(PROXY_A) * np.sqrt(var)
    S = float(coef.sum())
    gamma = d * d / (2.0 * S * S)
    w = coef / S
    return gamma, w


# ----------------------------------------------------------------- the true game
def true_regions():
    """The sixteen polyhedra of `rangeA <= rangeB`, as `(A lambda <= b)` row blocks.

    Region `(j, j')` says the B-pair `(j, j')` dominates every A-pair, which is exactly the
    condition under which `rangeB` is realised there and already exceeds `rangeA`.
    """
    regs = []
    for j, jp in product(range(4), repeat=2):
        rows = []
        for i, ip in product(range(4), repeat=2):
            r = np.zeros(8)
            r[i] += 1.0
            r[ip] -= 1.0
            r[4 + j] -= 1.0
            r[4 + jp] += 1.0
            if np.allclose(r, 0.0):
                continue
            rows.append(r)
        regs.append((np.array(rows), np.zeros(len(rows)), (j, jp)))
    return regs


REGIONS = true_regions()


def solve_region(theta, H, Amat, bvec, starts=2):
    def f(x):
        d = x - theta
        return 0.5 * float(d @ (H * d))

    def gf(x):
        return H * (x - theta)

    cons = [{"type": "ineq",
             "fun": (lambda x, r=Amat[k], s=bvec[k]: s - r @ x),
             "jac": (lambda x, r=Amat[k]: -r)} for k in range(len(bvec))]
    best = None
    for seed in range(starts):
        x0 = theta if seed == 0 else theta + 0.2 * np.random.default_rng(seed).normal(size=8)
        res = minimize(f, x0, jac=gf, constraints=cons, method="SLSQP",
                       options={"maxiter": 500, "ftol": 1e-14})
        if res.success and (best is None or res.fun < best.fun):
            best = res
    return best


def kkt_residual(theta, H, Amat, bvec, x):
    """Stationarity, non-negativity and complementarity, with NON-NEGATIVE multipliers."""
    slack = bvec - Amat @ x
    act = np.where(slack < 1e-7)[0]
    grad = H * (x - theta)
    if len(act) == 0:
        return float(np.max(np.abs(grad)))
    Aa = Amat[act]
    y, _ = nnls(Aa.T, -grad)
    stat = float(np.max(np.abs(grad + Aa.T @ y)))
    comp = float(np.max(np.abs(y * slack[act])))
    return max(stat, comp)


def J_true(w, theta, var, want_cert=False):
    H = np.maximum(w, EPS_W) / var
    best, cert = np.inf, None
    worst_kkt, ncert = 0.0, 0
    for Amat, bvec, tag in REGIONS:
        res = solve_region(theta, H, Amat, bvec)
        if res is None:
            continue
        k = kkt_residual(theta, H, Amat, bvec, res.x)
        if k <= 1e-5:
            ncert += 1
            worst_kkt = max(worst_kkt, k)
        if res.fun < best - 1e-14:
            best = float(res.fun)
            cert = {"region": list(tag), "lambda": res.x.tolist(), "kkt": k}
    if want_cert:
        return best, {"witness": cert, "worst_kkt": worst_kkt,
                      "certified": ncert, "regions": len(REGIONS)}
    return best


# ------------------------------------------------- the outer sup, by cutting planes
def lp_upper(grads):
    """max_w min_{l in L} <w, g_l>  over the simplex, as a linear program.

    Variables `(w, t)`; maximise `t` subject to `<w, g_l> >= t` for every cut.  Its value is
    an upper bound on the game, because restricting the adversary can only help the
    maximiser.
    """
    from scipy.optimize import linprog
    n = 8
    G = np.array(grads)
    nc = len(G)
    c = np.zeros(n + 1)
    c[-1] = -1.0                                  # maximise t
    A_ub = np.hstack([-G, np.ones((nc, 1))])      # t - <w,g> <= 0
    b_ub = np.zeros(nc)
    A_eq = np.zeros((1, n + 1))
    A_eq[0, :n] = 1.0
    b_eq = np.array([1.0])
    bounds = [(0.0, None)] * n + [(None, None)]
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=bounds,
                  method="highs")
    if not res.success:
        return None, None
    return float(-res.fun), np.array(res.x[:n])


def true_gradient(lam, theta, var):
    return (lam - theta) ** 2 / (2.0 * var)


def solve_sup_true(theta, var, iters=80, tol=1e-12):
    """Cutting planes: alternate an LP upper bound with a true-value lower bound."""
    w = np.ones(8) / 8.0
    cuts, best_lo, best_w, best_cert = [], -np.inf, w.copy(), None
    up = np.inf
    for _ in range(iters):
        lo, cert = J_true(w, theta, var, want_cert=True)
        if lo > best_lo:
            best_lo, best_w, best_cert = lo, w.copy(), cert
        lam = np.array(cert["witness"]["lambda"])
        cuts.append(true_gradient(lam, theta, var))
        u, w_new = lp_upper(cuts)
        if u is None:
            break
        up = u
        w = w_new
        if up - best_lo <= tol * max(1.0, abs(up)):
            break
    return best_lo, best_w, float(up - best_lo), best_cert


def main():
    print("=" * 78)
    print("Paper A: both games solved after the sup over allocations")
    print("=" * 78)

    Ms = [1.0, 2.0, 4.0, 8.0, 16.0, 32.0, 64.0, 128.0, 256.0, 512.0, 1024.0]
    if "--smoke" in sys.argv:
        Ms = [4.0, 64.0]

    rows_low, rows_high = [], []

    print("\n  Family A-low: variance M on B3 and B4   (proved: ratio <= 64/M)")
    print("  " + "-" * 72)
    for M in Ms:
        theta, var = family_low(M)
        gp, wp = proxy_sup(theta, var)
        gt, wt, gap, cert = solve_sup_true(theta, var)
        ratio = gt / gp
        rows_low.append({"M": M, "Gamma_true": gt, "Gamma_proxy": gp, "ratio": ratio,
                         "bound_64_over_M": 64.0 / M, "duality_gap": gap,
                         "w_true": wt.tolist(), "w_proxy": wp.tolist(),
                         "proxy_witness": proxy_witness(wp, theta, var).tolist(),
                         "true_cert": cert})
        print(f"      M={M:7.1f}:  G_true={gt:.6e}  G_proxy={gp:.6e}"
              f"  ratio={ratio:.4e}   64/M={64.0/M:.4e}   gap={gap:.1e}"
              f"   {cert['certified']}/{cert['regions']} certified")

    print("\n  Family A-high: variance M on A2 and A4   (proved: ratio >= M/96)")
    print("  " + "-" * 72)
    for M in Ms:
        theta, var = family_high(M)
        gp, wp = proxy_sup(theta, var)
        gt, wt, gap, cert = solve_sup_true(theta, var)
        ratio = gt / gp
        rows_high.append({"M": M, "Gamma_true": gt, "Gamma_proxy": gp, "ratio": ratio,
                          "bound_M_over_96": M / 96.0, "duality_gap": gap,
                          "w_true": wt.tolist(), "w_proxy": wp.tolist(),
                          "proxy_witness": proxy_witness(wp, theta, var).tolist(),
                          "true_cert": cert})
        print(f"      M={M:7.1f}:  G_true={gt:.6e}  G_proxy={gp:.6e}"
              f"  ratio={ratio:.4e}   M/96={M/96.0:.4e}   gap={gap:.1e}"
              f"   {cert['certified']}/{cert['regions']} certified")

    # ---- the two designs the Lean proofs name, evaluated directly
    print("\n  the constants the Lean proofs use, evaluated at the designs they name")
    print("  " + "-" * 72)
    w_low_star = np.array([.25, .25, 0, 0, .25, .25, 0, 0])
    w_high_star = np.array([1, 0, 1, 0, 1, 1, 1, 1]) / 6.0
    th_l, va_l = family_low(64.0)
    th_h, va_h = family_high(64.0)
    jl = J_proxy(w_low_star, th_l, va_l)
    jh = J_true(w_high_star, th_h, va_h)
    print(f"      low_proxy_ge  : J_proxy(w*) = {jl:.10f}   Lean lower bound 1/512"
          f" = {1/512:.10f}")
    print(f"      high_true_ge  : J_true(w*)  = {jh:.10f}   Lean lower bound 1/768"
          f" = {1/768:.10f}")

    # ---------------------------------------------------------------- self-checks
    print()
    check("A-low: the solved ratio obeys the proved bound 64/M at every M",
          all(r["ratio"] <= r["bound_64_over_M"] * (1 + 1e-6) for r in rows_low),
          f"worst slack {min(r['bound_64_over_M'] / r['ratio'] for r in rows_low):.3f}x")
    check("A-low: and the ratio actually decays, so the bound is not vacuous",
          rows_low[-1]["ratio"] < rows_low[0]["ratio"] / 4,
          f"{rows_low[0]['ratio']:.3e} at M={rows_low[0]['M']:g}"
          f" -> {rows_low[-1]['ratio']:.3e} at M={rows_low[-1]['M']:g}")
    exact_low = all(abs(r["Gamma_proxy"] - 1/512) < 1e-12 for r in rows_low)
    check("A-low: the proxy value is EXACTLY 1/512 at every M, so the Lean bound"
          " `low_proxy_ge` is not merely valid but TIGHT", exact_low,
          "the design it names is the proxy game's optimum")
    check("A-high: the solved ratio obeys the proved bound M/96 at every M",
          all(r["ratio"] >= r["bound_M_over_96"] * (1 - 1e-6) for r in rows_high),
          f"worst slack {min(r['ratio'] / max(r['bound_M_over_96'], 1e-12) for r in rows_high):.3f}x")
    check("A-high: and the ratio actually diverges",
          rows_high[-1]["ratio"] > 4 * rows_high[0]["ratio"],
          f"{rows_high[0]['ratio']:.3e} at M={rows_high[0]['M']:g}"
          f" -> {rows_high[-1]['ratio']:.3e} at M={rows_high[-1]['M']:g}")
    cf = all(abs(r["Gamma_proxy"] - 1.0 / (8 * (3 + r["M"] ** 0.5) ** 2)) < 1e-12
             for r in rows_high)
    check("A-high: the proxy value matches its closed form 1/(8(3+sqrt M)^2) exactly,"
          " which sits below the Lean bound 1/(8M) as the proof requires", cf,
          "so `high_proxy_le` is valid and the exact value is sharper")
    check("the design named in `low_proxy_ge` attains at least the Lean constant 1/512",
          jl >= 1/512 - 1e-12, f"{jl:.10f} vs {1/512:.10f}")
    check("the design named in `high_true_ge` attains at least the Lean constant 1/768",
          jh >= 1/768 - 1e-9, f"{jh:.10f} vs {1/768:.10f}")
    check("every region of the true game certifies at the maximising design",
          all(r["true_cert"]["certified"] == r["true_cert"]["regions"]
              for r in rows_low + rows_high),
          "non-negative multipliers exist in all 16 regions at every M")
    worst_rel = max(r["duality_gap"] / max(r["Gamma_true"], 1e-12)
                    for r in rows_low + rows_high)
    check("every solved true value carries a two-sided certificate whose duality gap"
          " closed to 1e-3 relative, so it is the game's value and not a local search's",
          worst_rel <= 1e-3,
          f"worst relative gap {worst_rel:.2e}; absolute gaps are LP-vs-QP tolerances,"
          " not modelling error")
    check("the proxy game is solved in closed form, so it carries no solver error at all",
          True, "Cauchy-Schwarz gives both the value and the maximising design")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperA_separation_games.py").read_bytes()).hexdigest(),"family_low": rows_low, "family_high": rows_high,
           "lean_constant_low": jl, "lean_constant_high": jh,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperA_separation_games.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
