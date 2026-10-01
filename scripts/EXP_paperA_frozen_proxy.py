#!/usr/bin/env python3
"""Paper A, steps A2/A3/A5: the frozen-extrema proxy misprices in BOTH directions.

A range-based compression decision compares `range(A)` with `range(B)`.  The natural proxy
freezes the argmax and argmin cells at their current positions and asks how much the
observations must move to reverse the comparison.  That proxy is wrong in both directions,
and this script computes by how much.

The TRUE alternative set is a union of polyhedral regions, one per assignment of which cell
realises each arm's maximum and minimum:

    region(iM, im, jM, jm) = { a', b' :  a'_{iM} >= a'_i for all i,
                                         a'_{im} <= a'_i for all i,
                                         b'_{jM} >= b'_j, b'_{jm} <= b'_j,
                                         (a'_{iM} - a'_{im}) - (b'_{jM} - b'_{jm}) <= 0 }

so `J_full` is the minimum over regions of a convex QP.

`J_frozen` is NOT one of those regions.  It is the FROZEN-LINEAR PROXY: the range
comparison is linearised at the original extrema and the ordering constraints are DROPPED
entirely.  The distinction decides what the numbers can mean.  If `J_frozen` were the
minimum over a single region, then, a region being a subset of the whole space,

    J_full <= J_region   always,

and a ratio `J_full / J_frozen > 1` would be arithmetically impossible.  Family 2 produces
ratios far above one, and that is coherent only because the proxy optimises over a LARGER
set than the true alternative set -- it admits points that violate the ordering conditions
and therefore are not alternatives at all.  So the two quantities are not nested in either
direction, which is exactly why the surrogate can misprice BOTH ways.  Dropping the ordering constraints would
make the relaxation vacuous -- a region with `iM = im` forces `a'` constant and admits a
zero-energy point -- so the constraints are carried, and each region is solved as a QP.

Every region is SETTLED, not just the winning one.  For each region the solver's primal
point and its non-negative multipliers are checked against the stationarity and
complementary-slackness conditions of `LeanPaperAOracleCertificateV1.kkt_region_minimum`,
which proves that a point passing those checks is the minimum over that region for EVERY
feasible competitor.  A region that fails to certify is not skipped: it is discharged by a
solver-free lower bound that already exceeds the best certified value, so it provably
cannot contain the global minimum.  Any region that is neither certified nor dominated is
counted as UNRESOLVED and fails the self-check, because a minimum over a union is only as
trustworthy as the weakest of its parts.  A grid would only produce a candidate.

Two families, with `M` the effective variance of one designated cheap cell:

  FAMILY 1 (the proxy prices the information too high: J_full / J_frozen -> 0).
      A = (0, 1, 1/2),   B = (0, 3/4, 1/2),  variance M on B's middle cell.
      Freezing the extrema forces four unit-variance cells to close a gap of 1/4.
      The true alternative may instead lift B's middle cell to become the new maximum,
      which costs `1/(8M)`.  So `J_full / J_frozen -> 0`.

  FAMILY 2 (the proxy prices it too low: J_full / J_frozen -> infinity, which is possible
             only because the proxy's feasible set is not contained in the true one).
      A = (0, 1, 3/4),   B = (0, 1/2, 1/4),  variance M on A's original maximum.
      Lowering the cheap maximum is not enough: the runner-up at 3/4 remains, so the
      true cost stays bounded below while the frozen proxy becomes free.
      So `J_full / J_frozen -> infinity`.
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


def region_constraints(nA, nB, iM, im, jM, jm):
    """Rows of `A x <= b` for one region, in the stacked variable x = (a', b')."""
    n = nA + nB
    rows, rhs = [], []
    for i in range(nA):                      # a'_{iM} >= a'_i
        if i == iM:
            continue
        r = np.zeros(n); r[i] = 1.0; r[iM] -= 1.0
        rows.append(r); rhs.append(0.0)
    for i in range(nA):                      # a'_{im} <= a'_i
        if i == im:
            continue
        r = np.zeros(n); r[im] = 1.0; r[i] -= 1.0
        rows.append(r); rhs.append(0.0)
    for j in range(nB):
        if j == jM:
            continue
        r = np.zeros(n); r[nA + j] = 1.0; r[nA + jM] -= 1.0
        rows.append(r); rhs.append(0.0)
    for j in range(nB):
        if j == jm:
            continue
        r = np.zeros(n); r[nA + jm] = 1.0; r[nA + j] -= 1.0
        rows.append(r); rhs.append(0.0)
    # the decision flips: range(a') <= range(b')
    r = np.zeros(n)
    r[iM] += 1.0; r[im] -= 1.0
    r[nA + jM] -= 1.0; r[nA + jm] += 1.0
    rows.append(r); rhs.append(0.0)
    return np.array(rows), np.array(rhs)


def solve_region(theta, Hdiag, Amat, bvec):
    """Minimise (1/2) sum_i H_ii (x_i - theta_i)^2 over {A x <= b}."""
    n = len(theta)

    def f(x):
        d = x - theta
        return 0.5 * float(d @ (Hdiag * d))

    def gf(x):
        return Hdiag * (x - theta)

    cons = [{"type": "ineq",
             "fun": (lambda x, r=Amat[k], s=bvec[k]: s - r @ x),
             "jac": (lambda x, r=Amat[k]: -r)} for k in range(len(bvec))]
    best = None
    for seed in range(4):
        x0 = theta + (0.0 if seed == 0 else 0.25 * np.random.default_rng(seed).normal(size=n))
        res = minimize(f, x0, jac=gf, constraints=cons, method="SLSQP",
                       options={"maxiter": 800, "ftol": 1e-14})
        if res.success and (best is None or res.fun < best.fun):
            best = res
    return best


def kkt_residual(theta, Hdiag, Amat, bvec, x):
    """Recover multipliers from the active set and return the KKT residuals that
    `kkt_region_minimum` checks: stationarity, non-negativity, complementarity.

    The multipliers are recovered by NON-NEGATIVE least squares, not plain least
    squares.  On a degenerate region -- one whose active constraints are linearly
    dependent, such as `iM = im`, which forces the arm constant -- the multipliers
    are not unique, and the minimum-norm solution that plain least squares returns
    can carry negative entries while a perfectly good non-negative one exists.  The
    condition the Lean theorem asks for is existence of non-negative multipliers, so
    that is what is searched for.
    """
    slack = bvec - Amat @ x
    act = np.where(slack < 1e-7)[0]
    grad = Hdiag * (x - theta)                      # H (x - theta)
    if len(act) == 0:
        return float(np.max(np.abs(grad))), 0.0, 0.0
    Aa = Amat[act]
    y, _ = nnls(Aa.T, -grad)                        # min ||Aa^T y + grad|| s.t. y >= 0
    stat = float(np.max(np.abs(grad + Aa.T @ y)))
    neg = float(max(0.0, -y.min())) if len(y) else 0.0
    comp = float(np.max(np.abs(y * slack[act]))) if len(act) else 0.0
    return stat, neg, comp


def region_lower_bound(theta, Hdiag, Amat, bvec):
    """A lower bound on the region's minimum that needs no solver.

    Relaxing `{A x <= b}` to a single half-space `{a_j^T x <= b_j}` can only enlarge
    the feasible set, so the exact distance-energy to that half-space is a valid
    lower bound; taking the largest over `j` keeps it valid.  A region whose bound
    already exceeds the best certified value cannot hide a smaller minimum, which is
    what lets an unresolved region be discharged instead of ignored.
    """
    viol = Amat @ theta - bvec
    best = 0.0
    for j in range(len(bvec)):
        if viol[j] <= 0:
            continue
        q = float((Amat[j] ** 2 / Hdiag).sum())     # a_j^T H^{-1} a_j
        if q > 0:
            best = max(best, float(viol[j]) ** 2 / (2.0 * q))
    return best


def J_full(a, b, varA, varB):
    """Minimum over ALL regions, with every region given one of three statuses.

    CERTIFIED   the solver returned a point and non-negative multipliers satisfying
                stationarity and complementary slackness, so
                `LeanPaperAOracleCertificateV1.kkt_region_minimum` applies and the
                value is the minimum over that region for EVERY feasible competitor.
    DOMINATED   the solve did not certify, but the solver-free lower bound of
                `region_lower_bound` already exceeds the best certified value, so the
                region provably cannot contain the global minimum.
    UNRESOLVED  neither.  These are counted and reported; a run with any of them has
                not established the minimum over the union, and the self-check fails.

    A minimum over a union is only as trustworthy as the weakest of its parts, so an
    unresolved region is never silently skipped.
    """
    nA, nB = len(a), len(b)
    theta = np.concatenate([a, b])
    Hdiag = 1.0 / np.concatenate([varA, varB])
    entries = []
    for iM, im, jM, jm in product(range(nA), range(nA), range(nB), range(nB)):
        Amat, bvec = region_constraints(nA, nB, iM, im, jM, jm)
        lb = region_lower_bound(theta, Hdiag, Amat, bvec)
        res = solve_region(theta, Hdiag, Amat, bvec)
        if res is None:
            entries.append({"reg": (iM, im, jM, jm), "val": None, "kkt": None,
                            "lb": lb, "A": Amat, "b": bvec, "x": None})
            continue
        st, ng, cp = kkt_residual(theta, Hdiag, Amat, bvec, res.x)
        entries.append({"reg": (iM, im, jM, jm), "val": float(res.fun),
                        "kkt": max(st, ng, cp), "lb": lb,
                        "A": Amat, "b": bvec, "x": res.x})

    TOL = 1e-5
    cert = [e for e in entries if e["kkt"] is not None and e["kkt"] <= TOL]
    if not cert:
        raise RuntimeError("no region certified; the minimum over the union is unknown")
    win = min(cert, key=lambda e: e["val"])
    best = win["val"]

    n_dom, unresolved, worst_cert = 0, [], 0.0
    for e in entries:
        if e["kkt"] is not None and e["kkt"] <= TOL:
            worst_cert = max(worst_cert, e["kkt"])
            continue
        if e["lb"] >= best - 1e-9:
            n_dom += 1
        else:
            unresolved.append(e)

    bestinfo = {"region": win["reg"], "x": win["x"], "A": win["A"], "b": win["b"]}
    return best, bestinfo, theta, Hdiag, {
        "regions": len(entries), "certified": len(cert), "dominated": n_dom,
        "unresolved": len(unresolved),
        "unresolved_regions": [list(e["reg"]) for e in unresolved[:8]],
        "worst_certified_kkt": worst_cert,
        "settled": len(unresolved) == 0}


def J_frozen(a, b, varA, varB):
    """The frozen-LINEAR proxy.

    The range comparison is linearised at the original extrema and the ordering constraints
    are dropped, so this is the energy to flip a single linear contrast on four cells.  It
    is NOT the minimum over the region that keeps those extrema: that minimum would carry
    the ordering inequalities and would necessarily be at least `J_full`.  Dropping them is
    what lets the proxy underprice, and keeping the true union is what lets it overprice.
    """
    iM, im = int(np.argmax(a)), int(np.argmin(a))
    jM, jm = int(np.argmax(b)), int(np.argmin(b))
    gap = (a[iM] - a[im]) - (b[jM] - b[jm])
    if gap <= 0:
        return 0.0
    cells = {}
    for idx, v in [(("A", iM), varA[iM]), (("A", im), varA[im]),
                   (("B", jM), varB[jM]), (("B", jm), varB[jm])]:
        cells[idx] = cells.get(idx, 0.0) + v
    return float(gap * gap / (2.0 * sum(cells.values())))


def main():
    print("=" * 78)
    print("Paper A / A5: the frozen-extrema proxy misprices in both directions")
    print("=" * 78)

    # ---------------- FAMILY 1
    print("\n  Family 1: A=(0,1,1/2), B=(0,3/4,1/2), variance M on B's middle cell")
    print("  " + "-" * 70)
    a1 = np.array([0.0, 1.0, 0.5])
    b1 = np.array([0.0, 0.75, 0.5])
    rows1, kkt_ok1 = [], True
    for M in [1.0, 4.0, 16.0, 64.0, 256.0, 1024.0]:
        varA = np.array([1.0, 1.0, 1.0])
        varB = np.array([1.0, 1.0, M])
        jf = J_frozen(a1, b1, varA, varB)
        ju, info, theta, Hd, diag = J_full(a1, b1, varA, varB)
        stat, neg, comp = kkt_residual(theta, Hd, info["A"], info["b"], info["x"])
        if not diag["settled"] or max(stat, neg, comp) > 1e-5:
            kkt_ok1 = False
        rows1.append({"M": M, "J_frozen": jf, "J_full": ju, "ratio": ju / jf,
                      "bound_16_over_M": 16.0 / M,
                      "kkt": [stat, neg, comp],
                      "kkt_certified_regions": diag["certified"],
                      "kkt_dominated_regions": diag["dominated"],
                      "kkt_unresolved_regions": diag["unresolved"],
                      "worst_certified_kkt": diag["worst_certified_kkt"],
                      "regions": diag["regions"], "settled": diag["settled"]})
        print(f"      M={M:7.1f}:  J_frozen={jf:.6e}  J_full={ju:.6e}"
              f"   ratio={ju/jf:.4e}   {diag['certified']} certified"
              f" + {diag['dominated']} dominated + {diag['unresolved']} unresolved"
              f" of {diag['regions']}")
    check("family 1: every region is settled -- KKT-certified, or provably unable to"
          " beat the certified minimum", kkt_ok1,
          "no region is skipped, so the minimum over the union is established")
    check("family 1: J_frozen is the predicted 1/128", abs(rows1[0]["J_frozen"] - 1 / 128) < 1e-12,
          f"{rows1[0]['J_frozen']:.8f}")
    check("family 1: J_full <= 1/(8M), the explicit lift of B's middle cell",
          all(r["J_full"] <= 1.0 / (8 * r["M"]) + 1e-9 for r in rows1))
    check("family 1: the ratio obeys the 16/M bound at every M",
          all(r["ratio"] <= r["bound_16_over_M"] + 1e-9 for r in rows1))
    check("family 1: and it decays to zero, tracking 16/M once M is large",
          rows1[-1]["ratio"] < rows1[2]["ratio"] / 20
          and abs(rows1[-1]["ratio"] / rows1[-1]["bound_16_over_M"] - 1.0) < 0.05,
          f"ratio {rows1[-1]['ratio']:.4e} vs 16/M {rows1[-1]['bound_16_over_M']:.4e}")
    # The proxy is EXACT until the cheap cell is cheap enough to change the argmax.
    check("family 1: the proxy is exact at small M and only then breaks",
          abs(rows1[0]["ratio"] - 1.0) < 1e-9 and rows1[-1]["ratio"] < 0.02,
          "so the failure is a threshold effect, not a modelling artefact")

    # ---------------- FAMILY 2
    print("\n  Family 2: A=(0,1,3/4), B=(0,1/2,1/4), variance M on A's maximum")
    print("  " + "-" * 70)
    a2 = np.array([0.0, 1.0, 0.75])
    b2 = np.array([0.0, 0.5, 0.25])
    rows2, kkt_ok2 = [], True
    for M in [1.0, 4.0, 16.0, 64.0, 256.0, 1024.0]:
        varA = np.array([1.0, M, 1.0])
        varB = np.array([1.0, 1.0, 1.0])
        jf = J_frozen(a2, b2, varA, varB)
        ju, info, theta, Hd, diag = J_full(a2, b2, varA, varB)
        stat, neg, comp = kkt_residual(theta, Hd, info["A"], info["b"], info["x"])
        if not diag["settled"] or max(stat, neg, comp) > 1e-5:
            kkt_ok2 = False
        rows2.append({"M": M, "J_frozen": jf, "J_full": ju, "ratio": ju / jf,
                      "pred_lower": (M + 3) / 24.0, "kkt": [stat, neg, comp],
                      "kkt_certified_regions": diag["certified"],
                      "kkt_dominated_regions": diag["dominated"],
                      "kkt_unresolved_regions": diag["unresolved"],
                      "worst_certified_kkt": diag["worst_certified_kkt"],
                      "regions": diag["regions"], "settled": diag["settled"]})
        print(f"      M={M:7.1f}:  J_frozen={jf:.6e}  J_full={ju:.6e}"
              f"   ratio={ju/jf:.4e}   {diag['certified']} certified"
              f" + {diag['dominated']} dominated + {diag['unresolved']} unresolved"
              f" of {diag['regions']}")
    check("family 2: every region is settled -- KKT-certified, or provably unable to"
          " beat the certified minimum", kkt_ok2,
          "no region is skipped, so the minimum over the union is established")
    check("family 2: J_frozen is the predicted 1/(8(M+3))",
          all(abs(r["J_frozen"] - 1.0 / (8 * (r["M"] + 3))) < 1e-12 for r in rows2))
    check("family 2: J_full stays bounded below by 1/192, the runner-up obstruction",
          all(r["J_full"] >= 1.0 / 192 - 1e-9 for r in rows2),
          f"smallest J_full = {min(r['J_full'] for r in rows2):.6e}")
    check("family 2: the ratio grows at least like (M+3)/24 and diverges",
          all(r["ratio"] >= r["pred_lower"] - 1e-6 for r in rows2)
          and rows2[-1]["ratio"] > 40,
          f"ratio at M=1024 is {rows2[-1]['ratio']:.2f}")

    # ---------------- the two directions, together
    check("the proxy is wrong in BOTH directions on the same decision rule",
          rows1[-1]["ratio"] < 1 and rows2[-1]["ratio"] > 1,
          "no constant-factor guarantee is possible")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperA_frozen_proxy.py").read_bytes()).hexdigest(),"family1": [{k: v for k, v in r.items() if k != "kkt"} for r in rows1],
           "family2": [{k: v for k, v in r.items() if k != "kkt"} for r in rows2],
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperA_frozen_proxy.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
