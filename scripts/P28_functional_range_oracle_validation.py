#!/usr/bin/env python3
"""P28 -- F5.5 experiments 1 and 2: validate the polyhedral range oracle.

The closure guide of 2026-09-15 proves (and `LeanFunctionalRangeAlternativeUnionV1`
now machine-checks) the boundary identity

    C_j(lam) >= C_i(lam)  <=>  exists a,b in relation j, forall u,v in relation i:
                               lam_ja - lam_jb >= lam_iu - lam_iv,

so the CLOSED answer-changing set is exactly a union of convex polyhedra

    P_ijab = { lam : lam_iu - lam_iv - lam_ja + lam_jb <= 0  for all u,v },

and for a Gaussian design with information matrix M(x),

    J_mu(x) = min over (i in T, j not in T, a, b) of
              inf over lam in P_ijab of  (1/2)(lam-mu)^T M (lam-mu).

This script does NOT re-derive that identity.  It validates the IMPLEMENTATION of it
against the naive oracle the identity is supposed to replace: enumerate, for each
relation, which action is the argmax and which the argmin, restrict to that region
(where the range is linear), intersect with the half-space `C_j >= C_i`, and solve.
The two must agree on every instance.  Disagreement means the implementation, not the
theorem, is wrong.

Per the guide, PRIMAL AND DUAL witnesses are saved, not only objective numbers.  Each
inner QP is solved through its dual

    max over y >= 0 of  y^T(A mu - b) - (1/2) y^T A M^{-1} A^T y,
    lam = mu - M^{-1} A^T y,

so every reported value comes with `lam`, `y >= 0`, the primal feasibility residual
`max(A lam - b)`, the stationarity residual `||M(lam-mu) + A^T y||`, the
complementary-slackness residual, and the duality gap.

Instances: constructed SWITCHING cases (two relations with nearly equal range),
constructed KINK cases (a relation whose argmax changes under the alternative), and
generator-drawn worlds with heterogeneous known variances.

Experiment 1 is `--R 2 --K 3`; experiment 2 is `--R 3 --K 3`.  Both use k = 1.
"""
from __future__ import annotations
import argparse, itertools, json, time
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

REPO = Path(__file__).resolve().parents[1]


# ----------------------------------------------------------------- model ---
def ranges(lam, R, K):
    L = lam.reshape(R, K)
    return L.max(axis=1) - L.min(axis=1)


def topk_set(mu, R, K, k):
    C = ranges(mu, R, K)
    order = np.argsort(-C)
    return set(int(i) for i in order[:k]), C


def idx(r, a, K):
    return r * K + a


# -------------------------------------------------------------- QP solver ---
def solve_qp(Minv_diag, mu, A, b):
    """min (1/2)(lam-mu)^T M (lam-mu) s.t. A lam <= b, through the dual.

    Returns the value and a full primal/dual certificate."""
    m = A.shape[0]
    if m == 0:
        return {"value": 0.0, "lam": mu.tolist(), "y": [],
                "primal_residual": 0.0, "stationarity_residual": 0.0,
                "complementary_slackness": 0.0, "duality_gap": 0.0}
    AMinvAT = A @ (Minv_diag[:, None] * A.T)
    c = A @ mu - b

    def negdual(y):
        return -(c @ y - 0.5 * y @ AMinvAT @ y)

    def grad(y):
        return -(c - AMinvAT @ y)

    best = None
    for start in (np.zeros(m), np.maximum(c, 0.0), np.ones(m) * 1e-3):
        r = minimize(negdual, start, jac=grad, method="L-BFGS-B",
                     bounds=[(0.0, None)] * m,
                     options={"maxiter": 20000, "ftol": 1e-16, "gtol": 1e-14})
        if best is None or r.fun < best.fun:
            best = r
    y = np.maximum(best.x, 0.0)
    lam = mu - Minv_diag * (A.T @ y)
    primal_val = 0.5 * float((lam - mu) @ ((lam - mu) / Minv_diag))
    dual_val = float(c @ y - 0.5 * y @ AMinvAT @ y)
    slack = A @ lam - b
    return {
        "value": primal_val,
        "lam": lam.tolist(), "y": y.tolist(),
        "primal_residual": float(max(slack.max(), 0.0)),
        "stationarity_residual": float(np.linalg.norm(
            (lam - mu) / Minv_diag + A.T @ y)),
        "complementary_slackness": float(np.abs(y * slack).max()),
        "duality_gap": float(abs(primal_val - dual_val)),
    }


# --------------------------------------------------------- the two oracles ---
def polyhedral_oracle(mu, Minv, R, K, T):
    """min over (i in T, j not in T, a, b) of the QP on P_ijab."""
    n = R * K
    best = None
    for i in sorted(T):
        for j in range(R):
            if j in T:
                continue
            for a in range(K):
                for b in range(K):
                    rows = []
                    for u in range(K):
                        for v in range(K):
                            row = np.zeros(n)
                            row[idx(i, u, K)] += 1.0
                            row[idx(i, v, K)] -= 1.0
                            row[idx(j, a, K)] -= 1.0
                            row[idx(j, b, K)] += 1.0
                            if np.any(row):
                                rows.append(row)
                    A = np.array(rows) if rows else np.zeros((0, n))
                    sol = solve_qp(Minv, mu, A, np.zeros(A.shape[0]))
                    sol["region"] = {"i": i, "j": j, "a": a, "b": b}
                    if best is None or sol["value"] < best["value"]:
                        best = sol
    return best


def extrema_region_oracle(mu, Minv, R, K, T):
    """the naive oracle: enumerate (argmax, argmin) per relation, where the range is
    linear, and solve on each region intersected with `C_j >= C_i`."""
    n = R * K
    best = None
    for i in sorted(T):
        for j in range(R):
            if j in T:
                continue
            for (pi, qi) in itertools.product(range(K), repeat=2):
                for (pj, qj) in itertools.product(range(K), repeat=2):
                    rows = []
                    for (r, p, q) in ((i, pi, qi), (j, pj, qj)):
                        for a in range(K):
                            if a != p:
                                row = np.zeros(n)
                                row[idx(r, a, K)] += 1.0
                                row[idx(r, p, K)] -= 1.0
                                rows.append(row)          # lam_ra <= lam_rp
                            if a != q:
                                row = np.zeros(n)
                                row[idx(r, q, K)] += 1.0
                                row[idx(r, a, K)] -= 1.0
                                rows.append(row)          # lam_rq <= lam_ra
                    row = np.zeros(n)                      # C_i - C_j <= 0
                    row[idx(i, pi, K)] += 1.0
                    row[idx(i, qi, K)] -= 1.0
                    row[idx(j, pj, K)] -= 1.0
                    row[idx(j, qj, K)] += 1.0
                    rows.append(row)
                    A = np.array(rows)
                    sol = solve_qp(Minv, mu, A, np.zeros(A.shape[0]))
                    sol["region"] = {"i": i, "j": j,
                                     "argmax_i": pi, "argmin_i": qi,
                                     "argmax_j": pj, "argmin_j": qj}
                    if best is None or sol["value"] < best["value"]:
                        best = sol
    return best


# -------------------------------------------------------------- instances ---
def instances(R, K, rng, n_random):
    out = []
    # SWITCHING: two relations with nearly equal range
    mu = np.zeros((R, K))
    mu[0] = np.linspace(0.0, 1.0, K)
    mu[1] = np.linspace(0.0, 0.97, K)
    for r in range(2, R):
        mu[r] = np.linspace(0.0, 0.5, K)
    out.append(("switching_near_tie", mu.reshape(-1).copy()))
    # KINK: a relation whose argmax changes as the alternative moves
    mu = np.zeros((R, K))
    mu[0] = np.array([0.0, 0.9, 0.88] + [0.0] * (K - 3))[:K]
    mu[1] = np.array([0.0, 0.5, 0.45] + [0.0] * (K - 3))[:K]
    for r in range(2, R):
        mu[r] = np.array([0.0, 0.6, 0.55] + [0.0] * (K - 3))[:K]
    out.append(("kink_argmax_swap", mu.reshape(-1).copy()))
    # DEGENERATE: a flat relation (zero range, argmax = argmin)
    mu = np.zeros((R, K))
    mu[0] = np.linspace(0.0, 1.0, K)
    mu[1] = np.full(K, 0.3)
    for r in range(2, R):
        mu[r] = np.linspace(0.0, 0.4, K)
    out.append(("degenerate_flat_challenger", mu.reshape(-1).copy()))
    # generator-drawn worlds
    for s in range(n_random):
        out.append((f"random_{s:02d}", rng.normal(size=R * K)))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--R", type=int, required=True)
    ap.add_argument("--K", type=int, default=3)
    ap.add_argument("--k", type=int, default=1)
    ap.add_argument("--worlds", type=int, default=25)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    R, K, k = args.R, args.K, args.k
    out_path = Path(args.out or (REPO / "research/worker_P28_functional_range_20260915"
                                 / f"P28_range_oracle_R{R}_K{K}_k{k}.json"))
    if out_path.exists():
        raise SystemExit(f"Refusing to overwrite {out_path}")

    rng = np.random.default_rng(20260915 + R)
    rows = []
    t0 = time.time()
    for name, mu in instances(R, K, rng, args.worlds):
        # heterogeneous known variances and a fixed unit-price uniform design
        nu = 0.5 + rng.random(R * K) * 1.5
        x = np.full(R * K, 1.0 / (R * K))
        Minv = nu / x                                  # M = diag(x/nu)
        T, C = topk_set(mu, R, K, k)
        gap = float(np.sort(C)[-1] - np.sort(C)[-2]) if R >= 2 else float("inf")
        poly = polyhedral_oracle(mu, Minv, R, K, T)
        exh = extrema_region_oracle(mu, Minv, R, K, T)
        rel = abs(poly["value"] - exh["value"]) / max(exh["value"], 1e-12)
        agree = rel < 1e-6
        rows.append({
            "instance": name, "R": R, "K": K, "k": k,
            "mu": mu.tolist(), "nu": nu.tolist(), "design_x": x.tolist(),
            "ranges": C.tolist(), "T": sorted(T), "boundary_gap_at_truth": gap,
            "polyhedral": poly, "extrema_region": exh,
            "relative_difference": rel, "oracles_agree": bool(agree),
            "polyhedral_certificate_ok": bool(
                poly["primal_residual"] < 1e-7
                and poly["stationarity_residual"] < 1e-7
                and poly["complementary_slackness"] < 1e-7
                and poly["duality_gap"] < 1e-9),
        })
        flag = "OK " if agree else "!! "
        print(f"  {flag}{name:26s} T={sorted(T)}  poly={poly['value']:.10e}  "
              f"exh={exh['value']:.10e}  rel={rel:.2e}  "
              f"feas={poly['primal_residual']:.1e} stat={poly['stationarity_residual']:.1e} "
              f"gap={poly['duality_gap']:.1e}", flush=True)

    nagree = sum(1 for r in rows if r["oracles_agree"])
    ncert = sum(1 for r in rows if r["polyhedral_certificate_ok"])
    out = {
        "script": "P28_functional_range_oracle_validation.py",
        "experiment": f"F5.5 item {'1' if R == 2 else '2'}: R={R}, K={K}, k={k}",
        "what_is_tested": "the IMPLEMENTATION of the polyhedral union oracle against "
                          "the naive extrema-region oracle.  The identity itself is "
                          "LeanFunctionalRangeAlternativeUnionV1, not this script.",
        "qp_method": "solved through the dual  max_{y>=0} y^T(A mu - b) - (1/2) y^T A "
                     "M^{-1} A^T y,  with lam = mu - M^{-1} A^T y; primal feasibility, "
                     "stationarity, complementary slackness and the duality gap are all "
                     "reported per instance",
        "oracles_agree": nagree, "certificates_clean": ncert, "instances": len(rows),
        "wall_seconds": round(time.time() - t0, 1),
        "rows": rows,
        "not_established": [
            "Agreement validates the implementation of the union identity.  It does NOT "
            "prove the identity; that is the Lean module.",
            "A fixed uniform design is used: this is an ORACLE test, not a design "
            "optimisation.  The outer sup over designs is not attempted here.",
            "Floating-point QPs: the residual and gap columns are what make each value "
            "auditable.  No value here is an exact certificate.",
            "k = 1.  Larger k changes the Top-k boundary and is not tested.",
        ],
        "lean": "LeanFunctionalRangeAlternativeUnionV1 "
                "(range_ge_iff_exists_pair, alternative_union_polyhedra, pairRegion_convex)",
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("x") as f:
        json.dump(out, f, indent=1)
    print(f"\noracles agree on {nagree}/{len(rows)} instances; "
          f"clean primal/dual certificates on {ncert}/{len(rows)}")
    print(f"artifact: {out_path}")


if __name__ == "__main__":
    main()
