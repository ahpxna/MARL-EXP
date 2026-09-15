#!/usr/bin/env python3
"""Functional target D: the measurement graph, with a physical cost.

    Y_ab ~ N(theta_a - theta_b, sigma_ab^2),   sum_ab kappa_ab x_ab <= 1,

and the question is the phase law: as the cost structure `kappa` changes, does the
optimal design measure LOCAL contrasts (neighbouring actions), LONG contrasts (far
apart), or CELL observations (a single action against a known zero)? The deliverable
is the map  kappa-regime -> support of the optimal design.

THE OBJECTIVE, and why it is the right one rather than a renamed one. The answer is
the Top-1 action. A design `x` puts mass on measurements `e` with unit coefficient
vectors `c_e` (`e_a - e_b` for a contrast, `e_a` for a cell observation) and noise
`sigma_e`, giving the information matrix `M(x) = sum_e x_e c_e c_e^T / sigma_e^2`. The
cheapest alternative that flips the answer from `i*` to `j` sits on the hyperplane
`theta_{i*} = theta_j`, so

    value(x) = min over j != i*  of  (theta_{i*} - theta_j)^2 / (2 * v_j^T M(x)^+ v_j),
    v_j = e_{i*} - e_j,

with the value 0 when `v_j` leaves the range of `M(x)` -- i.e. when the design simply
cannot tell `i*` from `j`. `v^T M^+ v` is convex in `M`, so its reciprocal is concave
and the objective is a minimum of concave functions: the programme is a CONCAVE
maximisation and a local optimum is global.

WHAT IS COMPUTED. For each cost regime the concave programme is solved from many
fixed starts, the support of the optimum is read off at a fixed tolerance, and the
regimes are tabulated. A CONTROL checks the two limits: when cell observations are
free the support must be cells, and when they are prohibitive it must be contrasts. If
the control fails the sweep means nothing.

WHAT THIS DOES NOT ESTABLISH
 - Floating point, and a numerical optimum: the support is read at a tolerance, so a
   weight just below it is reported as absent. No exact certificate is produced.
 - Gaussian with KNOWN variances, Top-1 only, static (non-adaptive) design.
 - Fixed instances; the boundaries reported are where the support changes ON THIS
   GRID, not solved-for phase boundaries.
 - Nothing here is a sample-complexity statement: the objective is the information
   rate per unit budget.

    .venv/bin/python scripts/F8_contrast_graph_phases.py
"""
from __future__ import annotations

import itertools, json
from pathlib import Path

import numpy as np
from scipy.optimize import linprog, minimize

REPO = Path(__file__).resolve().parents[1]


def measurements(K, include_cells=True):
    out = []
    for a, b in itertools.combinations(range(K), 2):
        c = np.zeros(K); c[a] = 1.0; c[b] = -1.0
        out.append((("contrast", a, b), c, abs(a - b)))
    if include_cells:
        for a in range(K):
            c = np.zeros(K); c[a] = 1.0
            out.append((("cell", a), c, 0))
    return out


def value(x, meas, sig2, theta, istar):
    K = len(theta)
    M = np.zeros((K, K))
    for xi, (_lab, c, _d) in zip(x, meas):
        M += xi * np.outer(c, c) / sig2[_lab]
    Mp = np.linalg.pinv(M, rcond=1e-10)
    best = None
    for j in range(K):
        if j == istar:
            continue
        v = np.zeros(K); v[istar] = 1.0; v[j] = -1.0
        # v must lie in the range of M, else the design cannot separate i* from j
        if np.linalg.norm(M @ (Mp @ v) - v) > 1e-7:
            return 0.0
        q = float(v @ Mp @ v)
        if q <= 0:
            return 0.0
        val = (theta[istar] - theta[j]) ** 2 / (2 * q)
        if best is None or val < best:
            best = val
    return best


def solve(meas, sig2, theta, istar, kappa, starts=10):
    """THE RIGHT FORMULATION. `v^T M(x)^+ v` for `v = e_i - e_j` is the EFFECTIVE
    RESISTANCE between i and j in the network whose conductances are `x_e/sigma_e^2`
    (a contrast is an edge, a cell observation an edge to ground). Effective resistance
    is CONVEX in the conductances, so

        maximise min_j Delta_j^2/(2 R_j(x))   subject to  kappa.x <= 1, x >= 0

    is exactly  minimise t  subject to  2 R_j(x)/Delta_j^2 <= t,  a convex programme
    with an ANALYTIC gradient  dR_j/dx_e = -(v_j^T M^+ c_e)^2 / sigma_e^2.  Solving it
    that way instead of by a derivative-free search is what makes the optimum sparse
    and the reported support meaningful."""
    n = len(meas)
    K = len(theta)
    kap = np.array([kappa[lab] for lab, _c, _d in meas])
    C = np.array([c for _lab, c, _d in meas])
    inv = np.array([1.0 / sig2[lab] for lab, _c, _d in meas])
    others = [j for j in range(K) if j != istar]
    V = []
    D2 = []
    for j in others:
        v = np.zeros(K); v[istar] = 1.0; v[j] = -1.0
        V.append(v); D2.append((theta[istar] - theta[j]) ** 2)
    V = np.array(V); D2 = np.array(D2)

    def MM(x):
        return (C * (x * inv)[:, None]).T @ C

    def resist_and_grad(x):
        M = MM(x)
        Mp = np.linalg.pinv(M, rcond=1e-12)
        R = np.einsum('ij,jk,ik->i', V, Mp, V)
        # dR_j/dx_e = -(v_j^T M^+ c_e)^2 / sigma_e^2
        W = V @ Mp @ C.T                      # (nj, n)
        G = -(W ** 2) * inv[None, :]
        return R, G

    def cons_f(z):
        x, t = z[:n], z[n]
        R, _ = resist_and_grad(np.maximum(x, 0.0))
        return t - 2.0 * R / D2

    def cons_j(z):
        x, t = z[:n], z[n]
        _, G = resist_and_grad(np.maximum(x, 0.0))
        J = np.zeros((len(others), n + 1))
        J[:, :n] = -2.0 * G / D2[:, None]
        J[:, n] = 1.0
        return J

    cons = [{"type": "ineq", "fun": cons_f, "jac": cons_j},
            {"type": "ineq", "fun": lambda z: 1.0 - float(kap @ z[:n]),
             "jac": lambda z: np.concatenate([-kap, [0.0]])}]
    bnds = [(1e-9, None)] * n + [(1e-12, None)]
    rng = np.random.default_rng(20260914)
    best = (0.0, None)
    for s_i in range(starts):
        x0 = (np.ones(n) if s_i == 0 else np.abs(rng.standard_normal(n)) + 0.05)
        x0 = x0 / float(kap @ x0)
        R0, _ = resist_and_grad(x0)
        z0 = np.concatenate([x0, [float(np.max(2.0 * R0 / D2)) + 1e-6]])
        try:
            r = minimize(lambda z: z[n], z0, jac=lambda z: np.eye(n + 1)[n],
                         constraints=cons, bounds=bnds, method="SLSQP",
                         options={"maxiter": 500, "ftol": 1e-14})
        except Exception:
            continue
        x = np.maximum(r.x[:n], 0.0)
        sbud = float(kap @ x)
        if sbud <= 0:
            continue
        x = x / sbud
        v = value(x, meas, sig2, theta, istar)
        if v > best[0]:
            best = (v, x)
    return best


def support(w, meas, tol=1e-3):
    tot = float(np.sum(w))
    return [lab for wi, (lab, _c, _d) in zip(w, meas) if wi > tol * tot]


def kind(sup):
    has_cell = any(s[0] == "cell" for s in sup)
    cons = [s for s in sup if s[0] == "contrast"]
    if has_cell and not cons:
        return "cells only"
    if cons and not has_cell:
        spans = {abs(s[1] - s[2]) for s in cons}
        return ("local contrasts" if spans == {1}
                else ("long contrasts" if min(spans) > 1 else "mixed contrasts"))
    return "cells + contrasts"


def main():
    K = 4
    theta = np.array([1.0, 0.7, 0.4, 0.0])
    istar = 0
    meas = measurements(K)
    sig2 = {}
    for lab, _c, _d in meas:
        sig2[lab] = 1.0

    print("Functional: the measurement-graph phase law\n")
    print("CONTROL -- the two limits must come out right")
    ctrl = []
    for name, cellcost in (("cells nearly free", 1e-3), ("cells prohibitive", 1e3)):
        kappa = {lab: (cellcost if lab[0] == "cell" else 1.0) for lab, _c, _d in meas}
        v, w = solve(meas, sig2, theta, istar, kappa)
        sup = support(w, meas)
        print(f"   {name:20s}: value {v:.6f}   support {kind(sup)}  {sup}")
        ctrl.append({"regime": name, "value": v, "support": [list(map(str, s))
                                                             for s in sup],
                     "kind": kind(sup)})
    if ctrl[0]["kind"] not in ("cells only", "cells + contrasts"):
        print("   WARNING: with nearly-free cells the optimum is not cell-dominated;")
        print("   the sweep below should not be trusted.")
    if "cell" in str(ctrl[1]["support"]):
        print("   WARNING: with prohibitive cells the optimum still buys one.")

    print("\nSWEEP -- long contrasts priced by distance: kappa(a,b) = 1 + lam*(|a-b|-1)")
    rows = []
    for cellcost in (0.5, 2.0, 10.0, 1e3):
        print(f"   cell cost {cellcost:g}")
        for lam in (0.0, 0.25, 0.5, 1.0, 2.0, 4.0):
            kappa = {}
            for lab, _c, d in meas:
                kappa[lab] = cellcost if lab[0] == "cell" else 1.0 + lam * (d - 1)
            v, w = solve(meas, sig2, theta, istar, kappa)
            sup = support(w, meas)
            print(f"      lam={lam:4g}: value {v:.6f}   {kind(sup):18s} {sup}")
            rows.append({"cell_cost": cellcost, "lambda": lam, "value": v,
                         "support": [list(map(str, s)) for s in sup],
                         "kind": kind(sup)})
        print()

    kinds = sorted({r["kind"] for r in rows})
    print("VERDICT")
    print(f"   regimes observed on this grid: {kinds}")
    # where does the support change?
    changes = []
    for cellcost in sorted({r["cell_cost"] for r in rows}):
        seq = [r for r in rows if r["cell_cost"] == cellcost]
        for a, b in zip(seq, seq[1:]):
            if a["kind"] != b["kind"]:
                changes.append(("lambda", cellcost, a["lambda"], b["lambda"],
                                a["kind"], b["kind"]))
    for lam in sorted({r["lambda"] for r in rows}):
        seq = sorted([r for r in rows if r["lambda"] == lam],
                     key=lambda r: r["cell_cost"])
        for a, b in zip(seq, seq[1:]):
            if a["kind"] != b["kind"]:
                changes.append(("cell_cost", lam, a["cell_cost"], b["cell_cost"],
                                a["kind"], b["kind"]))
    if changes:
        print("   support changes (BOTH directions of the grid are compared; an")
        print("   earlier version only compared along lambda and so reported 'no")
        print("   transition' while the cell-cost axis was moving the support):")
        for axis, fixed, u0, u1, k0, k1 in changes:
            print(f"      along {axis}: at {'cell cost' if axis=='lambda' else 'lam'}"
                  f"={fixed:g}, between {u0:g} and {u1:g}: {k0} -> {k1}")
    else:
        print("   the support type never changed anywhere on this grid.")
    print("\n   These are GRID observations, not solved phase boundaries, and the")
    print("   support is read at a 1e-3 relative tolerance in float arithmetic.")

    out = REPO / "research/worker_F8_functional_20260914/F8_contrast_graph_phases.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "model": "Y_ab ~ N(theta_a - theta_b, sigma_ab^2) and cell observations; "
                 "budget sum kappa x <= 1; objective min_j (theta_i* - theta_j)^2 / "
                 "(2 v_j^T M^+ v_j)",
        "theta": theta.tolist(), "istar": istar,
        "control": ctrl, "sweep": rows,
        "support_changes": [{"axis": ax, "fixed": f, "from_value": u0,
                             "to_value": u1, "from": k0, "to": k1}
                            for ax, f, u0, u1, k0, k1 in changes],
        "not_established": [
            "float arithmetic and a numerical optimum; support read at a tolerance",
            "Gaussian with known variances, Top-1 only, static design",
            "grid observations, not solved phase boundaries",
            "an information rate per unit budget, not a sample complexity",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
