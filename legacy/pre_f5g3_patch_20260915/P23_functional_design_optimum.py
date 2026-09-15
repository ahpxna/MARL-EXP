#!/usr/bin/env python3
"""P23 -- Functional: is `w*` actually optimal over the design polytope?

The standing caveat is that `A d^2/2` is the value AT `w*`, and `Gamma* = sup_w J(w)`
is NOT claimed.  This script decides the question numerically instead of leaving it as
a caveat.

`J(w) = min over ordered pairs (a,b) of DISTINCT outsider cells of

    pairV(wI0, wI1, prec a, prec b, mean a - mean b),
    pairV(u,v,pa,pb,D) = u v (pa pb)(1-D)^2 / (2(u v (pa+pb) + pa pb (u+v))),
    prec c = w_c / sigma_c,

which is exactly the quantity `LeanFunctionalHeterogeneousLowerV1.energyU_ge_pairV`
bounds the energy of a flipping alternative by, and which the endpoint witness attains.
`J` is a minimum of quasi-concave pinch values on the budget simplex, so a local
maximiser found from many starts is strong evidence for the global one; the comparison
reported is `sup_w J(w)` versus `J(w*)`.

Lean counterpart: `LeanFunctionalDesignOptimalityV1` (concavity, the segment bound, and
the improvement criterion a search has to fail).
"""
import json, os
import numpy as np
from scipy.optimize import minimize

OUT = "research/worker_P23_functional_20260915"


def build(n, d, mid, vr):
    """cells: 0,1 = incumbent (means -1/2, +1/2, var 1);
             2,3 = outsider endpoints (+/- (1-d)/2, var 1);
             4.. = middle cells."""
    mean = np.concatenate([[-0.5, 0.5], [(1 - d) / 2, -(1 - d) / 2], mid])
    sig = np.concatenate([[1.0, 1.0], [1.0, 1.0], vr])
    return mean, sig


def pairV(u, v, pa, pb, D):
    den = 2 * (u * v * (pa + pb) + pa * pb * (u + v))
    if den <= 0:
        return 0.0
    return u * v * (pa * pb) * (1 - D) ** 2 / den


def Jvalue(w, mean, sig):
    """min over ordered pairs of DISTINCT outsider cells."""
    wI0, wI1 = w[0], w[1]
    prec = w[2:] / sig[2:]
    m = mean[2:]
    K = len(m)
    best = None
    for a in range(K):
        for b in range(K):
            if a == b:
                continue
            v = pairV(wI0, wI1, prec[a], prec[b], m[a] - m[b])
            if best is None or v < best:
                best = v
    return best


def wstar(n, d, mid, vr):
    g = 0.5 - np.abs(mid)
    S = float(np.sum(vr / g ** 2))
    A = 1.0 / (16 + d ** 2 * S)
    w = np.empty(n + 4)
    w[:4] = 4 * A                      # incumbent 2 + outsider 2
    w[4:] = d ** 2 * vr * A / g ** 2
    return w, A, S


def main():
    os.makedirs(OUT, exist_ok=True)
    rows = []
    rng = np.random.default_rng(20260915)
    for n, c in ((4, 1.0), (4, 1.5), (9, 1.0), (16, 1.0), (25, 1.0)):
        d = c / np.sqrt(n)
        # middle cells spread so that g_i >= d/2 strictly
        gmin = d / 2 * 1.6
        mid = np.linspace(-(0.5 - gmin), 0.5 - gmin, n)
        vr = np.ones(n)
        mean, sig = build(n, d, mid, vr)
        ws, A, S = wstar(n, d, mid, vr)
        ws = ws / ws.sum()
        Jstar = Jvalue(ws, mean, sig)
        formula = A * d ** 2 / 2
        # --- maximise J over the simplex
        def neg(z):
            w = np.abs(z) + 1e-14
            w = w / w.sum()
            return -Jvalue(w, mean, sig)
        best = None
        starts = [np.abs(ws) + 1e-9]
        for _ in range(40):
            starts.append(rng.random(n + 4) + 0.02)
        for z0 in starts:
            r = minimize(neg, z0, method="Nelder-Mead",
                         options={"maxiter": 200000, "maxfev": 200000,
                                  "xatol": 1e-13, "fatol": 1e-15})
            if best is None or r.fun < best.fun:
                best = r
        sup = -best.fun
        wopt = np.abs(best.x); wopt = wopt / wopt.sum()
        ratio = sup / Jstar
        rows.append({
            "n": n, "c": c, "d": d, "S": S, "A": A,
            "J_wstar_from_pairs": Jstar,
            "J_wstar_from_formula_Ad2_over_2": formula,
            "formula_matches_pairs": bool(abs(Jstar - formula) / formula < 1e-9),
            "sup_w_J": sup,
            "ratio_sup_over_Jstar": ratio,
            "wstar_is_optimal_within_1e-6": bool(ratio < 1 + 1e-6),
            "w_star": ws.tolist(),
            "w_opt": wopt.tolist(),
        })
        mark = "OPTIMAL   " if ratio < 1 + 1e-6 else "NOT optimal"
        print(f"  n={n:3d} c={c:.1f} d={d:.4f}: J(w*)={Jstar:.10e}  "
              f"formula={formula:.10e}  sup_w J={sup:.10e}  "
              f"ratio={ratio:.8f}  {mark}")

    allopt = all(r["wstar_is_optimal_within_1e-6"] for r in rows)
    out = {
        "script": "P23_functional_design_optimum.py",
        "question": "is w* a maximiser of J over the budget simplex, or only a design "
                    "whose value we happen to know?",
        "J_definition": "min over ordered pairs of distinct outsider cells of pairV -- "
                        "the quantity energyU_ge_pairV bounds the flipping energy by, "
                        "and which the endpoint witness attains",
        "rows": rows,
        "verdict": ("w* attains the design optimum in every cell tested"
                    if allopt else
                    "w* is NOT the design optimum: some design strictly beats it"),
        "all_cells_optimal": allopt,
        "not_established": [
            "Nelder-Mead on the simplex with 41 starts; J is a min of pinch values, so "
            "a local maximum is strong but not conclusive evidence for the global one.",
            "Whatever this finds, the LEAN results still only give the value AT w*: "
            "Gamma* = sup_w J(w) is not proved either way in Lean.",
            "Only the pair reduction is used; the full flipping-alternative infimum "
            "equals it by energyU_ge_pairV plus the witness, not by fiat.",
        ],
        "lean": "LeanFunctionalDesignOptimalityV1 (concavity, segment bound, improvement criterion)",
    }
    path = os.path.join(OUT, "P23_functional_design_optimum.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\nverdict: {out['verdict']}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
