#!/usr/bin/env python3
"""F05 probe: is the full-extrema alternative set strictly cheaper than the
fixed-extrema (pair-flip) relaxation, and does the optimizer really move the
argmin/argmax?

EVIDENCE CLASS: NUMERICAL EVIDENCE. Nothing here is proved. It tests whether the
region decomposition F05 proposes is correct, and whether the phenomenon it is
built for actually occurs, BEFORE any Lean is written.

MODEL (taken from run_functional_variance_stopping_lab_v4.py, not invented)
    capacity of relation r :  c_r(t) = max_a t[r,a] - min_a t[r,a]     (np.ptp)
    answer                 :  Top-k of c, k = 1 here
    KL to an alternative   :  (1/2) * sum_{r,a} w[r,a] * (t[r,a]-t'[r,a])^2 / s2[r,a]
                              known independent Gaussian cell variances s2,
                              positive sampling weights w.

WHAT `LeanFunctionalPairFlipCostV1` ALREADY COVERS
    `energy v w x y = x^2/(2v) + y^2/(2w)` with `pair_flip_lower` giving
    `gap^2 / (2(v+w))`. Read against this model, `v` and `w` are the EFFECTIVE
    variances of the two capacities WHEN hi/lo are pinned:
        v_r = s2[r,hi]/w[r,hi] + s2[r,lo]/w[r,lo].
    So that theorem is exactly the fixed-extrema relaxation. It cannot see a
    minimiser that switches which action is extremal.

THE DECOMPOSITION UNDER TEST
    Fix, per relation, an ordered pair (hi, lo). On the closed region where hi
    attains the max and lo the min, `c_r` is LINEAR, so the alternative
    constraint `c_out >= c_in` is linear and the region is a polyhedron;
    minimising the positive-definite cost over it is a convex QP. The regions
    (closed, overlapping only on ties) cover everything, since every point has
    some argmax and argmin. `region_min` below is the min over all K(K-1) per
    relation; `direct_min` is an independent penalty search over the raw
    alternative set, used only to check the decomposition did not miss anything.

CLOSED BOUNDARY vs STRICT REVERSAL
    The alternative is reported two ways. `c_out >= c_in` is the CLOSED set: its
    minimum is attained, at a tie. `c_out >= c_in + eta` for small eta > 0 is a
    strict reversal: its value decreases to the closed one as eta -> 0 but need
    not be attained at eta = 0. Both are printed; they are different estimands
    and the corpus already makes this distinction for the two-score case.
"""
from __future__ import annotations

import itertools
import json
import sys
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

ROOT = Path(__file__).resolve().parents[1]


def capacity(t):
    return t.max(axis=1) - t.min(axis=1)


def cost(tp, t, w, s2):
    return 0.5 * float(np.sum(w * (t - tp) ** 2 / s2))


def fixed_extrema_pair_flip(t, w, s2, r_in, r_out):
    """The value `LeanFunctionalPairFlipCostV1` gives, with hi/lo pinned at the
    extrema of `t`. v_r is the effective variance of capacity r."""
    def eff_var(r):
        hi, lo = int(np.argmax(t[r])), int(np.argmin(t[r]))
        return s2[r, hi] / w[r, hi] + s2[r, lo] / w[r, lo]
    v, wv = eff_var(r_in), eff_var(r_out)
    gap = float(capacity(t)[r_in] - capacity(t)[r_out])
    return gap ** 2 / (2.0 * (v + wv)), gap, v, wv


def region_qp(t, w, s2, r_in, r_out, hi_lo, eta=0.0):
    """Convex QP on one extrema-selection region. Returns (value, argmin) or None."""
    R, K = t.shape
    x0 = t.flatten().copy()

    cons = []
    for r in range(R):
        hi, lo = hi_lo[r]
        for a in range(K):
            if a != hi:
                cons.append({"type": "ineq",
                             "fun": (lambda x, r=r, hi=hi, a=a:
                                     x[r * K + hi] - x[r * K + a])})
            if a != lo:
                cons.append({"type": "ineq",
                             "fun": (lambda x, r=r, lo=lo, a=a:
                                     x[r * K + a] - x[r * K + lo])})
    hi_o, lo_o = hi_lo[r_out]
    hi_i, lo_i = hi_lo[r_in]
    cons.append({"type": "ineq",
                 "fun": (lambda x: (x[r_out * K + hi_o] - x[r_out * K + lo_o])
                         - (x[r_in * K + hi_i] - x[r_in * K + lo_i]) - eta)})

    f = lambda x: cost(x.reshape(R, K), t, w, s2)
    g = lambda x: (w * (x.reshape(R, K) - t) / s2).flatten()

    best = None
    rng = np.random.default_rng(0)
    for trial in range(3):
        start = x0 if trial == 0 else x0 + rng.normal(0, 0.35, size=x0.size)
        res = minimize(f, start, jac=g, constraints=cons, method="SLSQP",
                       options={"maxiter": 300, "ftol": 1e-11})
        if not res.success:
            continue
        xr = res.x.reshape(R, K)
        # verify feasibility rather than trusting the solver's flag
        ok = all(c["fun"](res.x) >= -1e-7 for c in cons)
        if ok and (best is None or res.fun < best[0]):
            best = (float(res.fun), xr.copy())
    return best


def direct_min(t, w, s2, r_in, r_out, eta=0.0, restarts=25, seed=1):
    """Independent check: penalty search on the RAW alternative, no regions."""
    R, K = t.shape
    rng = np.random.default_rng(seed)
    best = (np.inf, None)
    for _ in range(restarts):
        x0 = t.flatten() + rng.normal(0, 0.6, size=t.size)

        def pen(x, mu):
            tp = x.reshape(R, K)
            c = capacity(tp)
            viol = max(0.0, (c[r_in] + eta) - c[r_out])
            return cost(tp, t, w, s2) + mu * viol ** 2

        x = x0
        for mu in (1e2, 1e4, 1e6):
            r = minimize(pen, x, args=(mu,), method="Nelder-Mead",
                         options={"maxiter": 1200, "xatol": 1e-9, "fatol": 1e-11})
            x = r.x
        tp = x.reshape(R, K)
        c = capacity(tp)
        if c[r_out] >= c[r_in] + eta - 1e-7:
            v = cost(tp, t, w, s2)
            if v < best[0]:
                best = (v, tp.copy())
    return best


def analyse(name, t, w, s2, eta_list=(0.0, 1e-3)):
    t = np.asarray(t, float); w = np.asarray(w, float); s2 = np.asarray(s2, float)
    R, K = t.shape
    c = capacity(t)
    r_in = int(np.argmax(c)); r_out = 1 - r_in
    pf, gap, v, wv = fixed_extrema_pair_flip(t, w, s2, r_in, r_out)

    print(f"\n{'='*74}\n{name}\n{'='*74}")
    print(f"  theta      =\n{t}")
    print(f"  sigma^2    =\n{s2}")
    print(f"  weights    =\n{w}")
    print(f"  capacities = {c}   Top-1 = relation {r_in}   gap = {gap:.6f}")
    print(f"  original extrema: " + ", ".join(
        f"r{r}: hi={int(np.argmax(t[r]))} lo={int(np.argmin(t[r]))}" for r in range(R)))
    print(f"  fixed-extrema pair-flip value (Lean pair_flip_lower)"
          f" = {pf:.8f}   [v={v:.4f}, w={wv:.4f}]")

    out = {"name": name, "pair_flip": pf, "gap": gap, "results": {}}
    pairs = [p for p in itertools.permutations(range(K), 2)]
    for eta in eta_list:
        best = None
        for hl in itertools.product(pairs, repeat=R):
            got = region_qp(t, w, s2, r_in, r_out, hl, eta=eta)
            if got and (best is None or got[0] < best[0]):
                best = (got[0], got[1], hl)
        dv, dx = direct_min(t, w, s2, r_in, r_out, eta=eta)
        lbl = "closed  (c_out >= c_in)" if eta == 0 else f"strict  (+eta={eta:g})"
        print(f"\n  -- {lbl}")
        if best is None:
            print("     region decomposition: NO feasible region found")
            continue
        bv, bx, bhl = best
        new_ex = [(int(np.argmax(bx[r])), int(np.argmin(bx[r]))) for r in range(R)]
        old_ex = [(int(np.argmax(t[r])), int(np.argmin(t[r]))) for r in range(R)]
        moved = new_ex != old_ex
        print(f"     region min   = {bv:.8f}   region label {bhl}")
        print(f"     direct min   = {dv:.8f}   (independent penalty search)")
        print(f"     |region-direct| = {abs(bv-dv):.2e}"
              f"   -> decomposition {'AGREES' if abs(bv-dv) < 1e-4*max(1,bv) else '*** DISAGREES'}")
        print(f"     optimiser extrema {old_ex} -> {new_ex}"
              f"   {'*** EXTREMA CHANGED' if moved else '(unchanged)'}")
        print(f"     region min vs pair-flip: {bv:.8f} vs {pf:.8f}"
              f"   ratio {bv/pf if pf else float('nan'):.4f}")
        print(f"     argmin theta' =\n{bx}")
        out["results"][str(eta)] = {"region_min": bv, "direct_min": dv,
                                    "extrema_changed": moved,
                                    "old_extrema": old_ex, "new_extrema": new_ex,
                                    "region_label": [list(map(int, p)) for p in bhl],
                                    "argmin": bx.tolist()}
    return out


def main():
    W = np.ones((2, 3))
    cases = []

    # A. Plain: both relations have cheap, well-separated extrema. Expect the
    #    fixed-extrema relaxation to be tight and the extrema to stay put.
    cases.append(("A. uniform variances, no reason to switch",
                  [[0.0, 0.5, 1.0], [0.0, 0.4, 0.8]],
                  np.ones((2, 3))))

    # B. The out-relation has an EXPENSIVE max and min but a CHEAP middle cell.
    #    Raising the middle cell past the max is a longer move at a much lower
    #    price. If the full-extrema problem is ever strictly cheaper, here.
    cases.append(("B. out-relation has a cheap middle cell (sigma^2=100)",
                  [[0.0, 0.5, 1.0], [0.0, 0.4, 0.8]],
                  [[1.0, 1.0, 1.0], [1.0, 100.0, 1.0]]))

    # C. Same idea, pushed: the in-relation must shrink and its runner-up is
    #    close, so lowering its max past the runner-up kinks the cost.
    cases.append(("C. in-relation runner-up is close (kink on shrink)",
                  [[0.0, 0.97, 1.0], [0.0, 0.2, 0.4]],
                  [[1.0, 1.0, 1.0], [1.0, 1.0, 1.0]]))

    # D. Both effects at once.
    cases.append(("D. cheap middle out + close runner-up in",
                  [[0.0, 0.97, 1.0], [0.0, 0.2, 0.4]],
                  [[1.0, 1.0, 1.0], [1.0, 60.0, 1.0]]))

    results = [analyse(n, t, W, s2) for n, t, s2 in cases]
    outp = ROOT / "research" / "high_risk_20260910" / "f05_full_extrema_probe_v1.json"
    outp.parent.mkdir(parents=True, exist_ok=True)
    outp.write_text(json.dumps({"evidence_class": "NUMERICAL_EVIDENCE",
                                "model": "capacity = max-min over actions; "
                                         "KL = 0.5*sum w*(dtheta)^2/sigma^2",
                                "cases": results}, indent=1))
    print(f"\n\nwritten: {outp}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
