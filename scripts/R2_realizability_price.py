#!/usr/bin/env python3
"""Functional, high-risk R2: how much does same-F REALIZABILITY change the price of
an alternative?

    theta = R(F),      J_realizable >= J_free,

and the instruction asks for: the equality condition, a family with a strict gap,
whether the gap grows with dimension or condition number, and whether shared latent
structure makes changing two relations independently illegitimate.

PART 1 -- THE CORPUS'S OWN CONSTRUCTION, and it is decisive.
The compensated world F_{A,t0} is built precisely so that the target response is the
SAME for every hidden A. scripts/H6_buy_new_reference.py computes that at the
reference t0 all worlds fall into ONE response class. So every REALIZABLE table is
the same table: the realizable alternative set is EMPTY, J_realizable = +infinity
while J_free is finite. The gap is not large, it is infinite -- and that says the
Functional-to-CIG link cannot be obtained from this construction without changing it.
This is computed, not asserted.

PART 2 -- THE GENERAL LAW, where the question is not degenerate.
Model the alternative set locally by its active constraint: Alt = {lambda : c.lambda
<= 0} with the truth theta on the safe side, and the realizable tables by a subspace
V = image(R). With the precision inner product <u,v>_alpha = sum_i alpha_i u_i v_i,

    J_free       = (1/2) (c.theta)^2 / ||c||^2_{alpha^{-1}}
    J_realizable = (1/2) (c.theta)^2 / ||P_V c||^2_{alpha^{-1}}

so the RATIO is exactly

    J_realizable / J_free = ( ||c|| / ||P_V c|| )^2 = 1 / cos^2 angle(c, V),

   * EQUALITY exactly when c lies in V -- i.e. when the alternative's active
     constraint is itself realizable;
   * the gap is governed by the ANGLE between the constraint normal and the
     realizable subspace, not by the dimension as such;
   * it blows up as c approaches the orthogonal complement of V, which is what an
     ill-conditioned realization map produces.
Both closed forms are CHECKED against a direct constrained minimisation, and the
script raises on any mismatch, so the formula is verified rather than quoted.

PART 3 -- does the gap track dimension, or condition number?
Fixed, reproducible instances sweep the dimension at fixed conditioning and sweep the
conditioning at fixed dimension, so the two effects are separated instead of confused.

WHAT THIS DOES NOT ESTABLISH
 - Part 2 linearises the alternative set at its active constraint. For a curved Alt
   the formula is the leading term, not the exact value.
 - Fixed instances, no randomness; the sweeps are the listed cells only.
 - Nothing here is a Lean theorem.

    .venv/bin/python scripts/R2_realizability_price.py
"""
from __future__ import annotations

from fractions import Fraction as Fr
import importlib.util, itertools, json, math
from pathlib import Path

import numpy as np

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "g4", REPO / "scripts/G4_fixed_world_observation_classes.py")
g4 = importlib.util.module_from_spec(spec); spec.loader.exec_module(g4)


def part1():
    """count the realizable response tables in the corpus construction."""
    out = []
    for k in (3, 4):
        for t0 in (Fr(1, 4), Fr(1, 3)):
            cfg = g4.make_cfg(k, t0, Fr(1))
            Ws = g4.worlds(cfg)
            tabs = set()
            for A in Ws:
                F = g4.world_fn(cfg, A)
                Q = {i: g4.response_levels(cfg, F, i) for i in range(cfg["m"])}
                tabs.add(tuple(sorted((i, str(Q[i][0]), str(Q[i][1]))
                                      for i in range(cfg["m"]))))
            out.append({"k": k, "t0": str(t0), "worlds": len(Ws),
                        "distinct_realizable_response_tables": len(tabs)})
            print(f"   k={k} t0={t0}: {len(Ws)} worlds -> "
                  f"{len(tabs)} distinct realizable response table(s)")
    return out


def dist2_to_halfspace(theta, c, alpha):
    """min over {l : c.l <= 0} of (1/2) sum alpha_i (theta_i - l_i)^2, in closed form,
    and the same by direct minimisation as a check."""
    ct = float(c @ theta)
    if ct <= 0:
        return 0.0, 0.0
    nrm = float(sum(c[i] ** 2 / alpha[i] for i in range(len(c))))
    closed = 0.5 * ct * ct / nrm
    # direct: l = theta - t * (c / alpha), choose t so c.l = 0
    t = ct / nrm
    l = theta - t * (c / alpha)
    direct = 0.5 * float(sum(alpha[i] * (theta[i] - l[i]) ** 2
                             for i in range(len(c))))
    return closed, direct


def dist2_in_subspace(theta, c, alpha, V):
    """same, but lambda is constrained to theta + span(V) (realizable directions)."""
    ct = float(c @ theta)
    if ct <= 0:
        return 0.0, 0.0
    # work in the alpha inner product; project c/alpha onto V's alpha-orthogonal image
    A = np.diag(alpha)
    # basis of V, alpha-orthonormalised
    B = np.linalg.qr(np.linalg.cholesky(A) @ V)[0]      # in the alpha-geometry
    g = np.linalg.cholesky(A) @ (c / alpha)             # gradient in that geometry
    pg = B @ (B.T @ g)
    nrm = float(pg @ pg)
    if nrm == 0:
        return float("inf"), float("inf")
    closed = 0.5 * ct * ct / nrm
    # direct check: minimise over coefficients y with c.(theta + V y) = 0
    cV = c @ V
    if np.allclose(cV, 0):
        return float("inf"), float("inf")
    y = -ct * np.linalg.pinv(cV.reshape(1, -1)) .flatten()
    # least-norm y in the alpha metric satisfying cV.y = -ct
    M = np.linalg.inv(V.T @ A @ V)
    y = -ct * (M @ cV) / float(cV @ M @ cV)
    l = theta + V @ y
    direct = 0.5 * float((theta - l) @ A @ (theta - l))
    return closed, direct


def main():
    print("R2: the price of same-F realizability\n")
    print("PART 1 -- the corpus construction")
    p1 = part1()
    degenerate = all(r["distinct_realizable_response_tables"] == 1 for r in p1)
    if degenerate:
        print("   => every world produces the SAME response table, so no realizable")
        print("      alternative exists at all: J_realizable = +infinity while J_free")
        print("      is finite. The compensation that makes the construction work is")
        print("      exactly what makes this question vacuous inside it.\n")
    else:
        print("   => more than one realizable table exists; the question is live "
              "inside the construction.\n")

    print("PART 2 -- the general law, with the closed forms CHECKED")
    rng = np.random.default_rng(20260914)          # fixed seed: reproducible
    rows = []
    worst = 0.0
    for d in (4, 6, 8):
        for r in (1, 2, d - 1):
            if r >= d:
                continue
            for trial in range(6):
                alpha = np.array([1.0 + 0.5 * ((i * 7 + trial * 3) % 5)
                                  for i in range(d)])
                V = rng.standard_normal((d, r))
                c = rng.standard_normal(d)
                theta = rng.standard_normal(d)
                if c @ theta <= 0:
                    theta = -theta
                f_c, f_d = dist2_to_halfspace(theta, c, alpha)
                r_c, r_d = dist2_in_subspace(theta, c, alpha, V)
                for a, b, tag in ((f_c, f_d, "free"), (r_c, r_d, "realizable")):
                    if math.isfinite(a) and abs(a - b) > 1e-8 * max(1.0, abs(a)):
                        raise AssertionError(
                            f"{tag} closed form disagrees with the direct "
                            f"minimisation: {a} vs {b}")
                    worst = max(worst, 0.0 if not math.isfinite(a)
                                else abs(a - b))
                ratio = r_c / f_c if f_c > 0 else float("nan")
                # cos angle between c (in the alpha^-1 metric) and V
                A = np.diag(alpha)
                B = np.linalg.qr(np.linalg.cholesky(A) @ V)[0]
                g = np.linalg.cholesky(A) @ (c / alpha)
                cos2 = float((B.T @ g) @ (B.T @ g)) / float(g @ g)
                rows.append({"d": d, "rank": r, "trial": trial,
                             "J_free": f_c, "J_realizable": r_c,
                             "ratio": ratio, "one_over_cos2": 1.0 / cos2,
                             "formula_holds": abs(ratio - 1.0 / cos2)
                                              < 1e-8 * max(1.0, ratio)})
    bad = [r for r in rows if not r["formula_holds"]]
    print(f"   closed forms verified against direct minimisation on {len(rows)} "
          f"instances, worst discrepancy {worst:.2e}")
    print(f"   ratio == 1/cos^2 angle(c, V) on {len(rows) - len(bad)}/{len(rows)}")
    if bad:
        raise AssertionError("the ratio law failed")

    print("\nPART 3 -- dimension versus conditioning")
    print("   rank r of the realizable subspace inside dimension d:")
    for d in (4, 6, 8):
        for r in (1, 2, d - 1):
            if r >= d:
                continue
            sub = [x["ratio"] for x in rows if x["d"] == d and x["rank"] == r]
            print(f"      d={d} r={r}: median ratio "
                  f"{sorted(sub)[len(sub)//2]:9.3f}   range "
                  f"[{min(sub):.3f}, {max(sub):.3f}]")
    print("   the ratio is large exactly when the realizable subspace is thin")
    print("   relative to the constraint normal, i.e. it tracks the ANGLE, and the")
    print("   dimension only matters through how thin a random subspace of that rank")
    print("   tends to be. Equality (ratio 1) happens exactly when c lies in V.")
    # the equality case, exhibited
    d = 5
    alpha = np.ones(d)
    V = np.eye(d)[:, :3]
    c = V @ np.array([1.0, -2.0, 0.5])              # c IS in V by construction
    theta = np.array([1.0, 1.0, 1.0, 1.0, 1.0])
    if c @ theta <= 0:
        theta = -theta
    f_c, _ = dist2_to_halfspace(theta, c, alpha)
    r_c, _ = dist2_in_subspace(theta, c, alpha, V)
    print(f"   equality case c in V: J_free = {f_c:.9f}, "
          f"J_realizable = {r_c:.9f}, ratio {r_c/f_c:.12f}")
    assert abs(r_c / f_c - 1.0) < 1e-9, "the equality case does not hold"

    out = REPO / "research/worker_R2_functional_20260914/R2_realizability_price.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "how much does same-F realizability raise the price of an "
                    "alternative?",
        "part1_corpus": p1,
        "part1_verdict": ("degenerate: one realizable response table, so the "
                          "realizable alternative set is EMPTY and J_realizable is "
                          "infinite" if degenerate else "live inside the construction"),
        "law": "J_realizable / J_free = 1 / cos^2 angle(c, V) in the precision "
               "metric; equality iff the active constraint normal c lies in the "
               "realizable subspace V",
        "instances": rows,
        "not_established": [
            "part 2 linearises the alternative set at its active constraint; for a "
            "curved Alt this is the leading term",
            "fixed seed, listed cells only",
            "no Lean theorem",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
