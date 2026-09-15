#!/usr/bin/env python3
"""Measure how often the Top-C selection is a tie, inside vs outside the raw fibre.

Why this experiment exists
--------------------------
The preliminary E2 run found no violation inside the raw fibre, but it also
rejected most of its leads for Top-C ties.  That confounds the result: the
StrictTopC gate maps a tie to UNDEFINED, which zeroes the search objective, so a
higher tie rate depresses the attainable ratio for reasons of SEARCH DYNAMICS
rather than geometry.  Before any conclusion about D6-prime, the tie rate itself
has to be measured, with no optimizer anywhere in the loop.

Design
------
Fix an action-coefficient tuple phi.  Both fibres are then defined:

    V_lambda   centred fibre, dim 1 + m(K-1) + (2^m - 1 - m)
    V^raw_phi  raw fibre,     dim 2^m,  codimension m(K-2) inside V_lambda

Take orthonormal bases Q_raw (d_raw) and, inside V_lambda but orthogonal to
V^raw, the complement E (m(K-2) columns).  Sample

    F(s) = Q_raw a + s * E b,     a, b iid standard normal,

so s = 0 is an isotropic sample of the raw fibre and s = 1 is an isotropic
sample of the whole centred fibre.  Sweeping s interpolates between them with
the SAME sample size, the SAME phi and the SAME random stream, so the only thing
that varies is how much of the extra additive gauge is switched on.

This is a two-sample comparison of a distribution, not a search, so it cannot be
confounded by optimizer behaviour.  Reported per arm:

  * P(delta_square = 0)                     -- world is degenerate, no geometry
  * P(relative Top-C margin <= eps)          -- for a ladder of eps
  * quantiles of the relative Top-C margin
  * the ratio distribution, for context

A prediction worth recording BEFORE looking: if the mechanism claim is right,
tie rate falls monotonically in s, and most of the fall happens between s = 0
and small s.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import importlib.util
import itertools
import json
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "b3", os.path.join(HERE, "run_d6_direct_rankone_linear_fiber_search.py"))
b3 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(b3)

PROTOCOL_VERSION = "d6_topc_tie_frequency_v1"


def bases(m: int, K: int, lam_int):
    """Column matrices (K^m x d) for the raw fibre and the centred fibre."""
    phi = [(0,) + tuple(int(v) for v in row) for row in lam_int]
    acts = list(itertools.product(range(K), repeat=m))
    const = [1.0 for _ in acts]
    prods = []
    for size in range(2, m + 1):
        for S in itertools.combinations(range(m), size):
            col = []
            for a in acts:
                v = 1
                for i in S:
                    v *= phi[i][a[i]]
                col.append(float(v))
            prods.append(col)
    raw_extra = [[float(phi[i][a[i]]) for a in acts] for i in range(m)]
    ind_extra = [[1.0 if a[i] == u else 0.0 for a in acts]
                 for i in range(m) for u in range(1, K)]
    B_raw = np.asarray([const] + raw_extra + prods, dtype=float).T
    B_cen = np.asarray([const] + ind_extra + prods, dtype=float).T
    return B_raw, B_cen


def orth(A: np.ndarray, tol: float = 1e-10) -> np.ndarray:
    u, s, _ = np.linalg.svd(A, full_matrices=False)
    return u[:, s > tol * max(1.0, s[0])]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--alphabet", type=int, default=3)
    ap.add_argument("--phi-tuples", type=int, default=3)
    ap.add_argument("--samples", type=int, default=800)
    ap.add_argument("--s-values", default="0,0.05,0.15,0.4,1.0")
    ap.add_argument("--eps-ladder", default="0,0.005,0.01,0.02,0.05")
    ap.add_argument("--denominator", type=int, default=16)
    ap.add_argument("--seed", type=int, default=20260905)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    m, K = args.m, args.alphabet
    s_values = [float(x) for x in args.s_values.split(",")]
    eps_ladder = [float(x) for x in args.eps_ladder.split(",")]
    rng = np.random.default_rng(args.seed)

    q_rows = [[b3.Fraction(1)] + [b3.Fraction(0)] * (K - 1) for _ in range(m)]
    # margin gate off: this script measures the margin, it must not filter on it
    model = b3.FloatModel(m, K, q_rows, min_topc_margin=0.0)

    lam_pool = b3.sample_lambdas(m, K, args.phi_tuples * 4, "halton",
                                 args.seed, args.denominator)
    lam_ints, seen = [], set()
    for lam in lam_pool:
        li = b3.rationalize_lambda(np.asarray(lam), args.denominator)
        if li is None:
            continue
        key = tuple(tuple(r) for r in li)
        if key in seen:
            continue
        seen.add(key)
        lam_ints.append(li)
        if len(lam_ints) >= args.phi_tuples:
            break

    per_phi = []
    for li in lam_ints:
        B_raw, B_cen = bases(m, K, li)
        Q_raw = orth(B_raw)
        Q_cen = orth(B_cen)
        # complement of the raw fibre inside the centred fibre
        resid = Q_cen - Q_raw @ (Q_raw.T @ Q_cen)
        E = orth(resid)
        d_raw, d_cen, d_extra = Q_raw.shape[1], Q_cen.shape[1], E.shape[1]

        # one random stream reused across arms so arms differ only by s
        A = rng.standard_normal((args.samples, d_raw))
        Bc = rng.standard_normal((args.samples, d_extra)) if d_extra else None

        arms = []
        for s in s_values:
            margins, ratios, undefined = [], [], 0
            for t in range(args.samples):
                vec = Q_raw @ A[t]
                if d_extra and s != 0.0:
                    vec = vec + s * (E @ Bc[t])
                F = vec.reshape((K,) * m)
                d = model.evaluate(F)
                if d["delta_square"] <= 1e-12:
                    undefined += 1
                    continue
                margins.append(d["topc_margin_relative"])
                ratios.append(2.0 * d["regret"] / ((m - 1) * d["delta_square"]))
            margins_arr = np.asarray(margins)
            arms.append({
                "s": s,
                "n_sampled": args.samples,
                "n_undefined_delta_zero": undefined,
                "p_undefined": undefined / args.samples,
                "tie_rate_at_eps": {
                    str(e): float(np.mean(margins_arr <= e)) if margins_arr.size else None
                    for e in eps_ladder},
                "margin_quantiles": {
                    q: (float(np.quantile(margins_arr, q)) if margins_arr.size else None)
                    for q in (0.05, 0.25, 0.5, 0.75, 0.95)},
                "ratio_mean": float(np.mean(ratios)) if ratios else None,
                "ratio_p95": float(np.quantile(ratios, 0.95)) if ratios else None,
                "ratio_max": float(np.max(ratios)) if ratios else None,
            })
        per_phi.append({
            "lambda_int": [list(r) for r in li],
            "dim_raw": d_raw, "dim_centred": d_cen, "dim_complement": d_extra,
            "arms": arms,
        })

    # pooled view across phi tuples
    pooled = []
    for idx, s in enumerate(s_values):
        tie0 = [p["arms"][idx]["tie_rate_at_eps"][str(eps_ladder[0])] for p in per_phi]
        tie2 = [p["arms"][idx]["tie_rate_at_eps"][str(eps_ladder[min(2, len(eps_ladder)-1)])]
                for p in per_phi]
        rmax = [p["arms"][idx]["ratio_max"] for p in per_phi]
        pooled.append({
            "s": s,
            "mean_exact_tie_rate": float(np.mean([t for t in tie0 if t is not None])),
            f"mean_tie_rate_at_eps_{eps_ladder[min(2, len(eps_ladder)-1)]}":
                float(np.mean([t for t in tie2 if t is not None])),
            "mean_ratio_max": float(np.mean([r for r in rmax if r is not None])),
        })

    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": "NUMERICAL_DISTRIBUTIONAL_MEASUREMENT",
        "development_only": True,
        "generated_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "question": ("Is the Top-C tie rate structurally higher inside the raw "
                     "fibre than in the centred fibre, at matched sample size?"),
        "interpretation_rule": (
            "s = 0 is the raw fibre, s = 1 the centred fibre, same phi and same "
            "random stream. A monotone fall of the tie rate in s supports the "
            "claim that the extra additive gauge directions are what break "
            "Top-C ties. A flat profile refutes it and means the preliminary E2 "
            "lead rejections were not structural."),
        "m": m, "alphabet": K, "samples_per_arm": args.samples,
        "pooled": pooled,
        "per_phi": per_phi,
        "args": vars(args),
    }
    out = args.out or f"research/d6_contrast_rank_falsification/TOPC_TIE_RATE_m{m}_K{K}.json"
    with open(out, "w") as fh:
        json.dump(payload, fh, indent=2)
    print(json.dumps({"out": out, "pooled": pooled}, indent=2))


if __name__ == "__main__":
    main()
