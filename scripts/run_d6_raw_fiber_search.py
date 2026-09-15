#!/usr/bin/env python3
"""E2: falsification search for D6-prime, restricted to RAW-rank-one fibres.

D6 (centred rank one => 2D <= (m-1) delta) is refuted.  D6-prime replaces the
hypothesis by RAW local contrast rank one, which is the same statement with the
additive gauge no longer free.  The counterexamples to D6 all live in that gauge.

Why the existing machinery transfers unchanged: for a fixed action-coefficient
tuple phi, raw rank one at every coordinate is a LINEAR condition on F (every
spanning column shares the same theta_i = phi_i), so the raw fibre V^raw_phi is
a linear subspace of dimension 2^m, sitting at codimension m(K-2) inside the
centred fibre V_lambda.  Searching inside it is unconstrained, exactly as in the
centred case, so `search_fiber` and its LP ascent apply verbatim.

The verdict is decided ONLY by the exact rational re-evaluation, never by the
float optimizer, and the exact leg also re-verifies raw rank one from the
definition rather than trusting the basis construction.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import importlib.util
import itertools
import json
import os
import sys
from fractions import Fraction

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from annotate_misalignment import (  # noqa: E402
    exact_evaluate, exact_rank, raw_contrast_matrix,
)

_spec = importlib.util.spec_from_file_location(
    "b3", os.path.join(HERE, "run_d6_direct_rankone_linear_fiber_search.py"))
b3 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(b3)

PROTOCOL_VERSION = "d6_raw_fiber_falsification_v1"


def raw_basis_exact(m: int, K: int, lam_int):
    """Exact integer spanning set of V^raw_phi, columns indexed by action."""
    phi = [(0,) + tuple(int(v) for v in row) for row in lam_int]
    acts = list(itertools.product(range(K), repeat=m))
    cols = [tuple(1 for _ in acts)]
    for i in range(m):
        cols.append(tuple(phi[i][a[i]] for a in acts))
    for size in range(2, m + 1):
        for S in itertools.combinations(range(m), size):
            col = []
            for a in acts:
                v = 1
                for i in S:
                    v *= phi[i][a[i]]
                col.append(v)
            cols.append(tuple(col))
    return acts, cols


def snap_exact(coeff: np.ndarray, denominator: int):
    return [Fraction(int(round(float(c) * denominator)), denominator) for c in coeff]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--alphabet", type=int, default=3)
    ap.add_argument("--fibers", type=int, default=24)
    ap.add_argument("--starts", type=int, default=3)
    ap.add_argument("--seed", type=int, default=20260905)
    ap.add_argument("--denominator", type=int, default=40)
    ap.add_argument("--optimizer", default="de+both+lp")
    ap.add_argument("--maxiter", type=int, default=2000)
    ap.add_argument("--lp-rounds", type=int, default=20)
    ap.add_argument("--lp-box", type=float, default=20.0)
    ap.add_argument("--min-topc-margin", type=float, default=0.01)
    ap.add_argument("--exact-leads", type=int, default=8)
    ap.add_argument("--exact-denominators", default="8,16,40,120")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    m, K = args.m, args.alphabet
    rng = np.random.default_rng(args.seed)
    q_rows = [[Fraction(1)] + [Fraction(0)] * (K - 1) for _ in range(m)]
    model = b3.FloatModel(m, K, q_rows, min_topc_margin=args.min_topc_margin)

    # Generic (halton) tuples first: structured tuples are symmetric across
    # coordinates, which inside the raw fibre forces equal response spans and
    # therefore Top-C ties, so they yield no admissible strict witness.
    lam_pool = b3.sample_lambdas(
        m, K, max(args.fibers * 3, 24), "halton", args.seed, args.denominator
    ) + b3.structured_lambdas(m, K)
    seen, lam_ints = set(), []
    for lam in lam_pool:
        li = b3.rationalize_lambda(np.asarray(lam), args.denominator)
        if li is None:
            continue
        key = tuple(tuple(r) for r in li)
        if key in seen:
            continue
        seen.add(key)
        lam_ints.append(li)
        if len(lam_ints) >= args.fibers:
            break

    denominators = [int(d) for d in args.exact_denominators.split(",")]
    leads, best_float, fibers_done = [], 0.0, 0

    for li in lam_ints:
        acts, cols = raw_basis_exact(m, K, li)
        B = np.asarray([[float(c[t]) for c in cols] for t in range(len(acts))],
                       dtype=float)
        if np.linalg.matrix_rank(B) != len(cols):
            # degenerate phi (a repeated or zero coefficient); skip rather than
            # silently search a smaller space than the label claims
            continue
        fibers_done += 1
        ratio, c, _evals, _log = b3.search_fiber(
            model, B, args.starts, rng, args.optimizer, args.maxiter,
            lp_rounds=args.lp_rounds, lp_box=args.lp_box)
        if c is None:
            continue
        best_float = max(best_float, float(ratio))
        leads.append((float(ratio), li, cols, acts, c))

    leads.sort(key=lambda t: -t[0])
    exact_results = []
    for ratio_f, li, cols, acts, c in leads[: args.exact_leads]:
        for den in denominators:
            coeff = snap_exact(c, den)
            vec = [sum((coeff[j] * cols[j][t] for j in range(len(cols))), Fraction(0))
                   for t in range(len(acts))]
            world = dict(zip(acts, vec))
            if all(v == 0 for v in vec):
                continue
            # exact re-verification of the HYPOTHESIS, from the definition
            ranks = [exact_rank(raw_contrast_matrix(world, m, K, i)) for i in range(m)]
            dec = exact_evaluate(world, q_rows, m, K)
            exact_results.append({
                "lambda_int": [list(r) for r in li],
                "snap_denominator": den,
                "float_ratio_lead": ratio_f,
                "raw_contrast_ranks": ranks,
                "raw_rank_one_all_coordinates": max(ranks) <= 1,
                "decision": dec,
            })

    admissible = [r for r in exact_results
                  if r["raw_rank_one_all_coordinates"]
                  and r["decision"]["ratio_float"] is not None
                  and r["decision"]["strict_topc"]]
    violations = [r for r in admissible if r["decision"]["violates"]]
    best_exact = max((r["decision"]["ratio_float"] for r in admissible), default=None)

    def _reject_reason(r):
        if not r["raw_rank_one_all_coordinates"]:
            return "hypothesis_failed_raw_rank_one"
        if r["decision"]["ratio_float"] is None:
            return "delta_square_zero_UNDEFINED"
        if not r["decision"]["strict_topc"]:
            return "top_c_tie_not_strict"
        return "admissible"

    rejections: dict = {}
    for r in exact_results:
        k = _reject_reason(r)
        rejections[k] = rejections.get(k, 0) + 1

    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": ("EXACT_RATIONAL_COUNTEREXAMPLE" if violations
                           else "NO_EXACT_COUNTEREXAMPLE_FROM_NUMERICAL_LEADS"),
        "development_only": True,
        "hypothesis_under_test": (
            "AllCoordinatesRawLocalContrastRankOne(F) and StrictTopC "
            "=> 2D <= (m-1) delta_square   [D6-prime]"),
        "generated_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "m": m, "alphabet": K,
        "raw_fiber_dim": 2 ** m,
        "centred_fiber_dim": 1 + m * (K - 1) + (2 ** m - 1 - m),
        "fibers_searched": fibers_done,
        "fibers_requested": args.fibers,
        "best_float_ratio": best_float,
        "best_exact_admissible_ratio": best_exact,
        "n_exact_leads_evaluated": len(exact_results),
        "n_admissible": len(admissible),
        "lead_disposition": rejections,
        "exact_leads": exact_results,
        "n_violations": len(violations),
        "violations": violations[:4],
        "limits": (
            "A float search maximises a LOWER bound per fibre and is "
            "path dependent, so absence of a violation here is NOT a proof of "
            "D6-prime. It is evidence at this fibre sample and this optimizer "
            "budget only."),
        "args": vars(args),
    }
    out = args.out or (f"research/d6_contrast_rank_falsification/"
                       f"E2_rawfiber_search_m{m}_K{K}.json")
    with open(out, "w") as fh:
        json.dump(payload, fh, indent=2)
    print(json.dumps({k: payload[k] for k in
                      ("out" ,) if False} | {
        "out": out,
        "evidence_class": payload["evidence_class"],
        "fibers_searched": fibers_done,
        "best_float_ratio": best_float,
        "best_exact_admissible_ratio": best_exact,
        "n_violations": len(violations),
        "lead_disposition": rejections,
    }, indent=2))


if __name__ == "__main__":
    main()
