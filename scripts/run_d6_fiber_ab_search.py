#!/usr/bin/env python3
"""A/B falsification search: RAW fibre vs CENTRED fibre, same code path.

Absence of a counterexample from a lower-bound search is never a proof.  What
can make it evidence is a POSITIVE CONTROL: run the identical code, budget,
seeds and fibre sampling on the centred fibre, where counterexamples are known
to exist (best recorded strict ratio 1.1611, B3small_m6_d16_s13).  If the
control reproduces a violation and the raw arm does not, the difference is
attributable to the hypothesis rather than to the search.

Two design faults of the first raw-fibre run are fixed here.

1.  The search model was gated on the StrictTopC margin, which maps a tie to
    UNDEFINED and therefore zeroes the objective.  The optimizer could not
    traverse tie regions.  The search model is now UNGATED (`--search-gate 0`)
    and the strict gate is applied only at exact certification.
2.  Leads were reported only after the gate, so a gate rejection was
    indistinguishable from a genuinely low ratio.  Both the gated and the
    ungated exact maxima are now reported.

Measured separately (TOPC_TIE_RATE_m6_K3.json): the Top-C tie rate is NOT higher
inside the raw fibre -- it is flat at about 0.26 at eps = 0.01 across the whole
interpolation from the raw fibre to the centred fibre.  So the tie rejections in
the first run were an artifact of lead selection, not of the geometry.  That is
why the fix above is about the optimizer, not about the fibre.
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
    centred_profile_matrix, exact_evaluate, exact_rank, product_response,
    raw_contrast_matrix,
)

_spec = importlib.util.spec_from_file_location(
    "b3", os.path.join(HERE, "run_d6_direct_rankone_linear_fiber_search.py"))
b3 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(b3)

PROTOCOL_VERSION = "d6_fiber_ab_falsification_v1"


def raw_basis_exact(m: int, K: int, lam_int):
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


def centred_basis_exact(m: int, K: int, lam_int):
    acts = list(itertools.product(range(K), repeat=m))
    return acts, b3.closed_form_basis_exact(m, K, lam_int)


def hypothesis_ranks(world, m, K, kind, q_rows):
    """Re-verify the HYPOTHESIS exactly, from the definitions."""
    if kind == "raw":
        return [exact_rank(raw_contrast_matrix(world, m, K, i)) for i in range(m)]
    ranks = []
    for i in range(m):
        raw_rows = raw_contrast_matrix(world, m, K, i)
        alpha = [product_response(world, q_rows, i, u) - product_response(world, q_rows, i, 0)
                 for u in range(K)]
        ranks.append(exact_rank(centred_profile_matrix(raw_rows, alpha)))
    return ranks


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--fiber-kind", choices=("raw", "centred"), required=True)
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--alphabet", type=int, default=3)
    ap.add_argument("--fibers", type=int, default=48)
    ap.add_argument("--starts", type=int, default=6)
    ap.add_argument("--seed", type=int, default=20260905)
    ap.add_argument("--denominator", type=int, default=16)
    ap.add_argument("--optimizer", default="de+both+lp")
    ap.add_argument("--maxiter", type=int, default=1500)
    ap.add_argument("--lp-rounds", type=int, default=40)
    ap.add_argument("--lp-box", type=float, default=20.0)
    ap.add_argument("--search-gate", type=float, default=0.0,
                    help="StrictTopC margin used DURING the float search. Keep 0: "
                         "gating the search objective makes tie regions untraversable.")
    ap.add_argument("--certify-margin", type=float, default=0.02,
                    help="StrictTopC margin required at exact certification.")
    ap.add_argument("--exact-leads", type=int, default=24)
    ap.add_argument("--exact-denominators", default="8,16,40,120,360")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    m, K, kind = args.m, args.alphabet, args.fiber_kind
    rng = np.random.default_rng(args.seed)
    q_rows = [[Fraction(1)] + [Fraction(0)] * (K - 1) for _ in range(m)]
    model = b3.FloatModel(m, K, q_rows, min_topc_margin=args.search_gate)

    lam_pool = b3.sample_lambdas(m, K, max(args.fibers * 3, 32), "halton",
                                 args.seed, args.denominator) + \
        b3.structured_lambdas(m, K)
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
        if len(lam_ints) >= args.fibers:
            break

    build = raw_basis_exact if kind == "raw" else centred_basis_exact
    denominators = [int(d) for d in args.exact_denominators.split(",")]
    leads, best_float, fibers_done = [], 0.0, 0

    for li in lam_ints:
        acts, cols = build(m, K, li)
        B = np.asarray([[float(c[t]) for c in cols] for t in range(len(acts))],
                       dtype=float)
        if np.linalg.matrix_rank(B) != len(cols):
            continue          # degenerate phi: the label would overstate the space
        fibers_done += 1
        ratio, c, _ev, _log = b3.search_fiber(
            model, B, args.starts, rng, args.optimizer, args.maxiter,
            lp_rounds=args.lp_rounds, lp_box=args.lp_box)
        if c is None:
            continue
        best_float = max(best_float, float(ratio))
        leads.append((float(ratio), li, cols, acts, c))

    leads.sort(key=lambda t: -t[0])
    results = []
    for ratio_f, li, cols, acts, c in leads[: args.exact_leads]:
        for den in denominators:
            coeff = [Fraction(int(round(float(v) * den)), den) for v in c]
            vec = [sum((coeff[j] * cols[j][t] for j in range(len(cols))), Fraction(0))
                   for t in range(len(acts))]
            if all(v == 0 for v in vec):
                continue
            world = dict(zip(acts, vec))
            ranks = hypothesis_ranks(world, m, K, kind, q_rows)
            dec = exact_evaluate(world, q_rows, m, K)
            rel = dec["topc_margin_relative_float"]
            results.append({
                "lambda_int": [list(r) for r in li],
                "snap_denominator": den,
                "float_ratio_lead": ratio_f,
                "hypothesis_ranks": ranks,
                "hypothesis_holds": max(ranks) <= 1,
                "topc_margin_relative": rel,
                "strict_certified": bool(rel is not None and rel >= args.certify_margin),
                "decision": dec,
            })

    valid = [r for r in results if r["hypothesis_holds"]
             and r["decision"]["ratio_float"] is not None]
    strict = [r for r in valid if r["strict_certified"]]
    viol_any = [r for r in valid if r["decision"]["ratio_float"] > 1]
    viol_strict = [r for r in strict if r["decision"]["ratio_float"] > 1]

    def _best(rows):
        return max((r["decision"]["ratio_float"] for r in rows), default=None)

    payload = {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": ("EXACT_RATIONAL_COUNTEREXAMPLE" if viol_strict
                           else "NO_STRICT_EXACT_COUNTEREXAMPLE_FROM_NUMERICAL_LEADS"),
        "development_only": True,
        "arm": kind,
        "hypothesis_under_test": (
            "AllCoordinatesRawLocalContrastRankOne(F) and StrictTopC "
            "=> 2D <= (m-1) delta   [D6-prime]" if kind == "raw" else
            "AllCoordinatesInteractionContrastRankOne(F) and StrictTopC "
            "=> 2D <= (m-1) delta   [D6, known FALSE: positive control]"),
        "control_expectation": (
            None if kind == "raw" else
            "This arm MUST find a strict violation. If it does not, the budget "
            "is too small and the raw arm's null result carries no weight."),
        "generated_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "m": m, "alphabet": K,
        "fiber_dim": (2 ** m if kind == "raw"
                      else 1 + m * (K - 1) + (2 ** m - 1 - m)),
        "fibers_searched": fibers_done,
        "best_float_ratio": best_float,
        "best_exact_ratio_hypothesis_valid": _best(valid),
        "best_exact_ratio_strict_certified": _best(strict),
        "n_leads": len(results),
        "n_hypothesis_valid": len(valid),
        "n_strict_certified": len(strict),
        "n_violations_any_margin": len(viol_any),
        "n_violations_strict": len(viol_strict),
        "violations_strict": viol_strict[:4],
        "limits": ("A per-fibre float search maximises a LOWER bound and is path "
                   "dependent. A null result here is evidence at this fibre sample "
                   "and budget, never a proof. It is interpretable ONLY against the "
                   "centred control run at identical settings."),
        "args": vars(args),
    }
    out = args.out or (f"research/d6_contrast_rank_falsification/"
                       f"AB_{kind}_m{m}_K{K}_seed{args.seed}.json")
    with open(out, "w") as fh:
        json.dump(payload, fh, indent=2)
    print(json.dumps({k: payload[k] for k in (
        "arm", "evidence_class", "fibers_searched", "best_float_ratio",
        "best_exact_ratio_hypothesis_valid", "best_exact_ratio_strict_certified",
        "n_hypothesis_valid", "n_strict_certified", "n_violations_strict")} |
        {"out": out}, indent=2))


if __name__ == "__main__":
    main()
