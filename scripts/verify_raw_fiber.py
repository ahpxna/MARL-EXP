#!/usr/bin/env python3
"""E1: construct and verify the RAW-rank-one fibre, exactly.

Claim under test
----------------
For a fixed action-coefficient tuple phi (phi_i(0) = 0), the set of worlds whose
RAW local contrast is rank one at every coordinate with that phi is a LINEAR
SUBSPACE V^raw_phi, spanned by

    constant                                 1 column
    phi_i(a_i)                               m columns
    prod_{i in S} phi_i(a_i),  |S| >= 2      2^m - 1 - m columns

so  dim V^raw = 1 + m + (2^m - 1 - m) = 2^m,

against the centred fibre  dim V_lambda = 1 + m(K-1) + (2^m - 1 - m).
The difference is m(K-2): the centred fibre carries K-1 free additive degrees
of freedom per coordinate, the raw fibre carries exactly 1 (the scale of an
additive part that must be affine in phi_i).

Everything below is exact rational arithmetic.  Three things are checked, not
assumed:
  (a) the stated dimension, by exact rank of the spanning set;
  (b) that every element of the span really is raw rank one at every coordinate
      (checked on the basis AND on random integer combinations, because rank one
      is not preserved by addition in general -- it is preserved here only
      because every basis column shares the same theta_i = phi_i);
  (c) that the directions the raw fibre drops really do break raw rank one, so
      the codimension is not an artifact of a redundant spanning set.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import itertools
import json
import os
import random
import sys
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from annotate_misalignment import exact_rank, raw_contrast_matrix  # noqa: E402

PROTOCOL_VERSION = "d6_raw_fiber_verification_v1"


def centred_fiber_dim(m: int, K: int) -> int:
    return 1 + m * (K - 1) + (2 ** m - 1 - m)


def raw_fiber_dim(m: int, K: int) -> int:
    return 1 + m + (2 ** m - 1 - m)


def build_columns(m: int, K: int, phi: List[List[Fraction]], kind: str):
    """Columns of the fibre basis, indexed by the action list `acts`."""
    acts = list(itertools.product(range(K), repeat=m))
    cols: List[Tuple[str, List[Fraction]]] = [("const", [Fraction(1)] * len(acts))]
    if kind == "raw":
        for i in range(m):
            cols.append((f"phi[{i}]", [phi[i][a[i]] for a in acts]))
    else:
        for i in range(m):
            for u in range(1, K):
                cols.append((f"ind[{i}={u}]",
                             [Fraction(1) if a[i] == u else Fraction(0) for a in acts]))
    for size in range(2, m + 1):
        for S in itertools.combinations(range(m), size):
            col = []
            for a in acts:
                v = Fraction(1)
                for i in S:
                    v *= phi[i][a[i]]
                col.append(v)
            cols.append((f"prod{S}", col))
    return acts, cols


def world_from(acts, vec: Sequence[Fraction]) -> Dict[Tuple[int, ...], Fraction]:
    return {a: v for a, v in zip(acts, vec)}


def raw_ranks(world, m: int, K: int) -> List[int]:
    return [exact_rank(raw_contrast_matrix(world, m, K, i)) for i in range(m)]


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--alphabet", type=int, default=3)
    ap.add_argument("--random-combos", type=int, default=12)
    ap.add_argument("--seed", type=int, default=20260905)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    m, K = args.m, args.alphabet
    rng = random.Random(args.seed)

    # a generic phi: phi_i(0) = 0, remaining values distinct and nonzero
    phi = [[Fraction(0)] + [Fraction(1 + i + 3 * u) for u in range(1, K)]
           for i in range(m)]

    report = {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": "EXACT_RATIONAL_VERIFICATION",
        "development_only": True,
        "generated_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "m": m, "alphabet": K,
        "phi": [[str(v) for v in row] for row in phi],
        "predicted_centred_fiber_dim": centred_fiber_dim(m, K),
        "predicted_raw_fiber_dim": raw_fiber_dim(m, K),
        "predicted_codimension": centred_fiber_dim(m, K) - raw_fiber_dim(m, K),
    }

    results = {}
    for kind in ("centred", "raw"):
        acts, cols = build_columns(m, K, phi, kind)
        rows = [c for _, c in cols]              # each column is a vector over acts
        dim = exact_rank(rows)                   # rank of the spanning set
        # (b) every basis element is raw rank one?
        basis_ok = all(max(raw_ranks(world_from(acts, c), m, K)) <= 1 for _, c in cols)
        # random integer combinations
        combo_ranks = []
        for _ in range(args.random_combos):
            coeff = [Fraction(rng.randint(-5, 5)) for _ in cols]
            vec = [sum((coeff[j] * cols[j][1][t] for j in range(len(cols))), Fraction(0))
                   for t in range(len(acts))]
            combo_ranks.append(max(raw_ranks(world_from(acts, vec), m, K)))
        results[kind] = {
            "spanning_set_size": len(cols),
            "exact_dimension": dim,
            "every_basis_column_raw_rank_one": basis_ok,
            "max_raw_rank_over_random_combinations": max(combo_ranks) if combo_ranks else None,
            "random_combinations_tested": len(combo_ranks),
            "all_random_combinations_raw_rank_one":
                all(r <= 1 for r in combo_ranks),
        }

    # (c) the dropped directions must genuinely break raw rank one
    acts, raw_cols = build_columns(m, K, phi, "raw")
    dropped = []
    for i in range(m):
        for u in range(1, K):
            ind = [Fraction(1) if a[i] == u else Fraction(0) for a in acts]
            ranks = raw_ranks(world_from(acts, ind), m, K)
            dropped.append({
                "direction": f"indicator[{i}={u}]",
                "raw_ranks": ranks,
                "breaks_raw_rank_one": max(ranks) > 1,
                "is_proportional_to_phi_column":
                    max(ranks) <= 1,
            })
    report["fibres"] = results
    report["dropped_direction_probe"] = {
        "note": ("An indicator direction is inside the raw fibre exactly when it is "
                 "already affine in phi_i, which at K=2 is every direction and at "
                 "K>=3 is a proper subset.  The count of directions that BREAK raw "
                 "rank one is the honest codimension."),
        "n_breaking": sum(1 for d in dropped if d["breaks_raw_rank_one"]),
        "detail": dropped,
    }
    report["verdict"] = {
        "raw_dim_matches_prediction":
            results["raw"]["exact_dimension"] == raw_fiber_dim(m, K),
        "centred_dim_matches_prediction":
            results["centred"]["exact_dimension"] == centred_fiber_dim(m, K),
        "raw_fibre_is_closed_under_addition":
            results["raw"]["all_random_combinations_raw_rank_one"],
        "observed_codimension":
            results["centred"]["exact_dimension"] - results["raw"]["exact_dimension"],
    }

    out = args.out or (f"research/d6_contrast_rank_falsification/"
                       f"E1_rawfiber_m{m}_K{K}.json")
    with open(out, "w") as fh:
        json.dump(report, fh, indent=2)
    print(json.dumps({"out": out, **report["verdict"],
                      "raw_dim": results["raw"]["exact_dimension"],
                      "centred_dim": results["centred"]["exact_dimension"]}, indent=2))


if __name__ == "__main__":
    main()
