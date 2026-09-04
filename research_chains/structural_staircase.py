"""Exact finite reconstruction of the Lean Structural staircase family.

The family mirrors ``LeanStructuralStaircaseFamilyV1``:
relations are ``(i, positive)`` / ``(i, negative)`` pairs and support actions
are ``none`` plus ``some i``.  A negative relation ``t`` contributes ``-1``
on the prefix ``i <= t`` while positive relation ``i`` contributes ``+1``
only at ``some i``.

This module is theorem-discovery / exact-computation code.  It does not turn
finite checks into a proof of the parametric Lean statement.
"""
from __future__ import annotations

import math
from typing import Sequence

import numpy as np

from .kprefix import acceptable_layers, exact_cover_layers, subset_from_mask


def relation_index(i: int, negative: bool) -> int:
    """Python bit index for Lean pair ``(i, Bool)``.

    Even indices are positive ``(i,false)`` and odd indices are negative
    ``(i,true)``.
    """
    return 2 * int(i) + int(bool(negative))


def staircase_block_mask(r: int, t: int) -> int:
    r = int(r); t = int(t)
    if not (0 <= t < r):
        raise ValueError("t must be in range(r)")
    mask = 1 << relation_index(t, True)
    for i in range(t + 1):
        mask |= 1 << relation_index(i, False)
    return int(mask)


def staircase_selected_mask(r: int, t: int) -> int:
    m = 2 * int(r)
    return int(((1 << m) - 1) ^ staircase_block_mask(r, t))


def omitted_response_values(r: int, selected_mask: int) -> np.ndarray:
    """Aggregate omitted response on ``none, some 0, ..., some (r-1)``."""
    r = int(r); m = 2 * r
    if selected_mask < 0 or selected_mask >= (1 << m):
        raise ValueError("selected_mask outside staircase ground set")
    omitted = ((1 << m) - 1) ^ int(selected_mask)
    values = [0.0]  # Lean ``none`` anchor.
    for i in range(r):
        positive = 1.0 if omitted & (1 << relation_index(i, False)) else 0.0
        negative_count = sum(
            1 for t in range(i, r)
            if omitted & (1 << relation_index(t, True))
        )
        values.append(float(positive - negative_count))
    return np.asarray(values, dtype=np.float64)


def staircase_radius(r: int, selected_mask: int) -> float:
    vals = omitted_response_values(r, selected_mask)
    return 0.5 * float(np.max(vals) - np.min(vals))


def dense_staircase_objective(r: int) -> np.ndarray:
    r = int(r)
    if r <= 0:
        raise ValueError("r must be positive")
    m = 2 * r
    out = np.empty(1 << m, dtype=np.float64)
    for mask in range(1 << m):
        out[mask] = staircase_radius(r, mask)
    return out


def staircase_exact_prefix_dimension(r: int, *, verify_milp: bool = True) -> dict:
    """Compute exact chi for one finite staircase instance.

    ``exact_cover_layers`` enumerates distinct budget-coverage masks rather
    than ``m!`` rankings, and independently MILP-checks the exact set-cover
    objective when requested.
    """
    r = int(r); m = 2 * r
    values = dense_staircase_objective(r)
    layers = acceptable_layers(values, m, epsilon=0.0)
    cover = exact_cover_layers(layers, m, verify_milp=bool(verify_milp))

    forced = []
    for t in range(r):
        selected = staircase_selected_mask(r, t)
        k = int(selected.bit_count())
        forced.append({
            "t": int(t),
            "budget": k,
            "selected_mask": int(selected),
            "selected": list(subset_from_mask(selected, m)),
            "radius": float(values[selected]),
            "unique_optimum_at_budget": bool(
                (k == 0 and selected == 0) or
                (k == m and selected == (1 << m) - 1) or
                (k in layers and len(layers[k]) == 1 and int(layers[k][0]) == int(selected))
            ),
        })

    incomparable = True
    for s in range(r):
        for t in range(r):
            if s == t:
                continue
            a = staircase_selected_mask(r, s)
            b = staircase_selected_mask(r, t)
            if (a & b) == a:
                incomparable = False

    return {
        "r": r,
        "m_relations": m,
        "dimension": int(cover.dimension),
        "equals_r": bool(int(cover.dimension) == r),
        "lean_lower_bound_r": r,
        "dimension_minus_r": int(cover.dimension - r),
        "rankings": [list(map(int, x)) for x in cover.rankings],
        "chain_masks": [list(map(int, x)) for x in cover.chain_masks],
        "coverage_masks": list(map(int, cover.coverage_masks)),
        "method": cover.method,
        "milp_objective": cover.milp_objective,
        "dp_milp_agree": bool(
            cover.milp_objective is None or
            math.isclose(float(cover.milp_objective), float(cover.dimension), abs_tol=1e-8)
        ),
        "optimal_set_counts": {str(k): int(len(v)) for k, v in layers.items()},
        "forced_optima": forced,
        "all_designated_zero": bool(all(abs(x["radius"]) <= 1e-12 for x in forced)),
        "all_designated_unique": bool(all(x["unique_optimum_at_budget"] for x in forced)),
        "designated_pairwise_incomparable": bool(incomparable),
    }
