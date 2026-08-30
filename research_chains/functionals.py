"""Functional-specific estimability and experimental-design primitives."""

from __future__ import annotations

from typing import Sequence

import numpy as np
from scipy.stats import norm

from .certificates import oscillation


def capacity(q: Sequence[float]) -> float:
    return oscillation(q)


def direction(q: Sequence[float], weights: Sequence[float]) -> float:
    q = np.asarray(q, dtype=np.float64); w = np.asarray(weights, dtype=np.float64)
    if q.shape != w.shape or q.ndim != 1 or not np.all(np.isfinite(q)) or not np.all(np.isfinite(w)):
        raise ValueError("q and weights must be same-length finite vectors")
    return float(np.dot(w, q))


def capacity_error_bound(qhat: Sequence[float], q: Sequence[float]) -> float:
    err = float(np.max(np.abs(np.asarray(qhat, dtype=float) - np.asarray(q, dtype=float))))
    return 2.0 * err


def direction_error_bound(qhat: Sequence[float], q: Sequence[float], weights: Sequence[float]) -> float:
    qhat = np.asarray(qhat, dtype=float); q = np.asarray(q, dtype=float); w = np.asarray(weights, dtype=float)
    err = float(np.max(np.abs(qhat - q)))
    return float(np.sum(np.abs(w)) * err)


def extrema_gaps(q: Sequence[float]):
    q = np.asarray(q, dtype=np.float64)
    if q.ndim != 1 or q.size < 2 or not np.all(np.isfinite(q)):
        raise ValueError("q must contain at least two finite actions")
    order_desc = np.argsort(-q, kind="stable"); order_asc = np.argsort(q, kind="stable")
    a_plus, next_plus = int(order_desc[0]), int(order_desc[1])
    a_minus, next_minus = int(order_asc[0]), int(order_asc[1])
    g_plus = float(q[a_plus] - q[next_plus])
    g_minus = float(q[next_minus] - q[a_minus])
    return {"argmax": a_plus, "argmin": a_minus, "g_plus": g_plus, "g_minus": g_minus, "g": min(g_plus, g_minus)}


def extrema_stable(qhat: Sequence[float], q: Sequence[float]) -> bool:
    qhat = np.asarray(qhat, dtype=np.float64); q = np.asarray(q, dtype=np.float64)
    gaps = extrema_gaps(q)
    if gaps["g"] <= 0.0:
        return False
    return float(np.max(np.abs(qhat - q))) < gaps["g"] / 2.0


def functional_boundary_diagnostics(
    qhat: Sequence[float],
    q: Sequence[float],
    action_ids: Sequence[int] | None = None,
    *,
    atol: float = 1e-12,
):
    """Gauge-invariant extrema-stability diagnostics for C=max Q-min Q.

    ``qhat`` and ``q`` must describe the same valid action coordinates.  A
    constant shift of the learned response surface is irrelevant to both
    capacity and extrema identities, so the phase error is measured in the
    quotient by constants:

        delta_Q^circ = inf_c ||qhat-q-c||_inf
                      = 0.5 * osc(qhat-q).

    If the oracle maximum and minimum are unique and
    ``delta_Q^circ < g/2``, where ``g`` is the smaller oracle extrema gap,
    both extrema identities are certified stable.
    """
    qhat = np.asarray(qhat, dtype=np.float64)
    q = np.asarray(q, dtype=np.float64)
    if qhat.shape != q.shape or q.ndim != 1 or q.size < 2:
        raise ValueError("qhat and q must be same-length vectors with at least two actions")
    if not np.all(np.isfinite(qhat)) or not np.all(np.isfinite(q)):
        raise ValueError("qhat and q must be finite")

    if action_ids is None:
        ids = np.arange(q.size, dtype=np.int64)
    else:
        ids = np.asarray(action_ids, dtype=np.int64)
        if ids.shape != q.shape:
            raise ValueError("action_ids must align with qhat/q")

    diff = qhat - q
    diff_min = float(np.min(diff))
    diff_max = float(np.max(diff))
    gauge_shift = 0.5 * (diff_max + diff_min)
    delta_circ = 0.5 * (diff_max - diff_min)
    raw_sup = float(np.max(np.abs(diff)))
    aligned_sup = float(np.max(np.abs(diff - gauge_shift)))

    oracle_max = float(np.max(q))
    oracle_min = float(np.min(q))
    max_mask = np.isclose(q, oracle_max, atol=float(atol), rtol=0.0)
    min_mask = np.isclose(q, oracle_min, atol=float(atol), rtol=0.0)
    max_idx = np.flatnonzero(max_mask)
    min_idx = np.flatnonzero(min_mask)
    max_count = int(max_idx.size)
    min_count = int(min_idx.size)

    oracle_argmax_local = int(np.argmax(q))
    oracle_argmin_local = int(np.argmin(q))
    learned_argmax_local = int(np.argmax(qhat))
    learned_argmin_local = int(np.argmin(qhat))

    if max_count == 1:
        remaining = np.delete(q, oracle_argmax_local)
        g_plus = float(oracle_max - np.max(remaining))
    else:
        g_plus = 0.0
    if min_count == 1:
        remaining = np.delete(q, oracle_argmin_local)
        g_minus = float(np.min(remaining) - oracle_min)
    else:
        g_minus = 0.0
    g = float(min(g_plus, g_minus))

    argmax_match = bool(max_mask[learned_argmax_local])
    argmin_match = bool(min_mask[learned_argmin_local])
    both_match = bool(argmax_match and argmin_match)
    unique = bool(max_count == 1 and min_count == 1)
    gap_zero = bool(g <= float(atol))
    lambda_c = float(delta_circ / g) if not gap_zero else float("inf")
    raw_lambda_c = float(raw_sup / g) if not gap_zero else float("inf")
    certified = bool(unique and delta_circ < g / 2.0)
    violation = bool(certified and not both_match)

    return {
        "oracle_argmax_action": int(ids[oracle_argmax_local]),
        "oracle_argmin_action": int(ids[oracle_argmin_local]),
        "learned_argmax_action": int(ids[learned_argmax_local]),
        "learned_argmin_action": int(ids[learned_argmin_local]),
        "oracle_argmax_count": max_count,
        "oracle_argmin_count": min_count,
        "oracle_extrema_unique": int(unique),
        "argmax_match": int(argmax_match),
        "argmin_match": int(argmin_match),
        "both_extrema_match": int(both_match),
        "oracle_g_plus": g_plus,
        "oracle_g_minus": g_minus,
        "oracle_extrema_gap": g,
        "extrema_gap_zero": int(gap_zero),
        "q_raw_sup_error": raw_sup,
        "q_gauge_shift_opt": gauge_shift,
        "q_gauge_sup_error": delta_circ,
        "q_gauge_sup_error_check": aligned_sup,
        "lambda_C": lambda_c,
        "lambda_C_raw": raw_lambda_c,
        "extrema_stability_certified": int(certified),
        "extrema_stability_violation": int(violation),
    }



def direction_sign_boundary_diagnostics(
    qhat: Sequence[float],
    q: Sequence[float],
    weights: Sequence[float],
    *,
    atol: float = 1e-12,
):
    """Gauge-invariant sign certificate for a zero-sum linear direction."""
    qhat = np.asarray(qhat, dtype=np.float64)
    q = np.asarray(q, dtype=np.float64)
    w = np.asarray(weights, dtype=np.float64)
    if qhat.shape != q.shape or q.shape != w.shape or q.ndim != 1:
        raise ValueError("qhat, q, and weights must align")
    if not np.all(np.isfinite(qhat)) or not np.all(np.isfinite(q)) or not np.all(np.isfinite(w)):
        raise ValueError("qhat, q, and weights must be finite")
    if abs(float(np.sum(w))) > 1e-8:
        raise ValueError("direction sign certificate requires zero-sum contrast weights")

    diff = qhat - q
    delta_circ = 0.5 * float(np.max(diff) - np.min(diff))
    learned_d = float(np.dot(w, qhat))
    oracle_d = float(np.dot(w, q))
    l1 = float(np.sum(np.abs(w)))
    error_bound = float(l1 * delta_circ)
    margin = float(abs(oracle_d))
    lambda_d = float(error_bound / margin) if margin > float(atol) else float("inf")
    sign_match = bool(
        margin > float(atol)
        and np.sign(learned_d) == np.sign(oracle_d)
    )
    certified = bool(margin > float(atol) and error_bound < margin)
    return {
        "learned_direction_from_q": learned_d,
        "oracle_direction_from_q": oracle_d,
        "direction_weight_l1": l1,
        "direction_q_error_bound": error_bound,
        "direction_sign_margin": margin,
        "lambda_D": lambda_d,
        "direction_sign_match_from_q": int(sign_match),
        "direction_sign_certified": int(certified),
        "direction_sign_violation": int(certified and not sign_match),
    }


def relation_ranking_diagnostics(
    relation_ids: Sequence[int],
    learned_capacity: Sequence[float],
    oracle_capacity: Sequence[float],
    q_gauge_errors: Sequence[float],
    *,
    top_k: int = 1,
    atol: float = 1e-12,
):
    """Two-level C diagnostics: local Q error -> between-relation rank stability.

    The deterministic Q-derived capacity error bound is ``2*delta_Q^circ``.
    Ranking certificates compare oracle between-relation margins against sums of
    those per-relation bounds.  Stable tie-breaking by relation id is used only
    to make diagnostic TopK sets reproducible; a zero oracle boundary margin is
    explicitly marked non-unique and never certified.
    """
    ids = np.asarray(relation_ids, dtype=np.int64)
    learned = np.asarray(learned_capacity, dtype=np.float64)
    oracle = np.asarray(oracle_capacity, dtype=np.float64)
    delta = np.asarray(q_gauge_errors, dtype=np.float64)
    if ids.ndim != 1 or learned.shape != ids.shape or oracle.shape != ids.shape or delta.shape != ids.shape:
        raise ValueError("relation ids, capacities, and q errors must align")
    if ids.size < 2 or len(set(ids.tolist())) != ids.size:
        raise ValueError("relation ids must contain at least two unique entries")
    if not np.all(np.isfinite(learned)) or not np.all(np.isfinite(oracle)) or not np.all(np.isfinite(delta)):
        raise ValueError("ranking diagnostics require finite capacities and q errors")
    if np.any(delta < -float(atol)):
        raise ValueError("q gauge errors must be non-negative")
    k = int(top_k)
    if k <= 0 or k >= ids.size:
        raise ValueError("top_k must be in [1, n_relations-1]")

    oracle_order = np.asarray(sorted(
        range(ids.size), key=lambda i: (-float(oracle[i]), int(ids[i]))
    ), dtype=np.int64)
    learned_order = np.asarray(sorted(
        range(ids.size), key=lambda i: (-float(learned[i]), int(ids[i]))
    ), dtype=np.int64)
    oracle_rank = np.empty(ids.size, dtype=np.int64)
    learned_rank = np.empty(ids.size, dtype=np.int64)
    for rank, idx in enumerate(oracle_order):
        oracle_rank[idx] = rank + 1
    for rank, idx in enumerate(learned_order):
        learned_rank[idx] = rank + 1

    true_top = set(int(i) for i in oracle_order[:k])
    learned_top = set(int(i) for i in learned_order[:k])
    q_bound = 2.0 * delta
    actual_error = np.abs(learned - oracle)
    q_bound_violation = actual_error > q_bound + max(float(atol), 1e-8)

    boundary_gap = float(oracle[oracle_order[k - 1]] - oracle[oracle_order[k]])
    boundary_unique = bool(boundary_gap > float(atol))
    topk_match = bool(true_top == learned_top)

    cross_ratios_q = []
    cross_ratios_actual = []
    cross_margins = []
    for i in true_top:
        for j in range(ids.size):
            if j in true_top:
                continue
            margin = float(oracle[i] - oracle[j])
            cross_margins.append(margin)
            if margin <= float(atol):
                cross_ratios_q.append(float("inf"))
                cross_ratios_actual.append(float("inf"))
            else:
                cross_ratios_q.append(float((q_bound[i] + q_bound[j]) / margin))
                cross_ratios_actual.append(float((actual_error[i] + actual_error[j]) / margin))
    lambda_topk_q = float(max(cross_ratios_q)) if cross_ratios_q else float("nan")
    lambda_topk_actual = float(max(cross_ratios_actual)) if cross_ratios_actual else float("nan")
    topk_q_certified = bool(boundary_unique and lambda_topk_q < 1.0)
    topk_actual_certified = bool(boundary_unique and lambda_topk_actual < 1.0)

    pair_total = 0
    pair_correct = 0
    pair_q_certified = 0
    pair_q_violations = 0
    pair_actual_certified = 0
    pair_actual_violations = 0
    strict_pair_margins = []
    full_q_ratios = []
    for i in range(ids.size):
        for j in range(i + 1, ids.size):
            margin = float(abs(oracle[i] - oracle[j]))
            if margin <= float(atol):
                continue
            pair_total += 1
            strict_pair_margins.append(margin)
            oracle_sign = np.sign(oracle[i] - oracle[j])
            learned_sign = np.sign(learned[i] - learned[j])
            correct = bool(oracle_sign == learned_sign)
            pair_correct += int(correct)
            ratio_q = float((q_bound[i] + q_bound[j]) / margin)
            full_q_ratios.append(ratio_q)
            if ratio_q < 1.0:
                pair_q_certified += 1
                pair_q_violations += int(not correct)
            ratio_actual = float((actual_error[i] + actual_error[j]) / margin)
            if ratio_actual < 1.0:
                pair_actual_certified += 1
                pair_actual_violations += int(not correct)

    adjacent_gaps = [
        float(oracle[oracle_order[r]] - oracle[oracle_order[r + 1]])
        for r in range(ids.size - 1)
    ]
    full_rank_min_gap = float(min(adjacent_gaps)) if adjacent_gaps else float("nan")
    full_rank_unique = bool(full_rank_min_gap > float(atol))
    lambda_full_rank_q = (
        float(max(full_q_ratios)) if full_q_ratios and full_rank_unique else float("inf")
    )

    learned_l = learned - q_bound
    learned_u = learned + q_bound
    learned_selected = list(learned_top)
    learned_rejected = [i for i in range(ids.size) if i not in learned_top]
    interval_separation = float(
        min(learned_l[i] for i in learned_selected)
        - max(learned_u[j] for j in learned_rejected)
    )
    interval_certified = bool(interval_separation > float(atol))

    per_relation = {}
    true_boundary_low = float(oracle[oracle_order[k - 1]])
    true_boundary_high_rejected = float(oracle[oracle_order[k]])
    for i, rid in enumerate(ids):
        if i in true_top:
            margin_to_boundary = float(oracle[i] - true_boundary_high_rejected)
        else:
            margin_to_boundary = float(true_boundary_low - oracle[i])
        per_relation[int(rid)] = {
            "oracle_capacity_rank": int(oracle_rank[i]),
            "learned_capacity_rank": int(learned_rank[i]),
            "oracle_capacity_topk_member": int(i in true_top),
            "learned_capacity_topk_member": int(i in learned_top),
            "capacity_q_error_bound": float(q_bound[i]),
            "capacity_q_error_bound_violation": int(q_bound_violation[i]),
            "oracle_capacity_margin_to_topk_boundary": margin_to_boundary,
        }

    return {
        "top_k": k,
        "oracle_topk_ids": [int(ids[i]) for i in oracle_order[:k]],
        "learned_topk_ids": [int(ids[i]) for i in learned_order[:k]],
        "oracle_topk_gap": boundary_gap,
        "oracle_topk_unique": int(boundary_unique),
        "capacity_topk_match": int(topk_match),
        "lambda_topk_Q": lambda_topk_q,
        "lambda_topk_actual_error": lambda_topk_actual,
        "capacity_topk_q_certified": int(topk_q_certified),
        "capacity_topk_q_certified_violation": int(topk_q_certified and not topk_match),
        "capacity_topk_actual_error_certified": int(topk_actual_certified),
        "capacity_topk_actual_error_certified_violation": int(topk_actual_certified and not topk_match),
        "capacity_topk_interval_separation": interval_separation,
        "capacity_topk_interval_certified": int(interval_certified),
        "capacity_topk_interval_certified_violation": int(interval_certified and not topk_match),
        "oracle_full_rank_min_gap": full_rank_min_gap,
        "oracle_full_rank_unique": int(full_rank_unique),
        "lambda_full_rank_Q": lambda_full_rank_q,
        "strict_relation_pair_count": int(pair_total),
        "strict_relation_pair_order_accuracy": float(pair_correct / pair_total) if pair_total else float("nan"),
        "q_certified_relation_pair_count": int(pair_q_certified),
        "q_certified_relation_pair_violation_count": int(pair_q_violations),
        "actual_error_certified_relation_pair_count": int(pair_actual_certified),
        "actual_error_certified_relation_pair_violation_count": int(pair_actual_violations),
        "capacity_q_error_bound_violation_count": int(np.count_nonzero(q_bound_violation)),
        "per_relation": per_relation,
    }


def split_capacity(selection_q: Sequence[float], evaluation_q: Sequence[float]) -> float:
    selection_q = np.asarray(selection_q, dtype=np.float64); evaluation_q = np.asarray(evaluation_q, dtype=np.float64)
    if selection_q.shape != evaluation_q.shape:
        raise ValueError("selection/evaluation vectors must align")
    return float(evaluation_q[int(np.argmax(selection_q))] - evaluation_q[int(np.argmin(selection_q))])


def simultaneous_capacity_interval(estimates: Sequence[float], standard_errors: Sequence[float], alpha: float = 0.05):
    """Bonferroni simultaneous coordinate intervals -> valid C bracket baseline."""
    q = np.asarray(estimates, dtype=np.float64); se = np.asarray(standard_errors, dtype=np.float64)
    if q.shape != se.shape or q.ndim != 1 or np.any(se < 0.0):
        raise ValueError("estimates/se must align and se must be non-negative")
    z = float(norm.ppf(1.0 - float(alpha) / (2.0 * q.size)))
    lower, upper = q - z * se, q + z * se
    lower_c = 0.0
    upper_c = 0.0
    for a in range(q.size):
        for b in range(q.size):
            lower_c = max(lower_c, float(lower[a] - upper[b]))
            upper_c = max(upper_c, float(upper[a] - lower[b]))
    return max(0.0, lower_c), max(0.0, upper_c), lower, upper


def neyman_allocation(weights: Sequence[float], sigmas: Sequence[float], budget: float, floor: float = 0.0) -> np.ndarray:
    """Continuous |w|sigma allocation with a positivity/sample floor."""
    w = np.abs(np.asarray(weights, dtype=np.float64)); sigma = np.asarray(sigmas, dtype=np.float64)
    if w.shape != sigma.shape or w.ndim != 1 or np.any(sigma < 0.0) or not np.all(np.isfinite(w + sigma)):
        raise ValueError("weights/sigmas must be same-length finite vectors")
    n = w.size; budget = float(budget); floor = float(floor)
    if floor < 0.0 or budget < n * floor - 1e-12:
        raise ValueError("budget is incompatible with requested floor")
    score = w * sigma
    allocation = np.full(n, floor, dtype=np.float64)
    remaining_budget = budget - n * floor
    active = set(range(n))
    # Water-fill the incremental allocation while respecting that the total
    # n_a, not just the increment, should be proportional to |w|sigma.
    fixed = set()
    while active:
        free_budget = budget - floor * len(fixed)
        total_score = float(sum(score[j] for j in active))
        if total_score <= 0.0:
            share = free_budget / len(active)
            for j in active:
                allocation[j] = share
            break
        proposal = {j: free_budget * score[j] / total_score for j in active}
        newly_fixed = {j for j, value in proposal.items() if value < floor - 1e-12}
        if not newly_fixed:
            for j, value in proposal.items():
                allocation[j] = value
            break
        for j in newly_fixed:
            allocation[j] = floor
        fixed |= newly_fixed; active -= newly_fixed
    # Numeric reconciliation.
    if allocation.sum() > 0:
        diff = budget - float(allocation.sum())
        allocation[int(np.argmax(allocation))] += diff
    if np.any(allocation < floor - 1e-9) or not np.isclose(allocation.sum(), budget, atol=1e-8):
        raise RuntimeError("floor-constrained allocation failed")
    return allocation


def linear_contrast_variance(weights: Sequence[float], sigmas: Sequence[float], allocation: Sequence[float]) -> float:
    w = np.asarray(weights, dtype=np.float64); s = np.asarray(sigmas, dtype=np.float64); n = np.asarray(allocation, dtype=np.float64)
    if w.shape != s.shape or w.shape != n.shape or np.any(n <= 0.0):
        raise ValueError("weights/sigmas/allocation must align and allocation be positive")
    return float(np.sum((w * s) ** 2 / n))
