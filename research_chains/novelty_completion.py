"""Executable objects for the post-P13 novelty proposals.

This module deliberately separates *deterministic certificate mechanics* from
statistical or empirical claims.  The corresponding Lean files prove the
formal safety statements; these helpers are for reproducible experiments that
measure cost, query count, refresh count, or witness frequency.
"""
from __future__ import annotations

from dataclasses import dataclass
import itertools
import math
from typing import Iterable, Mapping, Sequence

import numpy as np

from .certificates import exact_optimum, topk_indices
from .finite_world import FiniteResponseWorld
from .support import SupportModel


# ---------------------------------------------------------------------------
# Typed heterogeneous certificate completion

@dataclass(frozen=True)
class EvidenceItem:
    key: str
    evidence_type: str
    cost: float
    discharges: frozenset[str]

    def __post_init__(self) -> None:
        if not str(self.key):
            raise ValueError("evidence key must be non-empty")
        if not str(self.evidence_type):
            raise ValueError("evidence type must be non-empty")
        if not math.isfinite(float(self.cost)) or float(self.cost) < 0.0:
            raise ValueError("evidence cost must be finite and non-negative")


def minimum_cost_typed_completion(
    obligations: Mapping[str, str], evidence: Sequence[EvidenceItem]
) -> dict:
    """Exact finite minimum-cost completion with a typed discharge contract.

    ``obligations`` maps obligation id -> required evidence type.  An item may
    discharge an obligation only when its own type matches the obligation type.
    The exhaustive solver is intentionally for small development experiments;
    it is a scientific oracle/baseline, not a claim of scalable optimization.
    """
    obligations = {str(k): str(v) for k, v in obligations.items()}
    items = tuple(evidence)
    for item in items:
        unknown = set(item.discharges) - set(obligations)
        if unknown:
            raise ValueError(f"evidence {item.key} discharges unknown obligations: {sorted(unknown)}")
        bad = [o for o in item.discharges if obligations[o] != item.evidence_type]
        if bad:
            raise ValueError(
                f"typed discharge violation for {item.key}: {bad} require "
                f"{[obligations[o] for o in bad]} but item has {item.evidence_type}"
            )
    target = set(obligations)
    # Exact weighted set-cover DP over obligation masks.  The earlier naive
    # 2^|evidence| enumeration becomes unusable as soon as cheap decoys/bundles
    # are added; the scientific state space is the obligation set, which is the
    # intended small exact development regime.
    order = tuple(sorted(target))
    bit = {o: 1 << i for i, o in enumerate(order)}
    full_mask = (1 << len(order)) - 1
    cover_masks = []
    for item in items:
        mask = 0
        for o in item.discharges:
            mask |= bit[o]
        cover_masks.append(mask)
    # value = (cost, count, tuple(item_indices)); tie-break deterministically by keys
    dp = {0: (0.0, 0, ())}
    for i, (item, cmask) in enumerate(zip(items, cover_masks)):
        if cmask == 0:
            continue
        snapshot = list(dp.items())
        for state, (cost0, count0, ids0) in snapshot:
            nxt = state | cmask
            cand = (cost0 + float(item.cost), count0 + 1, ids0 + (i,))
            prev = dp.get(nxt)
            if prev is None:
                dp[nxt] = cand
            else:
                cand_key = (cand[0], cand[1], tuple(items[j].key for j in cand[2]))
                prev_key = (prev[0], prev[1], tuple(items[j].key for j in prev[2]))
                if cand_key < prev_key:
                    dp[nxt] = cand
    if full_mask not in dp:
        covered_mask = max(dp, key=lambda m: (m.bit_count(), -dp[m][0]))
        uncovered = [o for o in order if not (covered_mask & bit[o])]
        return {"complete": False, "cost": None, "selected": [], "uncovered": uncovered}
    cost0, _, ids = dp[full_mask]
    chosen = [items[i] for i in ids]
    return {
        "complete": True,
        "cost": float(cost0),
        "selected": [x.key for x in chosen],
        "selected_types": [x.evidence_type for x in chosen],
        "uncovered": [],
    }


# ---------------------------------------------------------------------------
# Functional selective certificate maintenance

def selective_refresh_solution(
    lower: Sequence[float],
    upper: Sequence[float],
    drift: Sequence[float],
    refresh_cost: Sequence[float],
    k: int,
) -> dict:
    """Minimum-cost idealized refresh set preserving the current Top-k.

    The current score interval is ``[lower, upper]``.  An unrefreshed relation
    may drift by ``drift[j]`` on either side.  In this first executable model a
    refresh removes the *future drift allowance* but leaves the current score
    interval intact, matching the LIFE-B idealized deterministic contract.
    """
    lower = np.asarray(lower, float)
    upper = np.asarray(upper, float)
    drift = np.asarray(drift, float)
    cost = np.asarray(refresh_cost, float)
    if not (lower.ndim == upper.ndim == drift.ndim == cost.ndim == 1):
        raise ValueError("selective maintenance inputs must be vectors")
    if not (lower.shape == upper.shape == drift.shape == cost.shape):
        raise ValueError("selective maintenance vectors must align")
    if np.any(lower > upper) or np.any(drift < 0) or np.any(cost < 0):
        raise ValueError("invalid intervals, drift, or costs")
    midpoint = 0.5 * (lower + upper)
    chosen = tuple(topk_indices(midpoint, int(k)))
    rejected = tuple(j for j in range(len(midpoint)) if j not in set(chosen))

    def safe(mask: int) -> bool:
        residual = np.asarray([0.0 if mask & (1 << j) else drift[j] for j in range(len(drift))])
        if not rejected:
            return True
        return all(
            float(lower[j] - upper[l]) > float(residual[j] + residual[l])
            for j in chosen for l in rejected
        )

    feasible = []
    for mask in range(1 << len(midpoint)):
        if safe(mask):
            selected = tuple(j for j in range(len(midpoint)) if mask & (1 << j))
            total = float(sum(cost[j] for j in selected))
            feasible.append((total, len(selected), selected))
    if not feasible:
        return {
            "safe": False,
            "chosen": list(chosen),
            "refresh": None,
            "refresh_cost": None,
            "full_refresh_cost": float(np.sum(cost)),
        }
    total, _, selected = min(feasible)
    return {
        "safe": True,
        "chosen": list(chosen),
        "refresh": list(selected),
        "refresh_cost": float(total),
        "full_refresh_cost": float(np.sum(cost)),
        "refresh_fraction": float(len(selected) / max(1, len(midpoint))),
        "cost_fraction": float(total / np.sum(cost)) if float(np.sum(cost)) > 0 else 0.0,
    }


# ---------------------------------------------------------------------------
# Decision-critical support identification

def support_certificate_state(
    world: FiniteResponseWorld,
    lower: SupportModel,
    upper: SupportModel,
    k: int,
) -> dict:
    if not lower.is_subset_of(upper):
        raise ValueError("lower support must be a subset of upper support")
    upper_opt, upper_sets = exact_optimum(world, int(k), support=upper)
    candidate = tuple(upper_sets[0])
    candidate_upper = float(world.additive_radius(candidate, support=upper))
    lower_opt, _ = exact_optimum(world, int(k), support=lower)
    bound = max(0.0, candidate_upper - float(lower_opt))
    return {
        "candidate": list(candidate),
        "candidate_upper_loss": candidate_upper,
        "lower_optimum": float(lower_opt),
        "upper_optimum": float(upper_opt),
        "regret_bound": float(bound),
    }


def _support_from_cells(action_sizes, cells, key):
    return SupportModel(tuple(action_sizes), tuple(sorted(set(tuple(x) for x in cells))), key=key)


def support_query_update(lower: SupportModel, upper: SupportModel, cell, feasible: bool):
    cell = tuple(int(x) for x in cell)
    if cell not in set(upper.omega) or cell in set(lower.omega):
        raise ValueError("cell must be unresolved (in upper but not lower)")
    lo = set(lower.omega)
    hi = set(upper.omega)
    if feasible:
        lo.add(cell)
    else:
        hi.remove(cell)
        if not hi:
            raise ValueError("query update would make upper support empty")
    return (
        _support_from_cells(lower.action_sizes, lo, lower.key + "+"),
        _support_from_cells(upper.action_sizes, hi, upper.key + "-"),
    )


def choose_minimax_support_query(world, lower, upper, k):
    """One-step decision-focused query using no hidden truth information."""
    unresolved = [a for a in upper.omega if a not in set(lower.omega)]
    rows = []
    for cell in unresolved:
        branch_bounds = []
        # feasible branch
        lo_p, hi_p = support_query_update(lower, upper, cell, True)
        branch_bounds.append(support_certificate_state(world, lo_p, hi_p, k)["regret_bound"])
        # infeasible branch is legal unless it would empty upper; lower is nonempty
        lo_n, hi_n = support_query_update(lower, upper, cell, False)
        branch_bounds.append(support_certificate_state(world, lo_n, hi_n, k)["regret_bound"])
        rows.append((max(branch_bounds), float(np.mean(branch_bounds)), tuple(cell), branch_bounds))
    if not rows:
        return None
    rows.sort(key=lambda x: (x[0], x[1], x[2]))
    best = rows[0]
    return {"cell": list(best[2]), "worst_next_bound": best[0], "mean_next_bound": best[1], "branch_bounds": best[3]}


def epsilon_optimal_decisions(world: FiniteResponseWorld, support: SupportModel, k: int, epsilon: float = 0.0):
    m = world.support.n_relations
    vals = []
    for S in itertools.combinations(range(m), int(k)):
        vals.append((tuple(S), float(world.additive_radius(S, support=support))))
    best = min(v for _, v in vals)
    return {S for S, v in vals if v <= best + float(epsilon) + 1e-12}


def critical_support_cells(world: FiniteResponseWorld, truth: SupportModel, k: int, epsilon: float = 0.0):
    """Exact one-cell witness set around a declared true support."""
    full = set(truth.full_product())
    base = set(truth.omega)
    good_base = epsilon_optimal_decisions(world, truth, k, epsilon)
    critical = []
    for cell in sorted(full):
        toggled = set(base)
        if cell in toggled:
            if len(toggled) == 1:
                continue
            toggled.remove(cell)
        else:
            toggled.add(cell)
        alt = _support_from_cells(truth.action_sizes, toggled, "toggle")
        good_alt = epsilon_optimal_decisions(world, alt, k, epsilon)
        if good_base.isdisjoint(good_alt):
            critical.append(list(cell))
    return critical


# ---------------------------------------------------------------------------
# Structural budget-transversal prefix-cover dimension

def epsilon_optimal_sets_by_budget(world: FiniteResponseWorld, epsilon: float = 0.0):
    m = world.support.n_relations
    out = {}
    for k in range(1, m):
        vals = [(tuple(S), float(world.additive_radius(S))) for S in itertools.combinations(range(m), k)]
        best = min(v for _, v in vals)
        out[k] = {S for S, v in vals if v <= best + float(epsilon) + 1e-12}
    return out


def prefix_cover_dimension(world: FiniteResponseWorld, epsilon: float = 0.0) -> dict:
    """Exact small-m prefix-cover dimension via coverage-mask DP."""
    m = world.support.n_relations
    opt = epsilon_optimal_sets_by_budget(world, epsilon)
    budgets = tuple(sorted(opt))
    if not budgets:
        return {"dimension": 1, "rankings": [list(range(m))], "budgets": []}
    bindex = {k: i for i, k in enumerate(budgets)}
    all_mask = (1 << len(budgets)) - 1
    best_ranking_for_mask = {}
    for perm in itertools.permutations(range(m)):
        mask = 0
        for k in budgets:
            if tuple(sorted(perm[:k])) in opt[k]:
                mask |= 1 << bindex[k]
        if mask and mask not in best_ranking_for_mask:
            best_ranking_for_mask[mask] = tuple(perm)
    masks = sorted(best_ranking_for_mask)
    # DP over covered budget layers; state stores selected masks.
    dp = {0: ()}
    for covered in range(all_mask + 1):
        if covered not in dp:
            continue
        for mask in masks:
            nxt = covered | mask
            cand = dp[covered] + (mask,)
            if nxt not in dp or len(cand) < len(dp[nxt]):
                dp[nxt] = cand
    if all_mask not in dp:
        raise AssertionError("one ranking per budget must always provide a finite cover")
    selected_masks = dp[all_mask]
    rankings = [list(best_ranking_for_mask[x]) for x in selected_masks]
    return {
        "dimension": int(len(selected_masks)),
        "rankings": rankings,
        "coverage_masks": list(map(int, selected_masks)),
        "budgets": list(budgets),
        "optimal_set_counts": {str(k): len(opt[k]) for k in budgets},
    }


# ---------------------------------------------------------------------------
# Cost-aware completion of an available linear/PAEC-style certificate

def upper_contribution(alpha: float, lower: float, upper: float) -> float:
    return float(alpha * (upper if alpha >= 0.0 else lower))


def robust_linear_certificate_bound(alpha, lower, upper, correction=0.0):
    alpha = np.asarray(alpha, float)
    lower = np.asarray(lower, float)
    upper = np.asarray(upper, float)
    if not (alpha.shape == lower.shape == upper.shape) or alpha.ndim != 1:
        raise ValueError("certificate vectors must align")
    if np.any(lower > upper):
        raise ValueError("invalid atom intervals")
    if float(correction) > 1e-12:
        raise ValueError("certificate correction must be non-positive")
    # correction <= 0 can only tighten the sound certificate, so dropping it
    # is the same conservative robust bound used in Lean D6-B1.
    return 0.5 * float(sum(upper_contribution(a, l, u) for a, l, u in zip(alpha, lower, upper)))


def certificate_uncertainty_width(alpha, lower, upper):
    alpha = np.asarray(alpha, float)
    lower = np.asarray(lower, float)
    upper = np.asarray(upper, float)
    return float(np.sum(np.abs(alpha) * (upper - lower)))


def choose_cost_aware_certificate(family: Sequence[Mapping], lower, upper, costs, measured=()):
    costs = np.asarray(costs, float)
    measured = set(map(int, measured))
    rows = []
    for idx, cert in enumerate(family):
        alpha = np.asarray(cert["alpha"], float)
        if alpha.shape != costs.shape:
            raise ValueError("certificate alpha/cost vectors must align")
        support = np.flatnonzero(np.abs(alpha) > 1e-12)
        remaining_cost = float(sum(costs[r] for r in support if int(r) not in measured))
        width = certificate_uncertainty_width(alpha, lower, upper)
        bound = robust_linear_certificate_bound(alpha, lower, upper, cert.get("correction", 0.0))
        rows.append({"index": idx, "remaining_cost": remaining_cost, "uncertainty_width": width, "robust_bound": bound})
    if not rows:
        raise ValueError("certificate family must be non-empty")
    by_cost = min(rows, key=lambda x: (x["remaining_cost"], x["uncertainty_width"], x["index"]))
    by_width = min(rows, key=lambda x: (x["uncertainty_width"], x["remaining_cost"], x["index"]))
    return {"rows": rows, "min_remaining_cost": by_cost, "min_uncertainty_width": by_width}
