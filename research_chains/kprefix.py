"""Exact/scalable algorithms for K-Prefix Incremental Optimisation.

The functions here make the structural theory operational without relying on
m! ranking enumeration:

* exact small scale: acceptable subsets -> inclusion DAG -> coverage masks ->
  exact set-cover DP and optional SciPy MILP cross-check;
* scalable: maximum-weight chain oracle and greedy COVER-RANK;
* fixed-K frontier: exact epsilon_K via the finite set of subset-regret
  breakpoints.

The code works with any finite subset objective supplied as a mapping from
bitmask to value.  Convenience adapters are provided for FiniteResponseWorld.
"""
from __future__ import annotations

from dataclasses import dataclass
import itertools
import math
import time
from typing import Mapping, Sequence

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy import sparse

from .finite_world import FiniteResponseWorld


@dataclass(frozen=True)
class ChainOracleResult:
    value: float
    chain_masks: tuple[int, ...]
    budgets: tuple[int, ...]
    ranking: tuple[int, ...]


@dataclass(frozen=True)
class CoverResult:
    dimension: int
    rankings: tuple[tuple[int, ...], ...]
    chain_masks: tuple[tuple[int, ...], ...]
    coverage_masks: tuple[int, ...]
    method: str
    milp_objective: float | None = None


def mask_from_subset(subset: Sequence[int]) -> int:
    mask = 0
    for j in subset:
        mask |= 1 << int(j)
    return int(mask)


def subset_from_mask(mask: int, m: int) -> tuple[int, ...]:
    return tuple(j for j in range(int(m)) if int(mask) & (1 << j))


def prefix_mask(ranking: Sequence[int], k: int) -> int:
    return mask_from_subset(tuple(ranking)[: int(k)])


def dense_subset_objective(world: FiniteResponseWorld) -> np.ndarray:
    m = world.support.n_relations
    values = np.empty(1 << m, dtype=np.float64)
    for mask in range(1 << m):
        values[mask] = world.additive_radius(subset_from_mask(mask, m))
    return values


def optima_by_budget(values: Sequence[float], m: int) -> dict[int, float]:
    values = np.asarray(values, dtype=np.float64)
    if values.shape != (1 << int(m),):
        raise ValueError("dense objective must have 2^m entries")
    out = {}
    for k in range(1, int(m)):
        masks = [mask for mask in range(1 << m) if mask.bit_count() == k]
        out[k] = float(min(values[mask] for mask in masks))
    return out


def regret_table(values: Sequence[float], m: int) -> np.ndarray:
    values = np.asarray(values, dtype=np.float64)
    opt = optima_by_budget(values, m)
    out = np.full_like(values, np.nan)
    for mask in range(1 << m):
        k = mask.bit_count()
        if k in opt:
            out[mask] = float(values[mask] - opt[k])
    return out


def acceptable_layers(values: Sequence[float], m: int, epsilon: float = 0.0) -> dict[int, tuple[int, ...]]:
    values = np.asarray(values, dtype=np.float64)
    opt = optima_by_budget(values, m)
    eps = float(epsilon)
    out = {}
    for k in range(1, int(m)):
        out[k] = tuple(
            mask for mask in range(1 << m)
            if mask.bit_count() == k and values[mask] <= opt[k] + eps + 1e-12
        )
        if not out[k]:
            raise AssertionError("every budget must contain at least one epsilon-optimal set")
    return out


def inclusion_dag(layers: Mapping[int, Sequence[int]]) -> tuple[tuple[int, ...], dict[int, tuple[int, ...]]]:
    nodes = tuple(sorted({int(mask) for masks in layers.values() for mask in masks}, key=lambda x: (x.bit_count(), x)))
    pred: dict[int, tuple[int, ...]] = {}
    for mask in nodes:
        km = mask.bit_count()
        pred[mask] = tuple(
            other for other in nodes
            if other.bit_count() < km and (other & mask) == other
        )
    return nodes, pred


def chain_to_ranking(chain_masks: Sequence[int], m: int) -> tuple[int, ...]:
    """Construct a full ranking whose specified prefixes equal a nested chain."""
    chain = tuple(sorted({int(x) for x in chain_masks}, key=lambda x: (x.bit_count(), x)))
    prev = 0
    ranking: list[int] = []
    for mask in chain:
        if (prev & mask) != prev:
            raise ValueError("chain masks are not nested")
        new_items = [j for j in range(int(m)) if (mask & (1 << j)) and not (prev & (1 << j))]
        ranking.extend(sorted(new_items))
        prev = mask
    ranking.extend(j for j in range(int(m)) if not (prev & (1 << j)))
    if sorted(ranking) != list(range(int(m))):
        raise AssertionError("chain extension did not produce a full ranking")
    # Verify exact prefixes at every selected chain cardinality.
    for mask in chain:
        if prefix_mask(ranking, mask.bit_count()) != mask:
            raise AssertionError("constructed ranking fails requested chain prefix")
    return tuple(ranking)


def best_chain_oracle(layers: Mapping[int, Sequence[int]], m: int, weights: Mapping[int, float] | None = None) -> ChainOracleResult:
    nodes, pred = inclusion_dag(layers)
    weights = {int(k): float(v) for k, v in (weights or {k: 1.0 for k in layers}).items()}
    best_val: dict[int, float] = {}
    best_path: dict[int, tuple[int, ...]] = {}
    for node in nodes:
        k = node.bit_count()
        own = float(weights.get(k, 0.0))
        candidates = [(0.0, ())]
        candidates.extend((best_val[p], best_path[p]) for p in pred[node])
        prev_val, prev_path = max(candidates, key=lambda row: (row[0], len(row[1]), tuple(-x for x in row[1])))
        best_val[node] = prev_val + own
        best_path[node] = prev_path + (node,)
    if not nodes:
        return ChainOracleResult(0.0, (), (), tuple(range(int(m))))
    endpoint = max(nodes, key=lambda n: (best_val[n], len(best_path[n]), -n))
    path = best_path[endpoint]
    budgets = tuple(mask.bit_count() for mask in path if mask.bit_count() in layers)
    return ChainOracleResult(float(best_val[endpoint]), path, budgets, chain_to_ranking(path, m))


def _all_chain_coverage_masks(layers: Mapping[int, Sequence[int]], m: int) -> tuple[dict[int, tuple[int, ...]], tuple[int, ...]]:
    """Enumerate distinct budget-coverage masks attainable by inclusion chains.

    At most 2^(m-1) coverage masks exist, even when the number of rankings is
    factorial.  Store one concrete chain per mask for exact set cover.
    """
    budgets = tuple(sorted(int(k) for k in layers))
    bidx = {k: i for i, k in enumerate(budgets)}
    nodes, pred = inclusion_dag(layers)
    ending: dict[int, dict[int, tuple[int, ...]]] = {}
    global_mask_to_chain: dict[int, tuple[int, ...]] = {}
    for node in nodes:
        bit = 1 << bidx[node.bit_count()]
        states = {bit: (node,)}
        for p in pred[node]:
            for cov, path in ending[p].items():
                nxt = cov | bit
                cand = path + (node,)
                old = states.get(nxt)
                if old is None or len(cand) > len(old):
                    states[nxt] = cand
        ending[node] = states
        for cov, path in states.items():
            old = global_mask_to_chain.get(cov)
            if old is None or len(path) > len(old):
                global_mask_to_chain[cov] = path
    return global_mask_to_chain, budgets


def exact_cover_layers(layers: Mapping[int, Sequence[int]], m: int, *, verify_milp: bool = True) -> CoverResult:
    mask_to_chain, budgets = _all_chain_coverage_masks(layers, m)
    if not budgets:
        return CoverResult(1, (tuple(range(m)),), ((),), (0,), "trivial")
    full = (1 << len(budgets)) - 1
    coverage_masks = tuple(sorted(mask_to_chain, key=lambda x: (-x.bit_count(), x)))
    # Exact DP set cover over budget-layer masks.
    dp: dict[int, tuple[int, ...]] = {0: ()}
    for state in range(full + 1):
        if state not in dp:
            continue
        for cov in coverage_masks:
            nxt = state | cov
            cand = dp[state] + (cov,)
            old = dp.get(nxt)
            if old is None or len(cand) < len(old):
                dp[nxt] = cand
    if full not in dp:
        raise AssertionError("one chain per budget must cover every layer")
    selected_cov = dp[full]
    chains = tuple(mask_to_chain[cov] for cov in selected_cov)
    rankings = tuple(chain_to_ranking(chain, m) for chain in chains)

    milp_obj = None
    if verify_milp and coverage_masks:
        # Minimum-cardinality set cover over the distinct chain-coverage columns.
        A = np.zeros((len(budgets), len(coverage_masks)), dtype=np.float64)
        for col, cov in enumerate(coverage_masks):
            for r in range(len(budgets)):
                A[r, col] = 1.0 if cov & (1 << r) else 0.0
        res = milp(
            c=np.ones(len(coverage_masks), dtype=np.float64),
            integrality=np.ones(len(coverage_masks), dtype=np.int8),
            bounds=Bounds(np.zeros(len(coverage_masks)), np.ones(len(coverage_masks))),
            constraints=LinearConstraint(sparse.csr_matrix(A), lb=np.ones(len(budgets)), ub=np.full(len(budgets), np.inf)),
            options={"presolve": True},
        )
        if not res.success:
            raise RuntimeError(f"set-cover MILP failed: {res.message}")
        milp_obj = float(res.fun)
        if abs(milp_obj - len(selected_cov)) > 1e-7:
            raise AssertionError("DP/MILP exact cover disagreement")
    return CoverResult(len(selected_cov), rankings, chains, tuple(map(int, selected_cov)), "coverage-mask-dp+milp", milp_obj)


def greedy_cover_rank(layers: Mapping[int, Sequence[int]], m: int) -> CoverResult:
    budgets = tuple(sorted(layers))
    uncovered = set(budgets)
    rankings: list[tuple[int, ...]] = []
    chains: list[tuple[int, ...]] = []
    coverage: list[int] = []
    bidx = {k: i for i, k in enumerate(budgets)}
    while uncovered:
        weights = {k: (1.0 if k in uncovered else 0.0) for k in budgets}
        best = best_chain_oracle(layers, m, weights)
        hit = set(best.budgets) & uncovered
        if not hit:
            raise AssertionError("Best-Chain failed to hit any uncovered budget")
        rankings.append(best.ranking)
        chains.append(best.chain_masks)
        cov = 0
        for k in best.budgets:
            cov |= 1 << bidx[k]
        coverage.append(cov)
        uncovered -= hit
    return CoverResult(len(rankings), tuple(rankings), tuple(chains), tuple(coverage), "greedy-COVER-RANK")


def menu_metrics(values: Sequence[float], m: int, rankings: Sequence[Sequence[int]]) -> dict:
    values = np.asarray(values, dtype=np.float64)
    opt = optima_by_budget(values, m)
    rows = []
    for k in range(1, int(m)):
        candidates = [float(values[prefix_mask(r, k)]) for r in rankings]
        achieved = min(candidates)
        regret = float(achieved - opt[k])
        rows.append({"k": k, "optimum": opt[k], "achieved": achieved, "regret": regret})
    regrets = np.asarray([r["regret"] for r in rows], dtype=np.float64)
    return {
        "worst_budget_regret": float(np.max(regrets)) if regrets.size else 0.0,
        "mean_budget_regret": float(np.mean(regrets)) if regrets.size else 0.0,
        "per_budget": rows,
    }


def epsilon_k_exact(values: Sequence[float], m: int, K: int, *, verify_milp: bool = False) -> dict:
    values = np.asarray(values, dtype=np.float64)
    K = int(K)
    if K <= 0:
        raise ValueError("K must be positive")
    regrets = regret_table(values, m)
    candidates = sorted({0.0} | {float(x) for x in regrets[np.isfinite(regrets)] if x >= -1e-12})
    started = time.perf_counter()
    for eps in candidates:
        layers = acceptable_layers(values, m, eps)
        cover = exact_cover_layers(layers, m, verify_milp=verify_milp)
        if cover.dimension <= K:
            metrics = menu_metrics(values, m, cover.rankings)
            return {
                "epsilon_K": float(eps),
                "rankings": [list(r) for r in cover.rankings[:K]],
                "dimension_at_epsilon": int(cover.dimension),
                "metrics": metrics,
                "solve_seconds": float(time.perf_counter() - started),
                "method": "exact-breakpoint-search",
            }
    raise AssertionError("epsilon_K must be finite once every budget can use its own chain")


def epsilon_k_greedy(values: Sequence[float], m: int, K: int) -> dict:
    values = np.asarray(values, dtype=np.float64)
    regrets = regret_table(values, m)
    candidates = sorted({0.0} | {float(x) for x in regrets[np.isfinite(regrets)] if x >= -1e-12})
    started = time.perf_counter()
    for eps in candidates:
        layers = acceptable_layers(values, m, eps)
        cover = greedy_cover_rank(layers, m)
        if cover.dimension <= int(K):
            metrics = menu_metrics(values, m, cover.rankings[:K])
            return {
                "epsilon_K": float(eps),
                "rankings": [list(r) for r in cover.rankings[:K]],
                "dimension_at_epsilon": int(cover.dimension),
                "metrics": metrics,
                "solve_seconds": float(time.perf_counter() - started),
                "method": "greedy-COVER-RANK-breakpoint-search",
            }
    raise AssertionError("greedy epsilon_K search must terminate")


def structural_world_features(world: FiniteResponseWorld) -> np.ndarray:
    """Fixed-m features for KPrefixNet: spans, support density, pair defects."""
    m = world.support.n_relations
    spans = world.component_spans().astype(np.float64)
    scale = float(max(1e-12, np.max(np.abs(spans))))
    spans = spans / scale
    full_size = float(np.prod(world.support.action_sizes))
    density = float(len(world.support.omega) / full_size)
    omega = tuple(world.support.omega)
    pair_defects = []
    for i in range(m):
        for j in range(i + 1, m):
            observed = {(a[i], a[j]) for a in omega}
            full_pair = world.support.action_sizes[i] * world.support.action_sizes[j]
            pair_defects.append(1.0 - len(observed) / float(full_pair))
    return np.asarray(list(spans) + [density] + pair_defects, dtype=np.float32)


def estimate_menu_memory_bytes(rankings: Sequence[Sequence[int]]) -> int:
    return int(sum(len(tuple(r)) for r in rankings) * np.dtype(np.int32).itemsize)
