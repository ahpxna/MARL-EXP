"""Support-compression objectives and deterministic certificate hierarchy."""

from __future__ import annotations

import itertools
from typing import Iterable, Sequence

import numpy as np
from scipy.optimize import linprog

from .finite_world import FiniteResponseWorld
from .support import SupportBracket, SupportModel


def oscillation(values: Sequence[float]) -> float:
    values = np.asarray(values, dtype=np.float64)
    if values.size == 0 or not np.all(np.isfinite(values)):
        raise ValueError("oscillation requires a non-empty finite vector")
    return float(np.max(values) - np.min(values))


def quotient_sup_distance(estimated: Sequence[float], truth: Sequence[float]) -> float:
    """Distance modulo action-independent offsets: inf_c ||e-t-c||_inf."""
    delta = np.asarray(estimated, dtype=np.float64) - np.asarray(truth, dtype=np.float64)
    if delta.ndim != 1 or delta.size == 0 or not np.all(np.isfinite(delta)):
        raise ValueError("estimated/truth must be finite one-dimensional vectors")
    return 0.5 * oscillation(delta)


def topk_indices(scores: Sequence[float], k: int) -> tuple[int, ...]:
    scores = np.asarray(scores, dtype=np.float64)
    if scores.ndim != 1 or not np.all(np.isfinite(scores)):
        raise ValueError("scores must be a finite vector")
    if type(k) is not int or not 0 < k <= scores.size:
        raise ValueError("k must be in [1, number of scores]")
    return tuple(sorted(range(scores.size), key=lambda j: (-scores[j], j))[:k])


def exact_optimum(world: FiniteResponseWorld, k: int, *, true_loss: bool = False, support: SupportModel | None = None):
    m = world.support.n_relations
    if not 0 < int(k) <= m:
        raise ValueError("invalid budget")
    objective = world.true_compression_loss if true_loss else world.additive_radius
    best, best_sets = float("inf"), []
    for retained in itertools.combinations(range(m), int(k)):
        value = objective(retained, support=support)
        if value < best - 1e-12:
            best, best_sets = value, [retained]
        elif abs(value - best) <= 1e-12:
            best_sets.append(retained)
    return float(best), tuple(best_sets)


def deficit_terms(world: FiniteResponseWorld, omitted: Iterable[int]):
    omitted = tuple(sorted({int(j) for j in omitted}))
    if not omitted:
        return {"F": 0.0, "M": 0.0, "d": 0.0, "e_plus": 0.0, "e_minus": 0.0}
    support = world.support
    maxs, mins, spans = {}, {}, {}
    for j in omitted:
        idx = np.asarray(support.projection(j), dtype=int)
        vals = world.primitives[j][idx]
        maxs[j], mins[j] = float(np.max(vals)), float(np.min(vals))
        spans[j] = maxs[j] - mins[j]
    sums = np.asarray([
        sum(world.primitives[j][a[j]] for j in omitted) for a in support.omega
    ], dtype=np.float64)
    F = oscillation(sums)
    M = float(sum(spans.values()))
    e_plus = min(
        sum(maxs[j] - world.primitives[j][a[j]] for j in omitted)
        for a in support.omega
    )
    e_minus = min(
        sum(world.primitives[j][a[j]] - mins[j] for j in omitted)
        for a in support.omega
    )
    return {
        "F": float(F), "M": M, "d": float(M - F),
        "e_plus": float(e_plus), "e_minus": float(e_minus),
    }


def global_extremizability_defect(world: FiniteResponseWorld) -> float:
    all_rel = tuple(range(world.support.n_relations))
    terms = deficit_terms(world, all_rel)
    return float(terms["e_plus"] + terms["e_minus"])


def zeta_def(world: FiniteResponseWorld, k: int) -> float:
    m = world.support.n_relations
    omitted_size = m - int(k)
    if omitted_size == 0:
        return 0.0
    return float(max(
        deficit_terms(world, omitted)["d"]
        for omitted in itertools.combinations(range(m), omitted_size)
    ))


def topc_regret(world: FiniteResponseWorld, k: int) -> float:
    spans = world.component_spans()
    retained = topk_indices(spans, int(k))
    optimum, _ = exact_optimum(world, int(k))
    return float(world.additive_radius(retained) - optimum)


def lp_lower_bound(world: FiniteResponseWorld, k: int, *, support: SupportModel | None = None):
    """LP relaxation lower bound for exact support-aware selection.

    Variables are [x_0..x_{m-1}, U, L] with x being retained fractions.
    """
    support = world.support if support is None else support
    m = world.support.n_relations
    nvar = m + 2
    c = np.zeros(nvar, dtype=np.float64)
    c[m] = 0.5
    c[m + 1] = -0.5
    A_ub, b_ub = [], []
    for action in support.omega:
        row_f = np.asarray([world.primitives[j][action[j]] for j in range(m)], dtype=np.float64)
        total = float(np.sum(row_f))
        # total - row_f @ x <= U
        row = np.zeros(nvar); row[:m] = -row_f; row[m] = -1.0
        A_ub.append(row); b_ub.append(-total)
        # L <= total - row_f @ x  -> row_f @ x + L <= total
        row = np.zeros(nvar); row[:m] = row_f; row[m + 1] = 1.0
        A_ub.append(row); b_ub.append(total)
    A_eq = np.zeros((1, nvar)); A_eq[0, :m] = 1.0
    b_eq = np.asarray([float(k)])
    bounds = [(0.0, 1.0)] * m + [(None, None), (None, None)]
    res = linprog(
        c, A_ub=np.asarray(A_ub), b_ub=np.asarray(b_ub),
        A_eq=A_eq, b_eq=b_eq, bounds=bounds, method="highs",
    )
    if not res.success or res.fun is None or not np.isfinite(res.fun):
        raise RuntimeError(f"LP lower bound failed closed: status={res.status} message={res.message}")
    return float(max(0.0, res.fun)), res


def fixed_subset_radius_error_bound(world: FiniteResponseWorld, estimated_primitives, retained: Sequence[int]):
    retained = {int(j) for j in retained}
    deltas = np.asarray([
        quotient_sup_distance(est, true)
        for est, true in zip(estimated_primitives, world.primitives)
    ], dtype=np.float64)
    return float(sum(deltas[j] for j in range(len(deltas)) if j not in retained)), deltas


def delta_k_circ(deltas: Sequence[float], k: int) -> float:
    deltas = np.asarray(deltas, dtype=np.float64)
    omitted_size = deltas.size - int(k)
    if omitted_size <= 0:
        return 0.0
    # largest possible omitted uncertainty sum
    return float(np.sum(np.sort(deltas)[-omitted_size:]))


def support_bracket_regret_bound(world: FiniteResponseWorld, bracket: SupportBracket, retained: Sequence[int], k: int, *, use_lp: bool = False) -> float:
    if not bracket.validates(world.support):
        raise ValueError("truth support is not contained in supplied support bracket")
    upper_candidate = world.additive_radius(retained, support=bracket.upper)
    if use_lp:
        lower_star, _ = lp_lower_bound(world, int(k), support=bracket.lower)
    else:
        lower_star, _ = exact_optimum(world, int(k), support=bracket.lower)
    return float(upper_candidate - lower_star)
