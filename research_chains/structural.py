"""Small finite discovery laboratory for support-constrained rankability."""

from __future__ import annotations

import itertools
from typing import Sequence

import numpy as np

from .certificates import exact_optimum, topk_indices
from .finite_world import FiniteResponseWorld


def globally_coextremizable(world: FiniteResponseWorld) -> bool:
    max_actions, min_actions = [], []
    for j in range(world.support.n_relations):
        projection = world.support.projection(j)
        values = world.primitives[j]
        max_value = max(values[a] for a in projection)
        min_value = min(values[a] for a in projection)
        max_actions.append({a for a in projection if np.isclose(values[a], max_value)})
        min_actions.append({a for a in projection if np.isclose(values[a], min_value)})
    has_max = any(all(action[j] in max_actions[j] for j in range(world.support.n_relations)) for action in world.support.omega)
    has_min = any(all(action[j] in min_actions[j] for j in range(world.support.n_relations)) for action in world.support.omega)
    return bool(has_max and has_min)


def all_subsets_modular(world: FiniteResponseWorld, atol: float = 1e-10) -> bool:
    m = world.support.n_relations
    spans = world.component_spans()
    for omitted_size in range(1, m + 1):
        for omitted in itertools.combinations(range(m), omitted_size):
            retained = tuple(j for j in range(m) if j not in omitted)
            F = 2.0 * world.additive_radius(retained)
            if not np.isclose(F, float(np.sum(spans[list(omitted)])), atol=atol, rtol=0.0):
                return False
    return True


def scalar_prefix_order_exists(world: FiniteResponseWorld, atol: float = 1e-10):
    """Existence of a single ordering whose every prefix is budget-optimal."""
    m = world.support.n_relations
    optimal = {}
    for k in range(1, m + 1):
        value, sets = exact_optimum(world, k)
        optimal[k] = {tuple(sorted(s)) for s in sets}
    for permutation in itertools.permutations(range(m)):
        if all(tuple(sorted(permutation[:k])) in optimal[k] for k in range(1, m + 1)):
            return True, permutation
    return False, None


def topc_exact_all_budgets(world: FiniteResponseWorld) -> bool:
    spans = world.component_spans()
    for k in range(1, world.support.n_relations + 1):
        retained = topk_indices(spans, k)
        optimum, _ = exact_optimum(world, k)
        if world.additive_radius(retained) > optimum + 1e-10:
            return False
    return True


def analyze_world(world: FiniteResponseWorld):
    prefix, order = scalar_prefix_order_exists(world)
    return {
        "globally_coextremizable": globally_coextremizable(world),
        "all_subsets_modular": all_subsets_modular(world),
        "scalar_prefix_order_exists": bool(prefix),
        "scalar_prefix_order": None if order is None else list(order),
        "topc_exact_all_budgets": topc_exact_all_budgets(world),
    }
