import numpy as np

from research_chains.finite_world import FiniteResponseWorld
from research_chains.support import SupportModel
from research_chains.kprefix import (
    acceptable_layers,
    best_chain_oracle,
    chain_to_ranking,
    dense_subset_objective,
    exact_cover_layers,
    epsilon_k_exact,
    greedy_cover_rank,
    menu_metrics,
)


def _world():
    # Deliberately non-Cartesian support, while preserving both actions in each
    # marginal, so supportOsc can produce non-nested budget optima.
    omega = (
        (0, 0, 0, 0),
        (1, 1, 0, 0),
        (0, 1, 1, 0),
        (0, 0, 1, 1),
        (1, 0, 0, 1),
    )
    support = SupportModel((2, 2, 2, 2), omega, key="test")
    primitives = tuple(np.asarray([0.0, x]) for x in (4.0, -3.0, 2.0, -5.0))
    return FiniteResponseWorld(support, primitives)


def test_chain_extension_realizes_all_requested_prefixes():
    chain = (0b0001, 0b0101, 0b1101)
    ranking = chain_to_ranking(chain, 4)
    for mask in chain:
        got = sum(1 << ranking[j] for j in range(mask.bit_count()))
        assert got == mask


def test_exact_cover_and_milp_agree_and_greedy_covers():
    world = _world()
    values = dense_subset_objective(world)
    layers = acceptable_layers(values, 4, 0.0)
    exact = exact_cover_layers(layers, 4, verify_milp=True)
    greedy = greedy_cover_rank(layers, 4)
    assert exact.dimension >= 1
    assert greedy.dimension >= exact.dimension
    assert exact.milp_objective is not None
    assert abs(exact.milp_objective - exact.dimension) <= 1e-7
    assert menu_metrics(values, 4, exact.rankings)["worst_budget_regret"] <= 1e-10


def test_epsilon_k_is_monotone_in_K():
    values = dense_subset_objective(_world())
    rows = [epsilon_k_exact(values, 4, K) for K in (1, 2, 3)]
    eps = [r["epsilon_K"] for r in rows]
    assert eps[1] <= eps[0] + 1e-12
    assert eps[2] <= eps[1] + 1e-12


def test_best_chain_hits_positive_weight_layer():
    values = dense_subset_objective(_world())
    layers = acceptable_layers(values, 4, 0.0)
    out = best_chain_oracle(layers, 4, {1: 0.0, 2: 4.0, 3: 0.0})
    assert 2 in out.budgets
    assert out.value >= 4.0
