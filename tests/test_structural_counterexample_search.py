from scripts.run_structural_counterexample_search import _evaluate, _world, directed


def test_structural_candidate_evaluator_uses_actual_support_radius():
    world = _world(3, ((0, 0, 1), (0, 1, 0), (1, 0, 0)), (-1, -1, -1))
    row = _evaluate(world)
    assert row["candidate_violation"] <= 1e-10
    assert row["best_nested_max_regret"] >= 0.0
    assert row["all_optimal_extension_defect"] >= 0.0


def test_directed_structural_search_is_a_falsifier_not_a_proof():
    result = directed(m=4, restarts=2, steps=2, seed=7)
    assert result["mode"] == "directed_binary_support_integer_slopes"
    assert result["best_witness"] is not None
    assert "candidate_violation" in result["best_witness"]
