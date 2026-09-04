from fractions import Fraction
import numpy as np

from research_chains.d6_active_cell_lp import (
    make_reference,
    derive_active_cell,
    solve_active_cell_lp,
)


def test_d6_active_cell_lp_strong_duality_small_binary_cell():
    rng = np.random.default_rng(7)
    ref = make_reference(4, "uniform", rng)
    F = rng.normal(size=ref.n_worlds)
    cell = derive_active_cell(F, ref)
    sol = solve_active_cell_lp(cell, ref)
    assert sol.success
    assert sol.gamma is not None
    assert sol.dual_cycle_mass is not None
    assert sol.primal_max_violation is not None and sol.primal_max_violation <= 1e-7
    assert sol.duality_gap is not None and sol.duality_gap <= 1e-6
    assert sol.stationarity_max_abs is not None and sol.stationarity_max_abs <= 1e-6
    # Cell inequalities have RHS zero, cycle inequalities RHS one, hence the
    # dual objective is exactly the cycle coefficient mass.
    assert abs(sol.gamma - sol.dual_cycle_mass) <= 1e-6


def test_d6_active_cell_is_balanced_complement():
    rng = np.random.default_rng(11)
    ref = make_reference(6, "point0", rng)
    cell = derive_active_cell(rng.normal(size=ref.n_worlds), ref)
    assert len(cell.selected) == 3
    assert len(cell.competitor) == 3
    assert set(cell.selected).isdisjoint(cell.competitor)
    assert set(cell.selected) | set(cell.competitor) == set(range(6))


def test_random_reference_is_frozen_into_cell_and_reconstructable():
    from research_chains.d6_active_cell_lp import reference_from_cell, exact_verify_binary_solution
    rng = np.random.default_rng(123)
    ref = make_reference(4, "random", rng, random_denominator=20)
    F = rng.normal(size=ref.n_worlds)
    cell = derive_active_cell(F, ref)
    rebuilt = reference_from_cell(cell)
    assert rebuilt.probs == ref.probs
    assert rebuilt.key == "random"
    sol = solve_active_cell_lp(cell, rebuilt, interaction_encoding="range")
    assert sol.success
    exact = exact_verify_binary_solution(sol, rebuilt)
    # Random q is now reconstructable and independently checked.  A zero-margin
    # floating LP optimum may fail exact rationalisation, which must fail closed
    # rather than silently switching to a different q.
    assert exact.get("reason") != "random_reference_not_reconstructed"
    assert exact["q_rational"] == [[str(Fraction(str(x))) for x in row] for row in rebuilt.probs]


def test_active_cell_rejects_reference_probability_mismatch():
    import pytest
    rng = np.random.default_rng(321)
    ref0 = make_reference(4, "point0", rng)
    cell = derive_active_cell(rng.normal(size=ref0.n_worlds), ref0)
    with pytest.raises(ValueError, match="probability mismatch"):
        solve_active_cell_lp(cell, make_reference(4, "uniform", rng))


def test_exact_verifier_enforces_requested_topc_margin():
    from research_chains.d6_active_cell_lp import exact_verify_binary_solution
    rng = np.random.default_rng(9)
    ref = make_reference(4, "point0", rng)
    cell = derive_active_cell(rng.normal(size=ref.n_worlds), ref)
    sol = solve_active_cell_lp(cell, ref, interaction_encoding="range", topc_margin=0.0)
    assert sol.success
    exact_loose = exact_verify_binary_solution(sol, ref, required_topc_margin=0.0)
    assert exact_loose["verified"]
    # Require a margin strictly larger than the exact observed one.
    observed = float(Fraction(exact_loose["topc_min_margin"]))
    exact_strict = exact_verify_binary_solution(sol, ref, required_topc_margin=observed + 0.25)
    assert not exact_strict["verified"]
    assert not exact_strict["topc_margin_ok"]
