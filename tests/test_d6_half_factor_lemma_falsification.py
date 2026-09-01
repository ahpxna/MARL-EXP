from fractions import Fraction
import numpy as np

from scripts.run_d6_half_factor_lemma_falsification import (
    evaluate_exact,
    evaluate_float,
)


def test_h3_prime_equals_direct_exact():
    values = [
        [[Fraction(0), Fraction(1)], [Fraction(-1), Fraction(2)]],
        [[Fraction(1), Fraction(-2)], [Fraction(2), Fraction(0)]],
    ]
    q = (
        (Fraction(3,4), Fraction(1,4)),
        (Fraction(1,2), Fraction(1,2)),
        (Fraction(1,4), Fraction(3,4)),
    )
    d = evaluate_exact(values, q, 1)
    assert isinstance(d["delta_square"], Fraction)
    assert isinstance(d["half_rhs"], Fraction)
    assert d["H3_prime_direct_identity_max_abs"] == 0
    for row in d["competitors"]:
        assert row["V_slack"] == row["V_direct"]


def test_h3_prime_equals_direct_float():
    values = np.asarray([
        [[0.0, 1.0], [-1.0, 2.0]],
        [[1.0, -2.0], [2.0, 0.0]],
    ])
    q = np.asarray([
        [0.75, 0.25],
        [0.50, 0.50],
        [0.25, 0.75],
    ])
    d = evaluate_float(values, q, 1)
    assert d["H3_prime_direct_identity_max_abs"] <= 1e-12


def test_additive_world_has_zero_delta_and_no_positive_direct_violation():
    # F(a0,a1)=a0+2*a1 is additive, so delta_square=0 and Top-C is exact.
    values = np.asarray([[0.0, 2.0], [1.0, 3.0]])
    q = np.asarray([[0.5, 0.5], [0.5, 0.5]])
    d = evaluate_float(values, q, 1)
    assert abs(d["delta_square"]) <= 1e-12
    assert d["H3_direct_max_violation"] <= 1e-12


def test_nontrivial_competitor_metrics_exist():
    values = np.asarray([[0.0, 2.0], [1.0, 3.0]])
    q = np.asarray([[0.5, 0.5], [0.5, 0.5]])
    d = evaluate_float(values, q, 1)
    assert "H3_old_max_violation_nontrivial" in d
    assert "H3_direct_max_violation_nontrivial" in d
    assert sum(bool(r["is_nontrivial_competitor"]) for r in d["competitors"]) == 1
