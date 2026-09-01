from scripts.run_functional_variance_stopping_lab import DEPLOYABLE, DIAGNOSTIC, run


def test_variance_stopping_uses_certificate_count_and_keeps_oracle_diagnostic():
    out = run(instances=2, seeds=(7,), relations=3, actions=4, topk=1,
              alpha=.1, max_n=96, batch=8, pilot_fraction=.15)
    assert out["primary_endpoint"] == "N_certificate"
    assert out["common_random_streams"] is True
    assert "every possible per-cell sample size" in out["confidence_method"]
    assert out["adaptive_stopping_coverage_contract"].startswith("union over n=")
    assert out["deployable_variants"] == list(DEPLOYABLE)
    assert out["diagnostic_variants"] == list(DIAGNOSTIC)
    assert "C_known_sigma" not in DEPLOYABLE
    assert out["deployable_winner_by_median_N_certificate"] in DEPLOYABLE
    for variant in DEPLOYABLE + DIAGNOSTIC:
        assert "median_N_certificate" in out["by_variant"][variant]
        assert out["by_variant"][variant]["false_safe_count"] == 0


def test_variance_stopping_rejects_out_of_protocol_pilot_fraction():
    try:
        run(instances=1, seeds=(1,), relations=3, actions=4, topk=1,
            max_n=96, pilot_fraction=.25)
    except ValueError as exc:
        assert "pilot_fraction" in str(exc)
    else:
        raise AssertionError("out-of-protocol pilot fraction must fail closed")
