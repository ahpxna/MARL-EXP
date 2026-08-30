from __future__ import annotations
import numpy as np

from envs.external.capability_audit import static_capability_profile, audit_environment
from scripts.run_functional_unknown_variance_lab import run as run_var
from scripts.run_reference_response_budget_lab import run as run_budget
from scripts.run_d6_exact_small_search import run as run_exact
from scripts.run_d6_counterexample_optimizer import run as run_opt


def test_capability_audit_is_fail_closed_for_master_reference_and_dynamic():
    for key in ('rware','flatland','cyborg','cityflow'):
        row=audit_environment(key)
        assert row['claim_readiness']['MASTER_reference']['ready'] is False
        assert row['claim_readiness']['DYNAMIC']['ready'] is False


def test_rware_static_profile_does_not_conflate_request_and_honored_support():
    p=static_capability_profile('rware')
    assert p['requestable_joint_support'].status == 'SUPPORTED_WITH_RESTRICTIONS'
    assert p['coupled_honored_support_observed'].status == 'UNVERIFIED'


def test_unknown_variance_keeps_known_sigma_out_of_deployable_winner():
    out=run_var(instances=5,seeds=(1,),budgets=(32,),K=6)
    assert 'known_sigma_oracle' not in out['deployable']
    assert out['by_budget']['32']['known_sigma_oracle']['relative_error_bound_violation_count'] == 0


def test_reference_response_budget_emits_all_preregistered_metrics():
    out=run_budget(instances=2,seeds=(1,),budgets=(64,),splits=(.2,.5),relations=4,actions=3,topk=2)
    assert out['required_metrics'] == ['Q_error','kernel_tv','chi_error','final_score_interval_width','topk_regret','certificate_coverage']
    row=out['by_budget']['64']['0.2']
    for key in out['required_metrics']:
        assert np.isfinite(row[key])


def test_exact_d6_search_is_exact_finite_and_reports_candidate_status():
    out=run_exact(m=3,k_values=(1,2),value_radius=1,anchor_zero=True)
    assert out['worlds_enumerated'] == 3**7
    assert out['evidence_class'] == 'EXHAUSTIVE_FINITE_EXACT_RATIONAL'
    assert 'candidate_killed' in out


def test_counterexample_optimizer_never_calls_survival_a_proof():
    out=run_opt(restarts=5,steps=5,m=3,alphabet=2,k=1,seed=2)
    assert out['evidence_class'] == 'DIRECTED_FALSIFICATION_NOT_PROOF'
    assert out['candidate_threshold'] == .5
