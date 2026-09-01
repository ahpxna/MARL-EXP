from __future__ import annotations
import numpy as np

from envs.external.capability_audit import static_capability_profile, audit_environment, probe_execution_and_support
from scripts.run_functional_unknown_variance_lab import run as run_var
from scripts.run_reference_response_budget_lab import run as run_budget
from scripts.run_d6_exact_small_search import run as run_exact
from scripts.run_d6_counterexample_optimizer import run as run_opt


def test_capability_audit_is_fail_closed_for_master_reference_and_dynamic():
    for key in ('rware','flatland','cyborg','cityflow'):
        row=audit_environment(key)
        assert 'per_agent_valid_mask' in row['capabilities']
        assert 'intervention_authority' in row['capabilities']
        assert row['claim_readiness']['MASTER_reference']['ready'] is False
        assert row['claim_readiness']['DYNAMIC']['ready'] is False
        assert set(row['query_capability_layers']) == {
            'EnvironmentCapabilities','PolicyCapabilities','CommunicationCapabilities','CausalContextCapabilities'}


def test_rware_static_profile_does_not_conflate_request_and_honored_support():
    p=static_capability_profile('rware')
    assert p['requestable_joint_support'].status == 'SUPPORTED_WITH_RESTRICTIONS'
    assert p['coupled_honored_support_observed'].status == 'UNVERIFIED'


class _ReceiptToy:
    n_agents=2
    def __init__(self,reject=()): self.reject=set(reject); self.state=0; self.receipt=[0,0]
    def clone_state(self): return self.state,list(self.receipt)
    def restore_state(self,state): self.state,self.receipt=state[0],list(state[1])
    def fixed_continuation_policy(self,agent): return 0
    def valid_action_mask(self,agent): return np.ones(2,dtype=bool)
    def step(self,actions):
        requested=tuple(map(int,actions)); self.receipt=[0,0] if requested in self.reject else list(requested); self.state+=1
        return None,[0.,0.],False,{}
    def trusted_execution_receipt(self): return tuple(self.receipt)


class _SubmittedOnlyToy(_ReceiptToy):
    trusted_execution_receipt=None
    def step(self,actions):
        self.last_actions=list(map(int,actions)); self.state+=1
        return None,[0.,0.],False,{}


def test_partial_support_panel_does_not_create_fake_coupling():
    out=probe_execution_and_support(_ReceiptToy(reject={(1,1)}),max_cells=3)
    assert out['panel_truncated'] is True
    assert out['coupled_honored_support_observed'] is False
    assert out['coupling_witnesses'] == []


def test_explicit_rejected_cross_cell_is_a_coupling_witness():
    out=probe_execution_and_support(_ReceiptToy(reject={(1,1)}),max_cells=4)
    assert out['panel_complete'] is True
    assert out['coupled_honored_support_observed'] is True
    assert out['coupling_witnesses'] == [[1,1]]


def test_submitted_last_actions_are_not_execution_receipts():
    out=probe_execution_and_support(_SubmittedOnlyToy(),max_cells=4)
    assert out['receipts_verified'] == 0
    assert out['coupled_honored_support_observed'] is False


def test_unknown_variance_keeps_known_sigma_out_of_deployable_winner():
    out=run_var(instances=5,seeds=(1,),budgets=(32,),K=6)
    assert 'known_sigma_oracle' not in out['deployable']
    assert out['by_budget']['32']['known_sigma_oracle']['relative_error_bound_violation_count'] == 0
    assert 'final_selection_error_fraction' in out['by_budget']['32']['variance_plugin']
    assert 'pilot_selection_error_fraction' in out['by_budget']['32']['variance_plugin']


def test_reference_response_budget_emits_all_preregistered_metrics():
    out=run_budget(instances=2,seeds=(1,),budgets=(64,),splits=(0,.2,.5),relations=4,actions=3,topk=2)
    assert out['required_metrics'] == ['Q_error','kernel_tv','chi_error','final_score_interval_width','topk_regret','certificate_coverage']
    row=out['by_budget']['64']['0.2']
    for key in out['required_metrics']:
        assert np.isfinite(row[key])
    assert out['common_random_streams'] is True
    assert out['kernel_smoothing'] == 0.0
    assert out['by_budget']['64']['0.0']['mean_nKappa'] == 0.0
    assert set(out['error_decomposition']) == {'e_stat','e_kappa','chi','e_decay'}


def test_exact_d6_search_is_exact_finite_and_reports_candidate_status():
    out=run_exact(m=3,k_values=(1,2),value_radius=1,anchor_zero=True)
    assert out['worlds_enumerated'] == 3**7
    assert out['evidence_class'] == 'EXHAUSTIVE_FINITE_EXACT_RATIONAL'
    assert 'candidate_killed' in out


def test_exact_d6_search_supports_coordinate_specific_rational_q():
    from fractions import Fraction
    out=run_exact(m=2,k_values=(1,),value_radius=1,anchor_zero=True,q_grid=(Fraction(1,4),Fraction(3,4)))
    assert out['reference_vectors'] == 4
    assert out['world_reference_pairs_evaluated'] == out['worlds_enumerated']*4
    assert out['best_ratio_witness']['reference_q']


def test_counterexample_optimizer_never_calls_survival_a_proof():
    out=run_opt(restarts=5,steps=5,m=3,alphabet=2,k=1,seed=2)
    assert out['evidence_class'] == 'DIRECTED_FALSIFICATION_NOT_PROOF'
    assert out['candidate_threshold'] == .5
