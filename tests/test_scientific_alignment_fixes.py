from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import numpy as np
import pytest

from research_chains.experimental_extensions import cascade_evaluation, d6_diagnostics
from research_chains.finite_world import FiniteResponseWorld
from research_chains.pairwise import ScoreErrorTerm, compose_same_target_score_error
from research_chains.support import SupportModel


def _zero_world(m=3):
    sizes=(2,)*m
    return FiniteResponseWorld(
        SupportModel(sizes, tuple(np.ndindex(*sizes)), key='full'),
        tuple(np.zeros(2) for _ in range(m)),
    )


def test_master_cascade_keeps_gamma_op_active_and_reports_box_comparator():
    out=cascade_evaluation(_zero_world(3), [0.,0.,0.], [2.,0.,0.], 1, 1.5)
    assert out['gamma_box'] == pytest.approx(1.0)
    assert out['gamma_operational'] == pytest.approx(2.0)
    assert out['box_certificate'] == pytest.approx(1.0)
    assert out['operational_certificate'] == pytest.approx(2.0)
    assert out['certificate'] == pytest.approx(out['operational_certificate'])
    assert out['active_certificate'] == 'Gamma_op'
    assert out['fallback'] is True


def test_same_target_error_composition_fails_closed_on_estimand_mismatch():
    good=compose_same_target_score_error(
        ScoreErrorTerm('primitive_capacity_span',[.1,.2],'stat'),
        ScoreErrorTerm('primitive_capacity_span',[.3,.4],'reference'),
    )
    assert np.allclose(good,[.4,.6])
    with pytest.raises(ValueError,match='do not share one target'):
        compose_same_target_score_error(
            ScoreErrorTerm('isolated_capacity',[.1,.2],'reference'),
            ScoreErrorTerm('feasible_capacity',[.3,.4],'support'),
        )


def test_d6_rejects_nonnormalized_negative_and_wrong_width_product_weights():
    world=_zero_world(2)
    assert d6_diagnostics(world,{0:[.5,.5],1:[.25,.75]},1)['applicable'] is True
    bad=d6_diagnostics(world,{0:[1.,2.],1:[.5,.5]},1)
    assert bad['applicable'] is False and bad['reason']=='invalid_product_marginal'
    assert 'normalized' in bad['detail']
    bad=d6_diagnostics(world,{0:[-.1,1.1],1:[.5,.5]},1)
    assert bad['applicable'] is False and bad['reason']=='invalid_product_marginal'
    bad=d6_diagnostics(world,{0:[1.],1:[.5,.5]},1)
    assert bad['applicable'] is False and bad['reason']=='invalid_product_marginal'


class _PolicyBaselineToy:
    n_agents=2
    def __init__(self,rewrite=False):
        self.rewrite=bool(rewrite); self.state=0; self.receipt=[1,1]
    def clone_state(self): return (self.state,list(self.receipt))
    def restore_state(self,state): self.state,self.receipt=state[0],list(state[1])
    def fixed_continuation_policy(self,agent): return 0
    def step(self,actions):
        self.state+=1
        self.receipt=[1,1] if self.rewrite else list(map(int,actions))
        return None,[0.,0.],False,{}
    def trusted_execution_receipt(self): return tuple(self.receipt)


def test_external_query_policy_baseline_is_evaluated_at_current_snapshot_not_reused_from_prior_receipt():
    from scripts.run_external_query_transfer import _verified_policy_baseline
    env=_PolicyBaselineToy(rewrite=False); snapshot=env.clone_state()
    requested,receipt=_verified_policy_baseline(env,snapshot)
    assert requested == [0,0]
    assert receipt == [0,0]
    assert env.state == snapshot[0]
    assert env.receipt == snapshot[1]


def test_external_query_policy_baseline_fails_closed_when_policy_action_is_not_honored():
    from scripts.run_external_query_transfer import _verified_policy_baseline
    env=_PolicyBaselineToy(rewrite=True); snapshot=env.clone_state()
    with pytest.raises(RuntimeError,match='baseline was not honored'):
        _verified_policy_baseline(env,snapshot)


def test_query_ate_name_does_not_alias_blocked_generic_causal_contribution():
    from research_chains.query_contracts import QUERY_SPECS
    assert QUERY_SPECS['causal_contribution'].required_capabilities == ('causal_context_provider',)
    assert QUERY_SPECS['interventional_response_ate_vs_noop'].semantic_target == '|E_uniform Q_j-Q_j(a_noop)|'
    assert 'generic causal ATE' in QUERY_SPECS['interventional_response_ate_vs_noop'].reference_semantics['warning']


def test_randomization_query_and_D_reference_are_typed():
    from research_chains.query_contracts import QUERY_SPECS
    assert QUERY_SPECS['randomization_effect'].semantic_target == '|E_pi[Q_j]-E_q[Q_j]|'
    d=QUERY_SPECS['signed_policy_effect'].reference_semantics
    assert d['pi'] == 'deterministic_frozen_policy_at_snapshot'
    assert d['q'] == 'uniform_over_honored_actions'


def test_randomized_importance_declares_absolute_D_dependency():
    from research_chains.query_contracts import METHOD_SPECS, LEGACY_METHOD_ALIASES
    spec=METHOD_SPECS['RandomizedActionImportance']
    assert spec.derived_from == 'D_signed_policy_projection'
    assert spec.transform == 'absolute_value'
    assert LEGACY_METHOD_ALIASES['InterventionalATE_vs_noop'] == 'InterventionalResponseATE_vs_noop'


def test_confirmatory_v7_refuses_to_retag_development_cell(tmp_path):
    from scripts import run_h1_fixed_panel_v7 as v7
    run_dir=tmp_path/'runs'/'ep20'/'seed5001'; run_dir.mkdir(parents=True)
    summary={'some_numeric_result':3.25,'v7_development_only':True}
    (run_dir/'tiny_oracle_summary.json').write_text(json.dumps(summary))
    marker={'complete':True,'development_only':True}
    (run_dir/'v7_complete.json').write_text(json.dumps(marker))
    args=SimpleNamespace(evidence_class='CONFIRMATORY_EMPIRICAL',evidence_protocol='h1_fixed_panel_confirmatory_v2')
    assert v7._cell_evidence_matches(run_dir,args) is False
    after=json.loads((run_dir/'tiny_oracle_summary.json').read_text())
    assert after == summary


def test_confirmatory_wrapper_dry_run_passes_explicit_evidence_class(tmp_path,capsys):
    from scripts.run_h1_fixed_panel_confirmatory import main
    out=tmp_path/'confirmatory'
    rc=main(['--seeds',*map(str,range(5001,5011)),'--out-root',str(out),'--dry-run'])
    assert rc == 0
    payload=json.loads(capsys.readouterr().out)
    cmd=payload['command']
    assert '--evidence-class' in cmd
    assert cmd[cmd.index('--evidence-class')+1] == 'CONFIRMATORY_EMPIRICAL'
    assert payload['evidence_class'] == 'CONFIRMATORY_EMPIRICAL'


def test_analyzer_serializes_missing_d6_adversarial_ratio_as_null(tmp_path):
    from scripts.run_d6_extension_lab import run as d6_run
    from scripts.analyze_high_value_extensions import main as analyze_main
    root=tmp_path/'runs'; (root/'d6').mkdir(parents=True)
    payload=d6_run(instances=1,seed=0,sharpness_instances=1,adversarial_instances=0,adversarial_steps=1)
    (root/'d6'/'seed0.json').write_text(json.dumps(payload,allow_nan=False))
    out=tmp_path/'decision.json'
    assert analyze_main(['--root',str(root),'--out',str(out)]) == 0
    matrix=json.loads(out.read_text())
    assert matrix['decisions']['D6']['half_factor_adversarial_best_ratio_to_worst_rhs'] is None
    coverage=matrix['proposal_coverage']
    # Legacy allocation artifacts are migrated to deployable-only headline winners.
    functional=matrix.get('decisions',{}).get('FUNCTIONAL')
    if functional:
        for row in functional.get('matched_budget_winners',{}).values():
            for winners in row.values():
                assert all(w is None or 'oracle' not in w.lower() for w in winners)
    registry=json.loads(
        (Path(__file__).resolve().parents[1] /
         'config/PROPOSAL_EXPERIMENT_REGISTRY.json').read_text()
    )
    assert coverage['registry_proposal_count'] == len(registry['items'])
    assert coverage['covered_by_suite_count'] < coverage['registry_proposal_count']
    assert coverage['all_registry_proposals_covered_by_suite'] is False


def test_p13_compile_ledger_includes_verified_conditional_topk_bridge():
    root=Path(__file__).resolve().parents[1]
    text=(root/'research/p13_redesign/ACTIVE_COMPILE_RESULTS_P13.tsv').read_text()
    assert 'LeanReferenceResponseTopKBudgetConjecture.lean\tLEAN_VERIFIED_QUARANTINED_CONDITIONAL\t0\t0\t0\t0' in text
