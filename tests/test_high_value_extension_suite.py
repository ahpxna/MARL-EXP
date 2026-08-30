from __future__ import annotations

import json
from pathlib import Path
import numpy as np

from research_chains.experimental_extensions import (
    covariance_design_misranking_search,
    lean_covariance_reversal_witness_diagnostics,
    all_optimal_extension_defect,
    d6_diagnostics,
    reference_uncertainty_diagnostics,
    representation_necessity_diagnostics, box_gamma_lean_witness_diagnostics,
    probability_lift_diagnostics, ru2_factor_two_sharpness_diagnostics, two_world_lower_bound_diagnostics,
)
from research_chains.finite_world import FiniteResponseWorld
from research_chains.reference import ConditionalReferenceKernel
from research_chains.support import SupportModel

ROOT=Path(__file__).resolve().parents[1]

REQUIRED_IDS={
'MASTER.RU1','MASTER.RU2','MASTER.RU3','MASTER.RU4','MASTER.RU5','MASTER.RI1','MASTER.RI2','MASTER.ACTIVE_REF','MASTER.CALIBRATION','MASTER.SUPPORT_UNCERTAINTY','MASTER.CASCADE','MASTER.DYN_SCORE','MASTER.DYN_REFERENCE','MASTER.DYN_SUPPORT','MASTER.EXTERNAL_REFERENCE','MASTER.OP_GAMMA','MASTER.DEFICIT_ZETA_E_LP','MASTER.REFERENCE_FIDELITY',
'FUNCTIONAL.CONFIRMATORY','FUNCTIONAL.COV_FULL','FUNCTIONAL.COV_MISRANK','FUNCTIONAL.CD_CROSSOVER','FUNCTIONAL.GEOMETRY_STRATA','FUNCTIONAL.STOP_C_EXTREMA','FUNCTIONAL.STOP_C_TOPK','FUNCTIONAL.STOP_D_SIGN','FUNCTIONAL.ADAPTIVE_C','FUNCTIONAL.ADAPTIVE_D','FUNCTIONAL.V7_BASELINE',
'D6.S1','D6.S2','D6.S3','D6.Q1','D6.Q2','D6.Q3','D6.Q4','D6.Q5','D6.APPLICABILITY_SYNTH','D6.APPLICABILITY_EXTERNAL','D6.STRESS_HIGHER_ORDER','D6.ANOVA_COMPARE',
'QUERY.QN1','QUERY.QN2','QUERY.QN3','QUERY.QN4','QUERY.TRANSFER_MATRIX','QUERY.NATIVE_ADVANTAGE','QUERY.HIGH_ORDER','QUERY.STALENESS','QUERY.REFERENCE_SHIFT','QUERY.EXTERNAL_TRANSFER','QUERY.PRIMITIVE_WITNESSES',
'STRUCTURAL.APPROX_DEFECT','STRUCTURAL.RUNTIME_COMPLEXITY','STRUCTURAL.NEGATIVE_TAXONOMY','EXTERNAL.CAPABILITY_AUDIT',
'MASTER.RU2_SHARPNESS','MASTER.GAMMA_BOX','MASTER.PROBABILITY_LIFT','QUERY.TWO_WORLD_LOWER_BOUND','STRUCTURAL.SR0_NESTED_EQUIV',
'FUNCTIONAL.ALLOC_UNIFORM','FUNCTIONAL.ALLOC_BEHAVIOR','FUNCTIONAL.ALLOC_UNCERTAINTY','FUNCTIONAL.ALLOC_D_NEYMAN','FUNCTIONAL.ALLOC_D_ORACLE','FUNCTIONAL.ALLOC_C_EXTREMAL','FUNCTIONAL.ALLOC_C_SUCCESSIVE','FUNCTIONAL.ALLOC_C_SPLIT','FUNCTIONAL.ALLOC_C_ORACLE',
'QUERY.DELETION','QUERY.LIMITED_SUPPORT','QUERY.NONLINEAR_NULLSPACE','QUERY.DYNAMIC_INTERACTION','QUERY.OVERLAPPING_GROUPS','QUERY.DRIFT_ERROR','QUERY.DRIFT_RANK',
'MASTER.ACTIVE_REF_UNCERTAINTY_TARGETED','MASTER.CASCADE_FRONTIER','FUNCTIONAL.ALLOC_C_SUCCESSIVE_KNOWN_SIGMA_DIAG','QUERY.ENTANGLED_STRESS','D6.S2_ADVERSARIAL','D6.OMNI_FULL_JOINT',
}

def test_registry_covers_every_proposal_node():
    payload=json.loads((ROOT/'research/high_value_extensions/PROPOSAL_EXPERIMENT_REGISTRY.json').read_text())
    got={item['proposal_id'] for item in payload['items']}
    assert REQUIRED_IDS <= got
    assert payload['paper3_merged_into_master'] is True


def test_reference_uncertainty_bounds_smoke():
    support=SupportModel((2,2),tuple(np.ndindex(2,2)),key='full')
    world=FiniteResponseWorld(support,(np.array([0.,1.]),np.array([-1.,2.])))
    truth=ConditionalReferenceKernel.product((2,2),0,{0:[.5,.5],1:[.25,.75]},key='truth')
    rows={0:{(0,0):.6,(0,1):.4},1:{(1,0):.2,(1,1):.8}}
    est=ConditionalReferenceKernel(0,(2,2),rows,key='est')
    d=reference_uncertainty_diagnostics(world,truth,est)
    assert d['pointwise_violation'] <= 1e-10
    assert d['chi_violation'] <= 1e-10
    assert d['score_interval_violation'] <= 1e-10


def test_d6_applicability_and_current_bounds_smoke():
    support=SupportModel((2,2),tuple(np.ndindex(2,2)),key='full')
    residual={(0,0):0.,(0,1):1.,(1,0):2.,(1,1):-1.}
    world=FiniteResponseWorld(support,(np.zeros(2),np.zeros(2)),residual=residual)
    d=d6_diagnostics(world,{0:[.5,.5],1:[.5,.5]},1)
    assert d['applicable'] is True
    assert d['worst_case_violation'] <= 1e-10
    assert d['decision_violation'] <= 1e-10
    assert d['residual_identity_worst_error'] <= 1e-10
    assert d['qavg_uniform_candidate_violation'] <= 1e-10
    assert d['qsigned_uniform_candidate_violation'] <= 1e-10
    assert d['qavg_distributional_candidate_violation'] <= 1e-10
    partial=FiniteResponseWorld(SupportModel((2,2),((0,0),(0,1),(1,0)),key='partial'),world.primitives,residual=residual)
    assert d6_diagnostics(partial,{0:[.5,.5],1:[.5,.5]},1)['applicable'] is False


def test_covariance_reversal_is_searchable():
    result=covariance_design_misranking_search(instances=10000,seed=4,n=3)
    assert result['found'] is True


def test_exact_lean_covariance_reversal_reproduced():
    result=lean_covariance_reversal_witness_diagnostics()
    assert result['psd'] is True
    assert result['reversal'] is True


def test_representation_necessity_detects_colliding_bad_fiber():
    loss=[[0.,3.],[3.,0.]]; summary=[0,0]
    result=representation_necessity_diagnostics(loss,summary,0.1)
    assert result['common_good_failure_count'] == 1


def test_structural_open_candidate_is_explicitly_measured():
    support=SupportModel((2,2,2),tuple(np.ndindex(2,2,2)),key='full3')
    world=FiniteResponseWorld(support,(np.array([0.,1.]),np.array([0.,2.]),np.array([0.,-1.])))
    result=all_optimal_extension_defect(world)
    assert 'all_optimal_extension_defect' in result
    assert 'candidate_violation' in result
    assert result['candidate_violation'] <= 1e-10


def test_analyzer_never_promotes_from_one_seed(tmp_path):
    from scripts.analyze_high_value_extensions import main as analyze_main
    root=tmp_path/'runs'; (root/'master').mkdir(parents=True)
    payload={
      'reference_uncertainty':{'worst_violation':{'pointwise':0.0,'chi':0.0,'score_interval':0.0}},
      'master_transfer':{'worst_violation':0.0},
      'active_acquisition':{'passive':{'256':{'kernel_tv':{'mean':1.0}}},'targeted':{'256':{'kernel_tv':{'mean':0.5}}}},
      'heldout_calibration':{'targeted':{'256':{'heldout_coverage':0.95}}},
      'cascade':{'safe_rate':1.0,'fallback_rate':0.2},
    }
    (root/'master'/'seed0.json').write_text(json.dumps(payload))
    out=tmp_path/'decision.json'
    assert analyze_main(['--root',str(root),'--out',str(out)]) == 0
    decision=json.loads(out.read_text())['decisions']['MASTER']
    assert decision['status'] == 'CONTINUE_MORE_SEEDS'
    assert decision['promotion_eligible'] is False


def test_new_lab_smokes():
    from scripts.run_master_extension_lab import run as master_run
    from scripts.run_functional_design_extension_lab import run as fd_run
    from scripts.run_functional_stopping_lab import run as fs_run
    from scripts.run_d6_extension_lab import run as d6_run
    from scripts.run_query_extension_lab import run as q_run
    from scripts.run_structural_defect_lab import run as s_run
    from scripts.run_dynamic_extension_lab import run as dyn_run
    m=master_run(3,(8,),0,.05); assert max(m['reference_uncertainty']['worst_violation'].values()) <= 1e-8
    assert fd_run(3,10,0,4)['explicit_covariance_reversal_search']['found'] is True
    fs=fs_run(2,0,4,3,.1,48,4); assert fs['protocol_version']; assert 'C_topk_targeted' in fs['by_allocation']; assert fs['geometry_generator_audit']['max_topk_gap_design_abs_error'] < 1e-10
    from scripts.run_query_optimal_allocation_lab import run as alloc_run
    al=alloc_run(2,(0,),(16,),3,4,1); assert set(('uniform','behavior_freq','uncertainty_only','D_neyman_pilot','D_oracle','C_extremal_confidence','C_successive_elimination','C_successive_known_sigma','C_split_eval','C_oracle')) <= set(al['strategies']); assert 'C_successive_known_sigma' in al['diagnostic_strategies']; assert 'C_successive_elimination' in al['deployable_strategies']
    d=d6_run(3,0,10); assert d['worst_candidate_violations']['worst'] <= 1e-8
    assert q_run(6,0,6,2)['unique_optimum_conflict']['epsilon_0_common_good_failures'] > 0
    assert s_run(4,0)['closed_exact_search']['retry_exact_iff'] is False
    dy=dyn_run(4,0); assert dy['score_drift']['worst_inflated_violation'] <= 1e-8


def test_box_probability_ru2_and_two_world_extensions():
    box=box_gamma_lean_witness_diagnostics(); assert box['lean_witness_reproduced'] is True; assert box['vertex_bound_violation'] <= 1e-12
    ru2=ru2_factor_two_sharpness_diagnostics(); assert ru2['sharpness_reproduced'] is True; assert abs(ru2['equality_residual']) <= 1e-12
    prob=probability_lift_diagnostics(repetitions=1000,seed=7); assert prob['set_inclusion_violation_count'] == 0
    low=two_world_lower_bound_diagnostics(0.,2.,1.); assert abs(low['violation']) <= 1e-12

def test_structural_subset_dp_matches_bruteforce_small_world():
    import itertools
    from research_chains.experimental_extensions import best_nested_prefix_regret
    support=SupportModel((2,2,2,2),tuple(np.ndindex(2,2,2,2)),key='full4')
    world=FiniteResponseWorld(support,(np.array([0.,1.]),np.array([0.,2.]),np.array([0.,-1.]),np.array([0.,3.])))
    got=best_nested_prefix_regret(world)
    opt={k:min(world.additive_radius(S) for S in itertools.combinations(range(4),k)) for k in range(1,5)}
    brute=float('inf')
    for perm in itertools.permutations(range(4)):
        brute=min(brute,max(world.additive_radius(perm[:k])-opt[k] for k in range(1,5)))
    assert abs(got['best_nested_max_regret']-brute) <= 1e-10


def test_high_value_analyzer_fails_closed_on_corrupt_seed_json(tmp_path):
    from scripts import analyze_high_value_extensions as analyzer
    root = tmp_path / 'runs'
    lab = root / 'master'
    lab.mkdir(parents=True)
    (lab / 'seed0.json').write_text('{not-json', encoding='utf-8')
    try:
        analyzer._load(root, 'master')
    except RuntimeError as exc:
        assert 'malformed experiment artifact' in str(exc)
    else:
        raise AssertionError('analyzer must fail closed on corrupt seed artifact')


def test_master_support_uncertainty_stress_is_nonvacuous():
    from scripts.run_master_extension_lab import run
    payload = run(instances=20, budgets=(16,), seed=991)
    support = payload['support_uncertainty']
    assert support['coverage_rate'] == 1.0
    assert support['nonzero_width_fraction'] > 0.9
    assert support['mean_span_interval_width'] > 0.0


def test_master_uncertainty_targeted_and_cascade_frontier():
    from scripts.run_master_extension_lab import run
    payload=run(instances=8,budgets=(16,),seed=123,tolerance=.05)
    assert 'uncertainty_targeted' in payload['active_acquisition']
    assert payload['active_acquisition_semantics']['uncertainty_targeted'].startswith('adaptive posterior')
    frontier=payload['cascade']['frontier']
    assert '0.05' in frontier
    assert frontier['0.05']['false_safe_count'] == 0

def test_functional_deployable_winners_exclude_oracles():
    from scripts.run_query_optimal_allocation_lab import run
    payload=run(instances=4,seeds=(0,),budgets=(16,),R=3,K=4,topk=1)
    assert set(payload['diagnostic_strategies']).isdisjoint(set(payload['endpoint_winners']['16'].values()))
    assert 'C_successive_known_sigma' in payload['diagnostic_strategies']

def test_query_entangled_family_is_reported():
    from scripts.run_query_extension_lab import run
    payload=run(instances=22,seed=2,n_rel=8,k=2)
    assert 'cross_query_entangled' in payload['families']
    assert payload['benchmark_scope'].startswith('synthetic semantic stress test')
    assert 'cross_query_entangled' in payload['native_query_advantage_by_regime']

def test_d6_adversarial_search_is_falsifier_only():
    from research_chains.experimental_extensions import d6_decision_adversarial_search
    out=d6_decision_adversarial_search(instances=5,steps=2,seed=1,m_values=(3,))
    assert out['candidate_ratio_threshold'] == 0.5
    assert 'candidate_killed' in out

def test_omni_full_joint_d6_smoke():
    from scripts.run_omni_d6_full_joint import run
    out=run(seed=3001,m_sources=2,n_states=1,warmup_steps=1)
    assert out['summary']['all_authority_verified'] is True
    assert out['command_support_semantics'].startswith('full Cartesian Omni command support')
