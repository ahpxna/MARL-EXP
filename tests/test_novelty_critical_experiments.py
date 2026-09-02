from __future__ import annotations

import numpy as np

from research_chains.novelty_completion import (
    EvidenceItem, minimum_cost_typed_completion, selective_refresh_solution,
    prefix_cover_dimension, robust_linear_certificate_bound,
)
from research_chains.finite_world import FiniteResponseWorld
from research_chains.support import SupportModel


def test_typed_completion_rejects_wrong_type_discharge():
    obligations={"o":"SUPPORT"}
    try:
        minimum_cost_typed_completion(obligations,[EvidenceItem("bad","RESPONSE",.1,frozenset({"o"}))])
    except ValueError as exc:
        assert "typed discharge violation" in str(exc)
    else:
        raise AssertionError("wrong evidence type must fail closed")


def test_typed_completion_uses_cheaper_same_type_bundle():
    obligations={"a":"SUPPORT","b":"SUPPORT"}
    items=[EvidenceItem("a","SUPPORT",1.,frozenset({"a"})),EvidenceItem("b","SUPPORT",1.,frozenset({"b"})),EvidenceItem("bundle","SUPPORT",1.2,frozenset({"a","b"}))]
    out=minimum_cost_typed_completion(obligations,items)
    assert out["complete"] and out["selected"]==["bundle"]


def test_selective_refresh_can_be_strictly_cheaper_than_full_refresh():
    out=selective_refresh_solution([2.9,1.9,0.0],[3.1,2.1,.2],[0.7,.1,.1],[5.,1.,1.],1)
    assert out["safe"] is True
    assert out["refresh_cost"] <= out["full_refresh_cost"]


def test_prefix_cover_dimension_is_one_on_full_additive_product_world():
    support=SupportModel((2,2,2),tuple(np.ndindex(2,2,2)),key="full")
    world=FiniteResponseWorld(support,(np.array([0.,3.]),np.array([0.,2.]),np.array([0.,1.])))
    out=prefix_cover_dimension(world,0.0)
    assert out["dimension"] == 1


def test_robust_linear_certificate_refines_down_to_exact_bound():
    alpha=np.array([1.,-.5]); values=np.array([2.,1.])
    wide=robust_linear_certificate_bound(alpha,values-.5,values+.5)
    exact=robust_linear_certificate_bound(alpha,values,values)
    assert exact <= wide


def test_new_runner_smokes():
    from scripts.run_typed_certificate_completion_lab import run as tcc
    from scripts.run_functional_selective_maintenance_lab import run as maint
    from scripts.run_support_critical_identification_lab import run as supp
    from scripts.run_structural_prefix_cover_lab import run as struct
    from scripts.run_d6_cost_aware_paec_lab import run as d6
    from scripts.run_query_identifiability_lab import run as query
    assert tcc(8,1)["typed_decoys_never_used_by_construction"] is True
    m=maint(30,1,5,2); assert m["false_safe_count"] == 0
    assert 0.0 < m["mean_refresh_fraction_vs_full"] < 1.0
    assert m["by_gap_regime"]["small"]["median_refresh_count"] >= 1.0
    assert m["by_gap_regime"]["large"]["median_refresh_count"] == 0.0
    assert supp(4,1,3,1,.1)["false_safe_count"] == 0
    assert struct(8,1,(3,4),0.0)["max_dimension_found"] >= 1
    d=d6(8,1); assert d["EveryTopCPairHasPAEC_assumed"] is False
    assert d["all_synthetic_certificate_families_sound"] is True
    assert d["all_completion_targets_reached"] is True
    assert d["signed_coefficient_cases_present"] is True
    assert d["b7_exact_reproduction"]["same_first_order"] is True
    assert d["b7_exact_reproduction"]["full_singleton_optima_disjoint"] is True
    q=query(20,1); assert 0.0 <= q["insufficient_fraction"] <= 1.0


def test_variance_analysis_does_not_call_first_variant_winner_when_all_medians_censored():
    from scripts.analyze_functional_variance_stopping import analyze
    payload={
        "protocol_version":"functional_variance_stopping_v1",
        "max_n":100,
        "deployable_variants":["uniform","adaptive"],
        "diagnostic_variants":["C_known_sigma"],
        "by_variant":{
            "uniform":{"median_N_certificate":101.,"certificate_fraction":0.,"false_safe_count":0,"mean_final_capacity_interval_width":9.},
            "adaptive":{"median_N_certificate":101.,"certificate_fraction":.4,"false_safe_count":0,"mean_final_capacity_interval_width":1.},
            "C_known_sigma":{"median_N_certificate":50.,"certificate_fraction":.9,"false_safe_count":0,"mean_final_capacity_interval_width":.1},
        },
    }
    out=analyze(payload)
    assert out["deployable_winner"] is None
    assert out["deployable_winner_status"] == "NO_MEDIAN_IDENTIFIED_CENSORING"
    assert out["deployable_secondary_order"][0] == "adaptive"
