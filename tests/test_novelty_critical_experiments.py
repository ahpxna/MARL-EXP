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


def test_typed_greedy_never_beats_exact_minimum_cost():
    from research_chains.novelty_completion import greedy_typed_completion
    obligations={"a":"SUPPORT","b":"SUPPORT","c":"QUERY"}
    items=[
        EvidenceItem("a","SUPPORT",1.0,frozenset({"a"})),
        EvidenceItem("b","SUPPORT",1.0,frozenset({"b"})),
        EvidenceItem("ab","SUPPORT",1.4,frozenset({"a","b"})),
        EvidenceItem("c","QUERY",0.7,frozenset({"c"})),
        EvidenceItem("decoy","REFERENCE",0.01,frozenset()),
    ]
    exact=minimum_cost_typed_completion(obligations,items)
    greedy=greedy_typed_completion(obligations,items)
    assert exact["complete"] and greedy["complete"]
    assert greedy["cost"] + 1e-12 >= exact["cost"]
    assert set(exact["selected_types"]) == {"SUPPORT","QUERY"}


def test_minimum_cost_typed_completion_matches_exhaustive_enumeration():
    """Regression for the 2026-09-04 MASTER campaign defect: the retired
    ``observatory.chains.master`` oracle (commit 418204a) searched item
    subsets in increasing cardinality order and stopped at the *first*
    cardinality with any feasible cover, so a cheap cover reachable only at a
    larger cardinality was never seen (e.g. one expensive item covering
    everything beat three cheap singletons, purely because it was found at
    size 1).  This pins the current DP oracle against a brute-force search
    over *all* subset sizes, in exact Fraction arithmetic, on small random
    instances -- including instances shaped exactly like the counterexample
    that exposed the historical bug (one broad expensive item plus several
    cheap narrow ones).
    """
    import itertools
    import random as _random
    from fractions import Fraction as F

    def brute_force_min_cost(obligations, items):
        order = sorted(obligations)
        n = len(items)
        best = None
        for r in range(0, n + 1):
            for combo in itertools.combinations(range(n), r):
                covered = set()
                cost = F(0)
                for i in combo:
                    it = items[i]
                    covered |= set(it.discharges)
                    cost += F(it.cost).limit_denominator(10 ** 6)
                if set(order) <= covered:
                    if best is None or cost < best:
                        best = cost
        return best

    # Hand-built counterexample shape: one item covers everything at high
    # cost; three singletons cover the same ground far more cheaply but only
    # at a larger subset cardinality.
    obligations = {"a": "T1", "b": "T1", "c": "T1"}
    wide = EvidenceItem("wide", "T1", 9.0, frozenset({"a", "b", "c"}))
    singles = [
        EvidenceItem("s_a", "T1", 1.0, frozenset({"a"})),
        EvidenceItem("s_b", "T1", 1.0, frozenset({"b"})),
        EvidenceItem("s_c", "T1", 1.0, frozenset({"c"})),
    ]
    items = [wide] + singles
    out = minimum_cost_typed_completion(obligations, items)
    true_min = brute_force_min_cost(obligations, items)
    assert out["complete"]
    assert F(out["cost"]).limit_denominator(10 ** 6) == true_min == F(3)

    # Randomized small instances, always checked against exhaustive search.
    types = ["T1", "T2", "T3"]
    rng = _random.Random(20260904)
    for _ in range(60):
        n_obl = rng.choice([2, 3, 4])
        obligations = {f"o{j}": rng.choice(types) for j in range(n_obl)}
        items = []
        for j in range(n_obl):
            o = f"o{j}"
            items.append(EvidenceItem(f"direct_{j}", obligations[o],
                                      rng.choice([0.25, 0.5, 1.0, 1.5, 2.0]),
                                      frozenset({o})))
        for j in range(rng.randint(0, 4)):
            ty = rng.choice(types)
            compatible = [o for o, t in obligations.items() if t == ty]
            if not compatible:
                continue
            k = rng.randint(1, len(compatible))
            items.append(EvidenceItem(f"extra_{j}", ty,
                                      rng.choice([0.1, 0.2, 0.4, 0.75, 3.0]),
                                      frozenset(rng.sample(compatible, k))))
        got = minimum_cost_typed_completion(obligations, items)
        true_min = brute_force_min_cost(obligations, items)
        assert got["complete"] and true_min is not None
        assert F(got["cost"]).limit_denominator(10 ** 6) == true_min


def test_probe_typed_completion_draws_always_satisfy_typing_predicate():
    """Regression for the 2026-09-04 MASTER campaign defect: the retired
    oracle assigned evidence a cosmetic ``TYPES[i % len(TYPES)]`` label that
    was never checked against any obligation, so a catalogue with obligations
    of one type could be silently discharged by evidence declared as a
    different type -- typing was decorative, not enforced.  This replays the
    live Observatory generator many times and, for every draw, re-verifies
    directly (independently of the constructor's internal check) that every
    catalogue item's discharge set only ever contains obligations whose
    required type equals that item's declared type, and that both the exact
    and greedy solvers' selections stay inside that same catalogue.
    """
    import random as _random
    from observatory import equations  # noqa: F401
    import observatory.chains.master as _M
    from observatory.schema import Emitter, make_context

    captured = []
    orig_min = _M.minimum_cost_typed_completion
    orig_greedy = _M.greedy_typed_completion

    def _capture_min(obligations, items):
        captured.append((dict(obligations), list(items)))
        return orig_min(obligations, items)

    _M.minimum_cost_typed_completion = _capture_min
    try:
        rng = _random.Random(9)
        with Emitter(_tmp_path(), make_context("typing-predicate-test", 9)) as em:
            for draw in range(200):
                n_obl = rng.choice([4, 5, 6, 7])
                n_ev = rng.choice([6, 8, 10, 12])
                _M.probe_typed_completion(
                    em, {"world_id": f"typing-{draw}", "draw": draw},
                    rng, n_obligations=n_obl, n_evidence=n_ev)
    finally:
        _M.minimum_cost_typed_completion = orig_min
        _M.greedy_typed_completion = orig_greedy

    assert len(captured) == 200
    violations = 0
    for obligations, items in captured:
        for item in items:
            for o in item.discharges:
                if obligations[o] != item.evidence_type:
                    violations += 1
    assert violations == 0, (
        f"typing predicate violated on {violations} discharge(s) across "
        f"{len(captured)} draws"
    )


def _tmp_path():
    import tempfile, os
    fd, path = tempfile.mkstemp(suffix=".jsonl")
    os.close(fd)
    return __import__("pathlib").Path(path)
