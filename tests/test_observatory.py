"""Contract tests for the observatory.

These check the *measurement apparatus*, not the science: that exact arithmetic
stays exact, that named witnesses still exhibit what they were built to exhibit,
that the schema refuses malformed rows, and that a screened candidate agrees
with its exact recomputation.  A scientific counterexample is never a test
failure here; a silently wrong number is.
"""
from __future__ import annotations

import json
import random
from fractions import Fraction as F
from pathlib import Path

import pytest

from observatory import equations  # noqa: F401
from observatory.exact import (Q, osc, half_osc, gauge_error, extrema_gaps,
                               topk, topk_is_tied, ratio)
from observatory.schema import (Emitter, make_context, registry, ST_OK,
                                ST_SKIPPED, ST_UNDEFINED)
from observatory.worlds import (Support, World, ProductReference, generate_world,
                                FAMILIES, coupled_support_witness,
                                staircase_family, same_summary_pair)
from observatory.chains._common import (exact_optimum, topc_set, deficit_terms,
                                        co_extremizable, all_subsets_modular,
                                        max_of_modular_value)


# ----------------------------------------------------------------- arithmetic

def test_gauge_error_is_shift_invariant():
    q = [F(1), F(3), F(2)]
    assert gauge_error([v + F(7, 3) for v in q], q) == 0


def test_half_osc_is_the_minimax_radius():
    v = [F(1), F(4)]
    r = half_osc(v)
    c = (max(v) + min(v)) / 2
    assert max(abs(x - c) for x in v) == r


def test_extrema_gaps_reports_ties_instead_of_guessing():
    g = extrema_gaps([F(1), F(1), F(0)])
    assert g["unique_max"] is False and g["g_plus"] == 0


def test_ratio_is_undefined_not_infinite():
    assert ratio(F(1), F(0)) is None


# --------------------------------------------------------------------- worlds

def test_world_content_id_is_stable_and_discriminating():
    rng = random.Random(0)
    a = generate_world("cartesian", 3, 2, rng=rng)
    b = generate_world("cartesian", 3, 2, rng=rng)
    assert a.content_id() == a.content_id()
    assert a.content_id() != b.content_id()


@pytest.mark.parametrize("family", FAMILIES)
def test_every_family_builds_and_has_a_finite_radius(family):
    rng = random.Random(11)
    w = generate_world(family, 3, 2, rng=rng)
    r = w.additive_radius((0,))
    assert isinstance(r, F) and r >= 0


def test_delta_square_refuses_non_cartesian_support():
    rng = random.Random(5)
    w = generate_world("strong_coupling", 3, 2, rng=rng)
    if not w.support.is_cartesian:
        with pytest.raises(ValueError):
            w.delta_square()


def test_coupled_support_witness_breaks_the_modular_formula():
    w = coupled_support_witness()
    spans = w.component_spans()
    exact = w.additive_radius(())
    modular = sum(spans) / 2
    assert exact < modular, "the P8/P10 witness must not be modular at S = empty"
    assert not co_extremizable(w)


def test_staircase_layers_have_unique_pairwise_incomparable_optima():
    w = staircase_family(3)
    opt_sets = []
    for k in range(w.m + 1):
        _, opts = exact_optimum(w, k)
        if len(opts) == 1:
            opt_sets.append(frozenset(opts[0]))
    incomparable = sum(
        1 for i in range(len(opt_sets)) for j in range(i + 1, len(opt_sets))
        if not (opt_sets[i] <= opt_sets[j] or opt_sets[j] <= opt_sets[i])
    )
    assert incomparable > 0, "the staircase must force an antichain of optima"


def test_same_summary_twins_share_spans_but_differ_in_truth():
    a, b = same_summary_pair(3, 2)
    assert a.component_spans() == b.component_spans()
    assert a.values_on_support() != b.values_on_support()


# ------------------------------------------------------------------ identities

@pytest.mark.parametrize("family", ["cartesian", "strong_coupling", "cancellation"])
def test_deficit_identity_holds_exactly(family):
    rng = random.Random(3)
    for _ in range(5):
        w = generate_world(family, 4, 2, rng=rng)
        for size in range(1, w.m + 1):
            for T in [tuple(range(size))]:
                t = deficit_terms(w, T)
                assert t["d"] == t["e_plus"] + t["e_minus"]
                assert t["d"] >= 0


def test_max_of_modular_identity():
    rng = random.Random(9)
    w = generate_world("cartesian", 3, 2, rng=rng)
    for S in [(), (0,), (0, 1)]:
        val, _, _ = max_of_modular_value(w, S)
        assert val == 2 * w.additive_radius(S)


def test_co_extremizability_implies_all_subsets_modularity():
    rng = random.Random(17)
    for _ in range(20):
        w = generate_world("weak_coupling", 4, 2, rng=rng)
        if co_extremizable(w):
            holds, gap, _ = all_subsets_modular(w)
            assert holds and gap == 0


# -------------------------------------------------------------------- schema

def test_emitter_rejects_unknown_symbol(tmp_path):
    ctx = make_context("test", 0)
    with Emitter(tmp_path / "x.jsonl", ctx) as em:
        with pytest.raises(ValueError):
            em.emit(chain="SUPPORT", eq_id="SUP.exact_radius",
                    symbol="not_a_declared_symbol", value=F(1))


def test_emitter_rejects_float_in_exact_mode(tmp_path):
    ctx = make_context("test", 0)
    with Emitter(tmp_path / "y.jsonl", ctx) as em:
        with pytest.raises(TypeError):
            em.emit(chain="SUPPORT", eq_id="SUP.exact_radius",
                    symbol="radius", value=0.5)


def test_emitter_round_trips_exact_values(tmp_path):
    p = tmp_path / "z.jsonl"
    ctx = make_context("test", 0)
    with Emitter(p, ctx) as em:
        em.emit(chain="SUPPORT", eq_id="SUP.exact_radius", symbol="radius",
                value=F(1, 3))
    rows = [json.loads(l) for l in p.read_text().splitlines()]
    q = [r for r in rows if r.get("record") == "q"][0]
    assert F(q["exact"]) == F(1, 3)


def test_every_equation_belongs_to_a_known_chain():
    chains = {"MASTER", "FUNCTIONAL", "SUPPORT", "STRUCTURAL", "D6", "QUERY", "CROSS"}
    for eq in registry().values():
        assert eq.chain in chains
        assert len(eq.symbols) == len(set(eq.symbols))


# -------------------------------------------------------------------- screen

def test_screened_candidate_agrees_with_exact_recomputation():
    from observatory.screen import screen_half_factor, to_exact_world
    res = screen_half_factor(120, 3, 2, seed=4, top=3)
    for c in res["candidates"]:
        w = to_exact_world(c, 3, 2)
        d = w.delta_square()
        if d == 0:
            continue
        S = topc_set(w, res["k"])
        L = w.true_compression_loss(S)
        Lo, _ = exact_optimum(w, res["k"], true_loss=True)
        J = (L - Lo) / ((3 - 1) * d)
        assert abs(float(J) - c["J_float"]) < 1e-9


def test_support_partial_test_cover_exact_solver_is_not_artificially_capped():
    from observatory.chains.support import _exact_cover
    cells=[(0,),(1,),(2,),(3,)]
    required=frozenset({('a','b'),('c','d'),('e','f'),('g','h')})
    separates={
        (0,):frozenset({('a','b')}),
        (1,):frozenset({('c','d')}),
        (2,):frozenset({('e','f')}),
        (3,):frozenset({('g','h')}),
    }
    q_star,found=_exact_cover(cells,separates,required,cap=None)
    assert found is True
    assert q_star == 4
    capped,found_capped=_exact_cover(cells,separates,required,cap=3)
    assert capped is None and found_capped is False


def test_master_typed_completion_probe_uses_true_cost_oracle(tmp_path):
    from observatory.chains.master import probe_typed_completion
    from observatory.schema import Emitter,make_context
    p=tmp_path/'typed.jsonl'
    rng=random.Random(20260904)
    with Emitter(p,make_context('typed-test',20260904)) as em:
        for draw in range(30):
            probe_typed_completion(em,{'world_id':f'typed-{draw}','draw':draw},rng,
                                   n_obligations=6,n_evidence=10)
    rows=[json.loads(line) for line in p.read_text().splitlines() if line.strip()]
    qrows=[r for r in rows if r.get('record')=='q' and r.get('eq_id')=='MASTER.typed_completion']
    by={}
    for row in qrows:
        key=row['instance']['world_id']; by.setdefault(key,{})[row['symbol']]=row
    for values in by.values():
        exact=F(values['completion_cost']['exact'])
        greedy=F(values['greedy_cost']['exact'])
        assert greedy >= exact


def test_miner_excludes_exact_affine_aliases_from_novel_inequalities(tmp_path):
    from observatory.mine import _exact_affine_map
    pairs=[(F(0),F(1)),(F(1),F(3)),(F(2),F(5)),(F(3),F(7))]
    assert _exact_affine_map(pairs) == (F(2),F(1))
    assert _exact_affine_map([(F(0),F(0)),(F(1),F(1)),(F(2),F(5))]) is None


# ------------------------------------------------------- D6 loss definition

def test_d6_loss_uses_marginals_not_primitives():
    """Regression: D6 retains a relation via Q_j^q, not via f_j.

    These two objects coincide on additive worlds and diverge on interacting
    ones.  The observatory measured the primitive-based loss for D6 until an
    audit caught it, so the divergence is pinned here rather than left to
    reappear silently.
    """
    import random
    from observatory.worlds import generate_world, ProductReference
    from observatory.chains.d6 import d6_loss, response_spans
    rng = random.Random(11)
    diverged = False
    for _ in range(40):
        w = generate_world("interaction_heavy", 3, 2, rng=rng)
        ref = ProductReference.point_mass(w.support.action_sizes)
        for S in [(0,), (1,), (0, 2)]:
            if d6_loss(w, ref, S) != w.true_compression_loss(S):
                diverged = True
    assert diverged, "the two loss definitions must not be interchangeable"


def test_d6_loss_matches_primitive_loss_on_additive_worlds():
    import random
    from observatory.worlds import generate_world, ProductReference
    from observatory.chains.d6 import d6_loss
    rng = random.Random(5)
    for _ in range(15):
        w = generate_world("cartesian", 3, 2, rng=rng)
        assert w.is_additive()
        ref = ProductReference.point_mass(w.support.action_sizes)
        for S in [(), (0,), (0, 1)]:
            assert d6_loss(w, ref, S) == w.true_compression_loss(S)


def test_ternary_probe_world_is_not_labelled_as_the_falsifier():
    from observatory.worlds import ternary_probe_world
    w = ternary_probe_world()
    assert w.meta["family"] == "ternary_probe"


# -------------------------------------------------------------------------
# dedup.py: semantic deduplication of mined candidate relations
#
# Each test plants a synthetic row set (and, where relevant, a synthetic
# `discover_inequalities`-shaped candidate) whose correct tier is known by
# construction, and asserts dedup.classify_candidate lands it there.  Row
# dicts are built directly in the schema mine.load() would hand back (the
# tests do not go through Emitter/load(), since dedup.py only ever consumes
# that in-memory shape and discover_inequalities() itself is orthogonal to
# what is under test here).
# --------------------------------------------------------------------------

from observatory import dedup as _dedup


def _drow(eq_id, symbol, role, val, world_id, *, k="0", family="famA", **extra_inst):
    """One synthetic measured row in the shape dedup.py / mine.py consume."""
    val = F(val)
    inst = {"world_id": world_id, "k": k, "family": family}
    inst.update(extra_inst)
    return {
        "eq_id": eq_id, "symbol": symbol, "role": role, "mode": "exact",
        "status": "measured", "value": float(val),
        "exact": "%d/%d" % (val.numerator, val.denominator),
        "instance": inst, "tags": [], "note": "",
    }


def _dcand(lhs_col, rhs_col, *, support, tight, distinct_lhs=5, distinct_rhs=5,
          cross_chain=False, cross_equation=True):
    """A discover_inequalities()-shaped candidate dict for the two given columns."""
    return {
        "lhs": lhs_col, "rhs": rhs_col, "support": support, "tight": tight,
        "tight_rate": (tight / support) if support else 0.0,
        "min_slack": 0.0, "max_slack": 5.0,
        "distinct_lhs": distinct_lhs, "distinct_rhs": distinct_rhs,
        "cross_chain": cross_chain, "cross_equation": cross_equation,
    }


def test_dedup_exact_alias_is_classified_alias_even_across_equations():
    """Same numbers under two (equation, symbol) names -> ALIAS, not a discovery."""
    rows = []
    fams = ["famA", "famB", "famC"]
    for i in range(1, 13):
        fam = fams[i % 3]
        rows.append(_drow("TEST.alias_eq_a", "x", "term", i, "w%d" % i, family=fam))
        rows.append(_drow("TEST.alias_eq_b", "y", "term", i, "w%d" % i, family=fam))
    cand = _dcand("TEST.alias_eq_a.x|max", "TEST.alias_eq_b.y|min", support=12, tight=12)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_ALIAS
    assert out["reason"] == "exact_alias"
    assert out["verified_support"] == 12
    assert out["n_families"] == 3


def test_dedup_affine_alias_is_classified_alias_not_novel():
    """y = 2x + 1 exactly, verified on every shared row -> ALIAS (affine, exact)."""
    rows = []
    for i in range(1, 16):
        fam = "famA" if i % 2 == 0 else "famB"
        x = F(i)
        y = 2 * x + 1
        rows.append(_drow("TEST.aff_eq_a", "p", "term", x, "w%d" % i, family=fam))
        rows.append(_drow("TEST.aff_eq_b", "q", "term", y, "w%d" % i, family=fam))
    cand = _dcand("TEST.aff_eq_a.p|max", "TEST.aff_eq_b.q|min", support=15, tight=0)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_ALIAS
    assert out["reason"].startswith("affine_alias")
    assert out["affine_exact"] is True
    assert out["affine_alpha"] == "2"
    assert out["affine_beta"] == "1"


def test_dedup_declared_lhs_rhs_of_same_equation_is_tautology():
    """Comparing an equation's own declared lhs/rhs re-derives the definition."""
    rows = []
    for i in range(1, 16):
        fam = "famA" if i % 2 == 0 else "famB"
        L = F(i)
        R = L + F(i % 3)      # not affine in L, not identical, not always tight
        rows.append(_drow("TEST.decl_ineq", "L", "lhs", L, "w%d" % i, family=fam))
        rows.append(_drow("TEST.decl_ineq", "R", "rhs", R, "w%d" % i, family=fam))
    cand = _dcand("TEST.decl_ineq.L|max", "TEST.decl_ineq.R|min", support=15, tight=5,
                  cross_equation=False)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_TAUTOLOGY
    assert out["reason"] == "declared_lhs_le_rhs(TEST.decl_ineq)"


def test_dedup_difference_equal_to_declared_slack_is_tautology():
    """rhs - lhs literally equals an already-declared slack symbol of the same eq."""
    rows = []
    for i in range(1, 16):
        fam = "famA" if i % 3 else "famB"
        P = F(i)
        gap = F(i % 4)
        Q = P + gap
        rows.append(_drow("TEST.slack_eq", "P", "term", P, "w%d" % i, family=fam))
        rows.append(_drow("TEST.slack_eq", "Q", "term", Q, "w%d" % i, family=fam))
        rows.append(_drow("TEST.slack_eq", "S", "slack", gap, "w%d" % i, family=fam))
    cand = _dcand("TEST.slack_eq.P|max", "TEST.slack_eq.Q|min", support=15, tight=4,
                  cross_equation=False)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_TAUTOLOGY
    assert out["reason"].startswith("diff_equals_slack(TEST.slack_eq.S)")


def test_dedup_ratio_vs_own_numerator_is_tautology():
    """A ratio symbol compared against its own equation's lhs is a restatement."""
    rows = []
    for i in range(1, 16):
        fam = "famA" if i % 2 else "famB"
        num = F(i)
        den = F(i + 3)
        rows.append(_drow("TEST.ratio_eq", "num", "lhs", num, "w%d" % i, family=fam))
        rows.append(_drow("TEST.ratio_eq", "rat", "ratio", num / den, "w%d" % i, family=fam))
    cand = _dcand("TEST.ratio_eq.rat|max", "TEST.ratio_eq.num|min", support=15, tight=3,
                  cross_equation=False)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_TAUTOLOGY
    assert out["reason"].startswith("ratio_vs_own_lhs")


def test_dedup_single_family_relation_is_degenerate():
    """A relation only ever observed on one world family is weak, not a discovery."""
    rows = []
    for i in range(1, 13):
        x = F(i)
        y = x * x + 1          # nonlinear: not affine, not identical
        rows.append(_drow("TEST.deg_eq_a", "x", "term", x, "w%d" % i, family="only_family"))
        rows.append(_drow("TEST.deg_eq_b", "y", "term", y, "w%d" % i, family="only_family"))
    cand = _dcand("TEST.deg_eq_a.x|max", "TEST.deg_eq_b.y|min", support=12, tight=0)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_DEGENERATE
    assert "single_world_family" in out["reason"]


def test_dedup_identically_zero_side_is_degenerate():
    rows = []
    fams = ["famA", "famB", "famC"]
    for i in range(1, 13):
        fam = fams[i % 3]
        rows.append(_drow("TEST.zero_eq_a", "x", "term", 0, "w%d" % i, family=fam))
        rows.append(_drow("TEST.zero_eq_b", "y", "term", i, "w%d" % i, family=fam))
    cand = _dcand("TEST.zero_eq_a.x|max", "TEST.zero_eq_b.y|min", support=12, tight=1)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_DEGENERATE
    assert "lhs_identically_zero" in out["reason"]


def test_dedup_monotone_nonlinear_relation_is_flagged_reparam():
    """y = x**3 is a monotone reparametrization: not affine, not degenerate."""
    rows = []
    fams = ["famA", "famB", "famC", "famD"]
    for i in range(1, 21):
        fam = fams[i % 4]
        x = F(i)
        y = x ** 3
        rows.append(_drow("TEST.mono_eq_a", "x", "term", x, "w%d" % i, family=fam))
        rows.append(_drow("TEST.mono_eq_b", "y", "term", y, "w%d" % i, family=fam))
    cand = _dcand("TEST.mono_eq_a.x|max", "TEST.mono_eq_b.y|min", support=20, tight=0)
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_REPARAM
    assert out["reason"].startswith("monotone_reparam")
    assert abs(out["spearman"]) >= _dedup.REPARAM_RHO


def test_dedup_genuinely_independent_inequality_is_novel_candidate():
    """Two independently-wiggling, non-monotonically-related quantities with x<=y
    everywhere, multiple families, tight on some rows and slack on others: this is
    exactly the shape a real discovery should have, and none of the disqualifying
    checks should fire.  (x, y) pairs and their spearman rho (~0.48, far from the
    +-1 a monotone reparametrization would show) were verified by hand offline.
    """
    xs = [3, 1, 4, 1, 5, 9, 2, 6, 1, 3, 5, 4, 2, 6, 3, 1, 4, 2, 5, 6]
    gaps = [0, 4, 1, 5, 0, 2, 3, 0, 4, 1, 0, 3, 2, 0, 1, 4, 0, 2, 3, 0]
    fams = ["famA", "famB", "famC", "famD"]
    rows = []
    tight_seen = False
    for i, (x, g) in enumerate(zip(xs, gaps)):
        fam = fams[i % 4]
        y = x + g
        if g == 0:
            tight_seen = True
        rows.append(_drow("TEST.novel_eq_a", "x", "term", x, "w%d" % i, family=fam))
        rows.append(_drow("TEST.novel_eq_b", "y", "term", y, "w%d" % i, family=fam))
    assert tight_seen, "test construction bug: fixture must include a tight row"
    cand = _dcand("TEST.novel_eq_a.x|max", "TEST.novel_eq_b.y|min", support=20, tight=7,
                  distinct_lhs=len(set(xs)), distinct_rhs=len(set(x + g for x, g in zip(xs, gaps))))
    idx, role_of = _dedup.build_row_index(rows)
    out = _dedup.classify_candidate(cand, idx, role_of)
    assert out["tier"] == _dedup.TIER_NOVEL
    assert out["n_families"] == 4
    assert len(out["tight_examples"]) >= 1
    assert abs(out["spearman"]) < 0.9


def test_dedup_coarse_join_fallback_recovers_cross_chain_alias_when_instance_shapes_differ():
    """Two chains stamping different EXTRA instance fields for "the same"
    (world_id, k) -- the real pattern behind the STR-vs-SUP DEGENERATE
    false-negatives found on the live store -- make the full-instance-key
    join come up empty even though the two quantities are the same number
    everywhere.  classify_candidate's coarse (world_id, k) fallback must
    still catch it as an ALIAS instead of leaving it DEGENERATE.
    """
    rows = []
    for i in range(1, 16):
        fam = "famA" if i % 2 else "famB"
        v = F(i)
        rows.append(_drow("TEST.chainA_eq", "x", "term", v, "w%d" % i, family=fam,
                           chainA_only_field="present"))
        rows.append(_drow("TEST.chainB_eq", "y", "term", v, "w%d" % i, family=fam,
                           chainB_only_field="also present"))
    cand = _dcand("TEST.chainA_eq.x|max", "TEST.chainB_eq.y|min", support=15, tight=15)
    idx, role_of = _dedup.build_row_index(rows)
    coarse = _dedup.build_coarse_index(rows)

    # sanity: the strict full-instance-key join really does find nothing,
    # exactly as it does on the live store between mismatched chains
    assert len(_dedup._shared(idx, ("TEST.chainA_eq", "x"), ("TEST.chainB_eq", "y"))) == 0

    without_fallback = _dedup.classify_candidate(cand, idx, role_of)
    assert without_fallback["tier"] == _dedup.TIER_DEGENERATE
    assert without_fallback["join"] == "full"

    with_fallback = _dedup.classify_candidate(cand, idx, role_of, coarse=coarse)
    assert with_fallback["tier"] == _dedup.TIER_ALIAS
    assert with_fallback["join"] == "coarse"
    assert with_fallback["verified_support"] == 15


def test_dedup_alias_classes_union_transitively_across_pairs():
    """A~B (exact) and B~C (affine) must merge into one 3-member equivalence class."""
    rows = []
    for i in range(1, 13):
        fam = "famA" if i % 2 else "famB"
        a = F(i)
        b = a                       # A == B exactly
        c = 2 * b + 5               # C affine in B
        rows.append(_drow("TEST.u_eq_a", "a", "term", a, "w%d" % i, family=fam))
        rows.append(_drow("TEST.u_eq_b", "b", "term", b, "w%d" % i, family=fam))
        rows.append(_drow("TEST.u_eq_c", "c", "term", c, "w%d" % i, family=fam))
    cands = [
        _dcand("TEST.u_eq_a.a|max", "TEST.u_eq_b.b|min", support=12, tight=12),
        _dcand("TEST.u_eq_b.b|max", "TEST.u_eq_c.c|min", support=12, tight=0),
    ]
    classified = _dedup.classify_all(rows, cands)
    assert all(c["tier"] == _dedup.TIER_ALIAS for c in classified)
    classes, edges = _dedup.alias_classes(classified)
    assert len(classes) == 1
    assert classes[0]["members"] == ["TEST.u_eq_a.a", "TEST.u_eq_b.b", "TEST.u_eq_c.c"]
    assert len(edges) == 2


def test_dedup_tier_counts_partitions_every_candidate_exactly_once():
    rows = []
    for i in range(1, 13):
        fam = "famA" if i % 2 else "famB"
        rows.append(_drow("TEST.tc_eq_a", "x", "term", i, "w%d" % i, family=fam))
        rows.append(_drow("TEST.tc_eq_b", "y", "term", i, "w%d" % i, family=fam))       # exact alias
        rows.append(_drow("TEST.tc_eq_c", "z", "term", 3 * i + 1, "w%d" % i, family=fam))  # affine alias of x
    cands = [
        _dcand("TEST.tc_eq_a.x|max", "TEST.tc_eq_b.y|min", support=12, tight=12),
        _dcand("TEST.tc_eq_a.x|max", "TEST.tc_eq_c.z|min", support=12, tight=0),
    ]
    classified = _dedup.classify_all(rows, cands)
    counts = _dedup.tier_counts(classified)
    assert sum(counts.values()) == len(cands) == 2
    assert counts[_dedup.TIER_ALIAS] == 2
    for t in _dedup.TIERS:
        assert t in counts


def test_mine_report_no_dedup_flag_preserves_legacy_candidate_file(tmp_path):
    """report(use_dedup=False) must not write the new classification artefacts,
    and must keep feeding mined_invariants.jsonl from the raw candidate list --
    i.e. the pre-dedup.py pipeline stays reachable behind the flag."""
    from observatory.mine import report
    from observatory.schema import Emitter, make_context
    ctx = make_context("dedup-cli-test", 0)
    p = tmp_path / "src.jsonl"
    with Emitter(p, ctx) as em:
        for i in range(1, 16):
            em.emit(chain="SUPPORT", eq_id="SUP.exact_radius", symbol="radius",
                    value=F(i), role="lhs",
                    instance={"world_id": "w%d" % i, "k": "0", "family": "famA"})
            em.emit(chain="SUPPORT", eq_id="SUP.support_brackets", symbol="r_upper",
                    value=F(i) + F(i % 3), role="term",
                    instance={"world_id": "w%d" % i, "k": "0", "family": "famA"})
    out_raw = tmp_path / "out_raw"
    report([p], out_raw, use_dedup=False)
    assert (out_raw / "candidate_inequalities.json").exists()
    assert not (out_raw / "candidate_inequalities_classified.json").exists()
    assert not (out_raw / "alias_classes.json").exists()

    out_dd = tmp_path / "out_dedup"
    s = report([p], out_dd, use_dedup=True)
    assert (out_dd / "candidate_inequalities.json").exists()
    assert "dedup_tier_counts" in s
