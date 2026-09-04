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
