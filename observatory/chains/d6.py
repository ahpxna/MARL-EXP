"""D6 chain probe: product-reference surrogate, the sharp world-approximation
constant, the decision transfer, the half-factor ratio, the decision-interaction
constant after the m-1 falsification, and the centered interaction profile.
"""
from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from ..exact import Q, ZERO, ONE, HALF, osc, half_osc, ratio, topk, argsort_desc
from ..schema import (Emitter, MODE_EXACT, MODE_FLOAT, ROLE_INPUT, ROLE_TERM,
                      ROLE_LHS, ROLE_RHS, ROLE_SLACK, ROLE_RATIO, ROLE_FLAG,
                      ROLE_DIAG, ST_OK, ST_UNDEFINED, ST_SKIPPED, ST_BLOCKED)
from ..worlds import Support, World, ProductReference, Action
from ._common import exact_optimum, topc_set, world_key

CHAIN = "D6"


def marginal_response(world: World, ref: ProductReference, j: int, aj: int) -> Q:
    """Q_j^q(a_j) = E_{a_{-j} ~ q_{-j}} F(a_j, a_{-j})."""
    total = ZERO
    sizes = world.support.action_sizes
    others = [range(sizes[i]) for i in range(world.m) if i != int(j)]
    for rest in itertools.product(*others):
        a = []
        it = iter(rest)
        for i in range(world.m):
            a.append(int(aj) if i == int(j) else next(it))
        a = tuple(a)
        w = ONE
        for i in range(world.m):
            if i != int(j):
                w *= ref.weights[i][a[i]]
        if w != 0:
            total += w * world.value(a)
    return total


def reference_mean(world: World, ref: ProductReference) -> Q:
    return sum(ref.prob(a) * world.value(a) for a in world.support.omega)


# ---------------------------------------------------------------- D6 loss
#
# CORRECTION (audit): D6 retains a relation through its *product-reference
# marginal* Q_j^q, not through the additive primitive f_j.  On an interacting
# world the two differ -- measured disagreement on 327 of 720 (S, reference)
# cases, worst |7/4 - 23/8| = 9/8 -- so the primitive-based compression loss
# used by the Support chain is simply a different object here.  Every D6
# quantity below is therefore computed from the marginals.

def response_marginals(world: World, ref: ProductReference):
    """Q_j^q(a_j) for every relation and action."""
    return tuple(
        tuple(marginal_response(world, ref, j, a)
              for a in range(world.support.action_sizes[j]))
        for j in range(world.m)
    )


def response_spans(world: World, ref: ProductReference, marg=None):
    """C_j = osc_a Q_j^q(a).  This -- not osc f_j -- is what Top-C ranks."""
    marg = marg if marg is not None else response_marginals(world, ref)
    return tuple(osc(list(mj)) for mj in marg)


def d6_loss(world: World, ref: ProductReference, S, marg=None) -> Q:
    """L_F(S) = (1/2) osc_a [ F(a) - sum_{j in S} Q_j^q(a_j) ]."""
    marg = marg if marg is not None else response_marginals(world, ref)
    keep = set(int(j) for j in S)
    vals = [world.value(a) - sum(marg[j][a[j]] for j in keep)
            for a in world.support.omega]
    return HALF * osc(vals)


def d6_optimum(world: World, ref: ProductReference, k: int, marg=None):
    """Exact minimum D6 loss at budget k, with every optimal retained set."""
    marg = marg if marg is not None else response_marginals(world, ref)
    best = None
    opts = []
    for S in itertools.combinations(range(world.m), int(k)):
        v = d6_loss(world, ref, S, marg)
        if best is None or v < best:
            best, opts = v, [S]
        elif v == best:
            opts.append(S)
    return best, tuple(opts)


def d6_topc(world: World, ref: ProductReference, k: int, marg=None):
    marg = marg if marg is not None else response_marginals(world, ref)
    return topk(response_spans(world, ref, marg), int(k))


def surrogate(world: World, ref: ProductReference):
    b = reference_mean(world, ref)
    m = world.m
    marg = tuple(
        tuple(marginal_response(world, ref, j, aj)
              for aj in range(world.support.action_sizes[j]))
        for j in range(m)
    )
    def A(a: Action) -> Q:
        return sum(marg[j][a[j]] for j in range(m)) - Q(m - 1) * b
    return A, b, marg


def probe_applicability(em: Emitter, world: World, ref: ProductReference, key: Dict) -> bool:
    """D6.applicability_gate -- fail closed rather than normalizing the input."""
    e = "D6.applicability_gate"
    inst = dict(key)
    cart = world.support.is_cartesian
    nonneg = all(all(x >= 0 for x in row) for row in ref.weights)
    normed = all(sum(row) == ONE for row in ref.weights)
    missing = world.support.n_full - len(world.support.omega)
    applicable = bool(cart and nonneg and normed)
    em.emit(chain=CHAIN, eq_id=e, symbol="cartesian_support", value=1 if cart else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="weights_nonnegative", value=1 if nonneg else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="weights_normalized", value=1 if normed else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="reference_conditional", value=0,
            role=ROLE_FLAG, instance=inst, note="product reference by construction")
    em.emit(chain=CHAIN, eq_id=e, symbol="missing_cells", value=missing,
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="applicable", value=1 if applicable else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="would_have_been_silently_normalized",
            value=1 if (nonneg and not normed) else 0, role=ROLE_FLAG, instance=inst,
            note="the exact defect the source audit found in the old runtime")
    return applicable


def probe_surrogate_and_bounds(em: Emitter, world: World, ref: ProductReference,
                               k: int, key: Dict) -> None:
    A, b, marg = surrogate(world, ref)
    m = world.m
    omega = world.support.omega
    delta = world.delta_square()
    diffs = [world.value(a) - A(a) for a in omega]
    sup_err = max(abs(d) for d in diffs)
    inst = dict(key, k=k, reference="pm" if ref.is_point_mass() else "mixed")

    e = "D6.additive_surrogate"
    Avals = [A(a) for a in omega]
    em.emit(chain=CHAIN, eq_id=e, symbol="b", value=b, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="A_min", value=min(Avals), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="A_max", value=max(Avals), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="surrogate_span", value=osc(Avals), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="max_abs_A", value=max(abs(v) for v in Avals),
            role=ROLE_DIAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="is_exactly_additive",
            value=1 if world.is_additive() else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="recovers_F_when_additive",
            value=1 if (not world.is_additive() or sup_err == 0) else 0,
            role=ROLE_FLAG, instance=inst)

    e = "D6.world_approximation"
    bound = Q(m - 1) * delta
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_square", value=delta, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
    em.emit_inequality(chain=CHAIN, eq_id=e, lhs=sup_err, rhs=bound,
                       lhs_symbol="sup_error", rhs_symbol="bound",
                       slack_symbol="slack", ratio_symbol="ratio",
                       holds_symbol="holds", instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="is_sharp", value=1 if sup_err == bound else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="argmax_action", value=0, role=ROLE_DIAG,
            instance=inst, note=str(omega[max(range(len(diffs)), key=lambda i: abs(diffs[i]))]))

    # -- decision transfer and the half factor -------------------------
    marg = response_marginals(world, ref)
    S = d6_topc(world, ref, k, marg)
    L_sel = d6_loss(world, ref, S, marg)
    L_opt, _ = d6_optimum(world, ref, k, marg)
    regret = L_sel - L_opt
    e = "D6.decision_transfer"
    em.emit(chain=CHAIN, eq_id=e, symbol="loss_selected", value=L_sel, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="loss_optimal", value=L_opt, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_square", value=delta, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
    em.emit_inequality(chain=CHAIN, eq_id=e, lhs=regret, rhs=2 * Q(m - 1) * delta,
                       lhs_symbol="decision_regret", rhs_symbol="bound",
                       slack_symbol="slack", ratio_symbol="ratio",
                       holds_symbol="holds", instance=inst)

    e = "D6.half_factor"
    den = Q(m - 1) * delta
    J = ratio(regret, den)
    em.emit(chain=CHAIN, eq_id=e, symbol="numerator", value=regret, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="denominator", value=den, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="J", value=J, role=ROLE_LHS,
            status=ST_OK if J is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="threshold", value=HALF, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="holds",
            value=(1 if (J is not None and J <= HALF) else (None if J is None else 0)),
            role=ROLE_FLAG, status=ST_OK if J is not None else ST_UNDEFINED,
            instance=inst,
            note="" if J is not None else "delta_square = 0: an additive world says nothing here")
    em.emit(chain=CHAIN, eq_id=e, symbol="margin",
            value=(HALF - J) if J is not None else None, role=ROLE_SLACK,
            status=ST_OK if J is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="killed",
            value=(1 if (J is not None and J > HALF) else (None if J is None else 0)),
            role=ROLE_FLAG, status=ST_OK if J is not None else ST_UNDEFINED, instance=inst,
            note="an exact rational J > 1/2 kills the conjecture outright")
    em.emit(chain=CHAIN, eq_id=e, symbol="best_seen", value=J, role=ROLE_DIAG,
            status=ST_OK if J is not None else ST_UNDEFINED, instance=inst,
            note="running maximum is taken in analysis, not at write time")
    em.emit(chain=CHAIN, eq_id=e, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="arity", value=max(world.support.action_sizes),
            role=ROLE_INPUT, instance=inst)


def probe_kappa_di(em: Emitter, world: World, ref: ProductReference, k: int,
                   key: Dict) -> None:
    """D6.decision_interaction_complexity and D6.symmetric_difference.

    ``S`` is a Top-k selected set and ``T`` ranges over equal-cardinality
    competitors, with the balanced complement flagged.  The doubled decision gap
    is compared against ``m-1`` -- the law falsified on 4 September -- and the
    single gap against the NEW-1 symmetric-difference bound.
    """
    m = world.m
    delta = world.delta_square()
    if delta == 0:
        return
    marg = response_marginals(world, ref)
    C = response_spans(world, ref, marg)
    S = topk(C, k)
    tied = _is_tied_topk(C, k)
    e_k = "D6.decision_interaction_complexity"
    e_n = "D6.symmetric_difference"
    for T in itertools.combinations(range(m), k):
        if T == S:
            continue
        L_S = d6_loss(world, ref, S, marg)
        L_T = d6_loss(world, ref, T, marg)
        D_ST = L_S - L_T
        l_C = 2 * D_ST
        symdiff = len(set(S) - set(T))
        balanced = (2 * k == m) and (set(T) == set(range(m)) - set(S))
        inst = dict(key, k=k, selected=str(S), competitor=str(T),
                    reference="pm" if ref.is_point_mass() else "mixed")

        em.emit(chain=CHAIN, eq_id=e_k, symbol="l_C", value=l_C, role=ROLE_LHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="kappa_observed", value=l_C / delta,
                role=ROLE_TERM, instance=inst,
                note="normalized by delta_square so worlds are comparable")
        em.emit(chain=CHAIN, eq_id=e_k, symbol="m_minus_1", value=Q(m - 1), role=ROLE_RHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="exceeds_m_minus_1",
                value=1 if l_C / delta > Q(m - 1) else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="slack", value=Q(m - 1) - l_C / delta,
                role=ROLE_SLACK, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="ratio", value=(l_C / delta) / Q(m - 1),
                role=ROLE_RATIO, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="normalized",
                value=1 if all(sum(r) == ONE for r in ref.weights) else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="balanced", value=1 if balanced else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="strict_topc", value=0 if tied else 1,
                role=ROLE_FLAG, instance=inst,
                note="the first ternary falsifier was tied; the strict version still fails")
        em.emit(chain=CHAIN, eq_id=e_k, symbol="arity", value=max(world.support.action_sizes),
                role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="reference_is_point_mass",
                value=1 if ref.is_point_mass() else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_k, symbol="reference_mass_check",
                value=sum(sum(r) for r in ref.weights) / Q(m), role=ROLE_DIAG, instance=inst)

        em.emit(chain=CHAIN, eq_id=e_n, symbol="D_ST", value=D_ST, role=ROLE_LHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="sym_diff_size", value=symdiff, role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="delta_square", value=delta, role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="bound", value=Q(symdiff) * delta, role=ROLE_RHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="slack", value=Q(symdiff) * delta - D_ST,
                role=ROLE_SLACK, instance=inst)
        rr = ratio(D_ST, Q(symdiff) * delta)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="ratio", value=rr, role=ROLE_RATIO,
                status=ST_OK if rr is not None else ST_UNDEFINED, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="holds",
                value=1 if D_ST <= Q(symdiff) * delta else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="is_balanced_complement",
                value=1 if balanced else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_n, symbol="k", value=k, role=ROLE_INPUT, instance=inst)


def _is_tied_topk(values, k) -> bool:
    order = argsort_desc(values)
    return bool(k < len(values) and values[order[k - 1]] == values[order[k]])


# --------------------------------------------------- centered interaction profile

def centered_profile(world: World, ref: ProductReference, i: int, u: int, u0: int,
                     context: Action) -> Q:
    """psi_{i,u}^{u0}(z) = [F(z_{i<-u}) - F(z_{i<-u0})] - [Q_i^q(u) - Q_i^q(u0)]."""
    zu = list(context); zu[int(i)] = int(u); zu = tuple(zu)
    z0 = list(context); z0[int(i)] = int(u0); z0 = tuple(z0)
    first = world.value(zu) - world.value(z0)
    second = (marginal_response(world, ref, i, u)
              - marginal_response(world, ref, i, u0))
    return first - second


def raw_profile(world: World, i: int, u: int, u0: int, context: Action) -> Q:
    """rho_{i,u}^{u0}(z) = F(z_{i<-u}) - F(z_{i<-u0}), the UNCENTRED contrast.

    Same data as `centered_profile`, minus the first-order subtraction.  That
    subtraction is a projection: it is exactly the additive layer in which every
    recorded D6 counterexample lives, so measuring rank on the centred profile
    alone cannot see the mechanism.
    """
    zu = list(context); zu[int(i)] = int(u); zu = tuple(zu)
    z0 = list(context); z0[int(i)] = int(u0); z0 = tuple(z0)
    return world.value(zu) - world.value(z0)


def probe_profile_rank(em: Emitter, world: World, ref: ProductReference, key: Dict,
                       *, max_contexts: int = 8) -> None:
    """D6.centered_interaction_profile and D6.rank_one_geometry.

    The rank-one predicate is the current live conjecture's hypothesis, so every
    2x2 minor is measured rather than summarized: the largest absolute minor per
    coordinate is what a falsification search must drive away from zero.
    """
    m = world.m
    sizes = world.support.action_sizes
    e_p = "D6.centered_interaction_profile"
    e_r = "D6.rank_one_geometry"
    e_w = "D6.raw_contrast_rank_one"
    all_rank_one = True
    all_raw_rank_one = True
    n_misaligned = 0
    for i in range(m):
        n_i = sizes[i]
        if n_i < 2:
            continue
        u0 = 0
        contexts = [a for a in world.support.omega][:max_contexts]
        prof = {}
        for u in range(n_i):
            prof[u] = [centered_profile(world, ref, i, u, u0, z) for z in contexts]
        vals = [v for u in prof for v in prof[u]]
        inst = dict(key, coordinate=i, anchor=u0)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="coordinate", value=i, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="anchor", value=u0, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="anchor_is_zero",
                value=1 if all(v == 0 for v in prof[u0]) else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="gauge_invariant", value=1, role=ROLE_FLAG,
                instance=inst, note="coordinate-additive terms cancel by construction")
        em.emit(chain=CHAIN, eq_id=e_p, symbol="profile_max", value=max(vals), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="profile_min", value=min(vals), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="profile_span", value=osc(vals), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="n_contexts", value=len(contexts),
                role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_p, symbol="n_actions", value=n_i, role=ROLE_INPUT, instance=inst)

        worst = ZERO
        wu = wv = -1
        for u, v in itertools.combinations(range(n_i), 2):
            for x in range(len(contexts)):
                for y in range(x + 1, len(contexts)):
                    minor = prof[u][x] * prof[v][y] - prof[u][y] * prof[v][x]
                    if abs(minor) > worst:
                        worst, wu, wv = abs(minor), u, v
        rank_one = worst == 0
        all_rank_one = all_rank_one and rank_one
        levels = len({tuple(prof[u]) for u in range(n_i)})
        em.emit(chain=CHAIN, eq_id=e_r, symbol="coordinate", value=i, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="max_abs_minor", value=worst, role=ROLE_LHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="is_rank_one", value=1 if rank_one else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="n_profile_levels", value=levels,
                role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="contrast_spectrum_size", value=levels,
                role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="two_profile", value=1 if levels <= 2 else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="binary_alphabet", value=1 if n_i == 2 else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="witness_minor_u", value=wu, role=ROLE_DIAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_r, symbol="witness_minor_v", value=wv, role=ROLE_DIAG, instance=inst)

        # ---- raw (uncentred) rank, over the same contexts and the same anchor
        rawp = {u: [raw_profile(world, i, u, u0, z) for z in contexts]
                for u in range(n_i)}
        raw_worst = ZERO
        rwu = rwv = -1
        for u, v in itertools.combinations(range(n_i), 2):
            for x in range(len(contexts)):
                for y in range(x + 1, len(contexts)):
                    minor = rawp[u][x] * rawp[v][y] - rawp[u][y] * rawp[v][x]
                    if abs(minor) > raw_worst:
                        raw_worst, rwu, rwv = abs(minor), u, v
        raw_rank_one = raw_worst == 0
        all_raw_rank_one = all_raw_rank_one and raw_rank_one
        misaligned = rank_one and not raw_rank_one
        if misaligned:
            n_misaligned += 1
        em.emit(chain=CHAIN, eq_id=e_w, symbol="coordinate", value=i,
                role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_w, symbol="raw_max_abs_minor", value=raw_worst,
                role=ROLE_LHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_w, symbol="raw_is_rank_one",
                value=1 if raw_rank_one else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_w, symbol="raw_rank_exceeds_one",
                value=0 if raw_rank_one else 1, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_w, symbol="centred_is_rank_one",
                value=1 if rank_one else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_w, symbol="misaligned",
                value=1 if misaligned else 0, role=ROLE_FLAG, instance=inst,
                note="centred rank one but raw rank > 1: invisible to D6")
        em.emit(chain=CHAIN, eq_id=e_w, symbol="n_raw_profile_levels",
                value=len({tuple(rawp[u]) for u in range(n_i)}),
                role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_w, symbol="binary_alphabet",
                value=1 if n_i == 2 else 0, role=ROLE_FLAG, instance=inst,
                note="a two-letter alphabet forces raw rank one unconditionally")
        em.emit(chain=CHAIN, eq_id=e_w, symbol="raw_witness_minor_u", value=rwu,
                role=ROLE_DIAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e_w, symbol="raw_witness_minor_v", value=rwv,
                role=ROLE_DIAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e_r, symbol="all_coordinates_rank_one",
            value=1 if all_rank_one else 0, role=ROLE_FLAG, instance=dict(key))
    em.emit(chain=CHAIN, eq_id=e_w, symbol="all_coordinates_raw_rank_one",
            value=1 if all_raw_rank_one else 0, role=ROLE_FLAG, instance=dict(key))
    em.emit(chain=CHAIN, eq_id=e_w, symbol="n_misaligned_coordinates",
            value=n_misaligned, role=ROLE_TERM, instance=dict(key),
            note="count of coordinates D6's centred hypothesis cannot see")


def run(em: Emitter, world: World, *, budgets: Sequence[int], rng,
        references: Sequence[Tuple[str, ProductReference]] = ()) -> None:
    key = world_key(world)
    sizes = world.support.action_sizes
    refs = list(references) or [
        ("point_mass", ProductReference.point_mass(sizes)),
        ("uniform", ProductReference.uniform(sizes)),
        ("skewed", ProductReference.skewed(sizes)),
    ]
    for name, ref in refs:
        k2 = dict(key, ref_name=name)
        if not probe_applicability(em, world, ref, k2):
            em.emit(chain=CHAIN, eq_id="D6.world_approximation", symbol="sup_error",
                    value=None, role=ROLE_LHS, status=ST_BLOCKED, instance=dict(k2),
                    note="D6 assumptions not met; refusing to project the input")
            continue
        for k in budgets:
            if not 0 < k < world.m:
                continue
            probe_surrogate_and_bounds(em, world, ref, k, k2)
            probe_kappa_di(em, world, ref, k, k2)
        probe_profile_rank(em, world, ref, k2)
