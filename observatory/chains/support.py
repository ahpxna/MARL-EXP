"""SUPPORT chain probe: exact compression radius, deficit, brackets, and the
decision-critical query problem measured as a Test Cover instance.
"""
from __future__ import annotations

import itertools
import math
from fractions import Fraction
from typing import Dict, Iterable, List, Sequence, Tuple

from ..exact import Q, ZERO, ONE, HALF, osc, half_osc, ratio
from ..schema import (Emitter, MODE_EXACT, MODE_FLOAT, ROLE_INPUT, ROLE_TERM,
                      ROLE_LHS, ROLE_RHS, ROLE_SLACK, ROLE_RATIO, ROLE_FLAG,
                      ROLE_DIAG, ST_OK, ST_UNDEFINED, ST_SKIPPED)
from ..worlds import Support, World, Action
from ._common import (exact_optimum, topc_set, deficit_terms, zeta_def, global_E,
                      co_extremizable, all_subsets_modular, eps_good_sets,
                      world_key)

CHAIN = "SUPPORT"


def probe_radius(em: Emitter, world: World, k: int, key: Dict) -> None:
    """SUP.exact_radius -- the definition, with every ingredient recorded."""
    S = _retained(world, k)
    omitted = [world.omitted_sum(S, a) for a in world.support.omega]
    inst = dict(key, k=k, retained=str(S))
    e = "SUP.exact_radius"
    em.emit(chain=CHAIN, eq_id=e, symbol="radius", value=half_osc(omitted),
            role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="k", value=int(k), role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="omitted_card", value=world.m - int(k),
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="omega_size", value=len(world.support.omega),
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="omega_density", value=world.support.density(),
            role=ROLE_DIAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="is_cartesian",
            value=1 if world.support.is_cartesian else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="osc_omitted", value=osc(omitted),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="min_omitted", value=min(omitted),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="max_omitted", value=max(omitted),
            role=ROLE_TERM, instance=inst)


def _retained(world: World, k: int):
    """Top-C retained set, with k = 0 meaning 'retain nothing'.

    Budget zero is not a degenerate case here: the modular formula's sharpest
    failure is at S = empty, where the radius must compress *every* component
    simultaneously.  Skipping it is how a coupled-support counterexample can
    look modular.
    """
    return () if int(k) == 0 else topc_set(world, int(k))


def probe_modular(em: Emitter, world: World, k: int, key: Dict) -> None:
    """SUP.modular_formula -- the killed universal law, measured as a gap."""
    S = _retained(world, k)
    spans = world.component_spans()
    exact = world.additive_radius(S)
    modular = HALF * sum(spans[j] for j in range(world.m) if j not in set(S))
    coext = co_extremizable(world)
    inst = dict(key, k=k, retained=str(S))
    e = "SUP.modular_formula"
    em.emit(chain=CHAIN, eq_id=e, symbol="radius_exact", value=exact, role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="radius_modular", value=modular, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="gap", value=modular - exact, role=ROLE_SLACK, instance=inst)
    r = ratio(exact, modular)
    em.emit(chain=CHAIN, eq_id=e, symbol="ratio", value=r, role=ROLE_RATIO,
            status=ST_OK if r is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="holds", value=1 if exact == modular else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="co_extremizable", value=1 if coext else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sum_spans", value=sum(spans), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_relations", value=world.m, role=ROLE_INPUT, instance=inst)


def probe_deficit(em: Emitter, world: World, key: Dict, *, max_sets: int = 64) -> None:
    """SUP.deficit -- the one-sided identity on every omitted set we can afford."""
    e = "SUP.deficit"
    seen = 0
    for size in range(1, world.m + 1):
        for T in itertools.combinations(range(world.m), size):
            if seen >= max_sets:
                return
            seen += 1
            t = deficit_terms(world, T)
            inst = dict(key, omitted=str(T), T_card=size)
            em.emit(chain=CHAIN, eq_id=e, symbol="M", value=t["M"], role=ROLE_TERM, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="F_Omega", value=t["F"], role=ROLE_TERM, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="d_Omega", value=t["d"], role=ROLE_LHS, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="e_plus", value=t["e_plus"], role=ROLE_TERM, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="e_minus", value=t["e_minus"], role=ROLE_TERM, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="identity_residual",
                    value=t["d"] - (t["e_plus"] + t["e_minus"]), role=ROLE_SLACK, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="nonneg_holds",
                    value=1 if t["d"] >= 0 else 0, role=ROLE_FLAG, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="T_card", value=size, role=ROLE_INPUT, instance=inst)


def probe_brackets(em: Emitter, world: World, k: int, key: Dict, *, rng=None) -> None:
    """SUP.support_brackets -- monotonicity of the radius in the support."""
    sup = world.support
    omega = list(sup.omega)
    if len(omega) < 3:
        return
    lower = Support(sup.action_sizes, tuple(omega[: max(2, len(omega) - 1)]))
    full = Support.cartesian(sup.action_sizes)
    S = _retained(world, k)
    r_lo = world.additive_radius(S, lower)
    r_ac = world.additive_radius(S, sup)
    r_up = world.additive_radius(S, full)
    inst = dict(key, k=k, retained=str(S))
    e = "SUP.support_brackets"
    em.emit(chain=CHAIN, eq_id=e, symbol="r_lower", value=r_lo, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="r_actual", value=r_ac, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="r_upper", value=r_up, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="bracket_width", value=r_up - r_lo,
            role=ROLE_SLACK, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="monotone_holds",
            value=1 if (r_lo <= r_ac <= r_up) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="interval_contains_truth",
            value=1 if (r_lo <= r_ac <= r_up) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lower_size", value=len(lower.omega),
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="actual_size", value=len(sup.omega),
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="upper_size", value=len(full.omega),
            role=ROLE_INPUT, instance=inst)


def probe_perturbation(em: Emitter, world: World, k: int, key: Dict, noise) -> None:
    """SUP.component_perturbation -- gauge error beats sup norm, measured."""
    est = []
    for j, vals in enumerate(world.primitives):
        shift = noise(j)
        est.append(tuple(v + shift for v in vals))
    est_world = World(world.support, tuple(est), world.baseline, world.residual, world.meta)
    S = _retained(world, k)
    r_hat = est_world.additive_radius(S)
    r_true = world.additive_radius(S)
    deltas = []
    supnorms = []
    for j in range(world.m):
        idx = world.support.projection(j)
        a = [est[j][i] for i in idx]
        b = [world.primitives[j][i] for i in idx]
        deltas.append(half_osc([x - y for x, y in zip(a, b)]))
        supnorms.append(max(abs(x - y) for x, y in zip(a, b)))
    keep = set(S)
    sum_delta = sum(deltas[j] for j in range(world.m) if j not in keep)
    sum_sup = sum(supnorms[j] for j in range(world.m) if j not in keep)
    err = abs(r_hat - r_true)
    inst = dict(key, k=k, retained=str(S))
    e = "SUP.component_perturbation"
    em.emit(chain=CHAIN, eq_id=e, symbol="r_hat", value=r_hat, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="r_true", value=r_true, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="abs_error", value=err, role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sum_delta", value=sum_delta, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="bound", value=sum_delta, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="slack", value=sum_delta - err, role=ROLE_SLACK, instance=inst)
    rr = ratio(err, sum_delta)
    em.emit(chain=CHAIN, eq_id=e, symbol="ratio", value=rr, role=ROLE_RATIO,
            status=ST_OK if rr is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="holds", value=1 if err <= sum_delta else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sup_norm_alternative", value=sum_sup,
            role=ROLE_DIAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="gauge_beats_supnorm",
            value=1 if sum_delta <= sum_sup else 0, role=ROLE_FLAG, instance=inst)


# ----------------------------------------------------- decision-critical cells

def _good_sets_by_support(worlds: Sequence[Tuple[str, Support]], base: World,
                          k: int, epsilon: Q):
    out = {}
    for name, sup in worlds:
        opt, good = eps_good_sets(base, k, epsilon, sup)
        out[name] = (opt, frozenset(good))
    return out


def probe_critical_cells(em: Emitter, world: World, k: int, epsilon: Q, key: Dict,
                         *, max_cells: int = 16) -> None:
    """SUP.critical_cell -- which single membership bits can flip the decision."""
    sup = world.support
    full = Support.cartesian(sup.action_sizes)
    cells = [a for a in full.omega][:max_cells]
    base_opt, base_good = eps_good_sets(world, k, epsilon, sup)
    n_critical = 0
    e = "SUP.critical_cell"
    for a in cells:
        present = a in set(sup.omega)
        if present:
            other = Support(sup.action_sizes, tuple(x for x in sup.omega if x != a))
        else:
            other = Support(sup.action_sizes, tuple(sorted(set(sup.omega) | {a})))
        if len(other.omega) < 1:
            continue
        o_opt, o_good = eps_good_sets(world, k, epsilon, other)
        disjoint = len(set(base_good) & set(o_good)) == 0
        n_critical += int(disjoint)
        inst = dict(key, k=k, cell=str(a), epsilon=str(epsilon))
        em.emit(chain=CHAIN, eq_id=e, symbol="cell_id", value=int(full.omega.index(a)),
                role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="is_critical", value=1 if disjoint else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="good_set_size_small",
                value=len(base_good), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="good_set_size_large",
                value=len(o_good), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="sets_disjoint", value=1 if disjoint else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="epsilon", value=epsilon,
                role=ROLE_INPUT, instance=inst)
    inst = dict(key, k=k, epsilon=str(epsilon))
    em.emit(chain=CHAIN, eq_id=e, symbol="n_critical", value=n_critical,
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_cells", value=len(cells),
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="critical_fraction",
            value=Q(n_critical, max(1, len(cells))), role=ROLE_RATIO, instance=inst)


# ------------------------------------------------------- test cover reduction

def _greedy_cover(cells: Sequence[Action], separates: Dict[Action, frozenset],
                  required: frozenset):
    """Classical greedy set cover on the required (incompatible) pairs."""
    remaining = set(required)
    chosen: List[Action] = []
    while remaining:
        best, best_gain = None, 0
        for a in cells:
            gain = len(separates[a] & remaining)
            if gain > best_gain:
                best, best_gain = a, gain
        if best is None:
            return chosen, False        # infeasible: some pair is unseparable
        chosen.append(best)
        remaining -= separates[best]
    return chosen, True


def _exact_cover(cells: Sequence[Action], separates: Dict[Action, frozenset],
                 required: frozenset, cap: int = 4):
    """Exact minimum separating set by increasing cardinality, up to ``cap``."""
    if not required:
        return 0, True
    for size in range(1, int(cap) + 1):
        for combo in itertools.combinations(cells, size):
            cov = set()
            for a in combo:
                cov |= separates[a]
            if required <= cov:
                return size, True
    return None, False


def probe_test_cover(em: Emitter, base: World, supports: Sequence[Tuple[str, Support]],
                     k: int, epsilon: Q, key: Dict, *, exact_cap: int = 2) -> None:
    """SUP.separating_query_set and SUP.test_cover_reduction.

    The candidate support family is the vertex set; a membership query on cell
    ``a`` is the edge ``e_a = {Omega : a in Omega}``.  A query set separates a
    pair iff exactly one of the two supports contains the queried cell.  Two
    supports are *required* to be separated when their eps-good decision sets
    are disjoint, so this is a partial Test Cover instance.
    """
    good = _good_sets_by_support(supports, base, k, epsilon)
    names = [n for n, _ in supports]
    sup_by_name = dict(supports)
    pairs = []
    for x, y in itertools.combinations(names, 2):
        if len(good[x][1] & good[y][1]) == 0:
            pairs.append((x, y))
    required = frozenset(pairs)

    all_cells = sorted({a for _, s in supports for a in s.omega})
    separates: Dict[Action, frozenset] = {}
    edge_size: Dict[Action, int] = {}
    for a in all_cells:
        inside = {n for n in names if a in set(sup_by_name[n].omega)}
        edge_size[a] = len(inside)
        sep = {(x, y) for (x, y) in pairs if (x in inside) != (y in inside)}
        separates[a] = frozenset(sep)

    greedy, feasible = _greedy_cover(all_cells, separates, required)
    q_star, found = _exact_cover(all_cells, separates, required, cap=exact_cap)

    n = len(names)
    r = max(edge_size.values()) if edge_size else 0
    lb_r = math.ceil(2 * (n - 1) / (r + 1)) if r > 0 and n > 1 else 0
    all_pairs_required = len(pairs) == n * (n - 1) // 2

    inst = dict(key, k=k, epsilon=str(epsilon), n_supports=n)

    e = "SUP.separating_query_set"
    em.emit(chain=CHAIN, eq_id=e, symbol="q_star", value=q_star,
            role=ROLE_LHS, status=ST_OK if found else ST_SKIPPED, instance=inst,
            note="" if found else "no separating set of size <= %d" % exact_cap)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_worlds", value=n, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_incompatible_pairs", value=len(pairs),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_cells", value=len(all_cells),
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="epsilon", value=epsilon, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="greedy_size", value=len(greedy),
            role=ROLE_TERM, instance=inst)
    gr = ratio(Q(len(greedy)), Q(q_star)) if (found and q_star) else None
    em.emit(chain=CHAIN, eq_id=e, symbol="greedy_ratio", value=gr, role=ROLE_RATIO,
            status=ST_OK if gr is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lower_bound_pairs",
            value=1 if pairs else 0, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="cover_feasible", value=1 if feasible else 0,
            role=ROLE_FLAG, instance=inst)

    e = "SUP.test_cover_reduction"
    em.emit(chain=CHAIN, eq_id=e, symbol="n_vertices", value=n, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_edges", value=len(all_cells), role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="max_edge_size_r", value=r, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="required_pairs", value=len(pairs), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="greedy_size", value=len(greedy), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="is_full_test_cover",
            value=1 if all_pairs_required else 0, role=ROLE_FLAG, instance=inst,
            note="the classical 2(n-1)/(r+1) bound applies only to the full instance")
    em.emit(chain=CHAIN, eq_id=e, symbol="lower_bound_r", value=lb_r,
            role=ROLE_RHS, status=ST_OK if all_pairs_required else ST_UNDEFINED,
            instance=inst)
    lbg = ratio(Q(lb_r), Q(max(1, len(greedy)))) if all_pairs_required else None
    em.emit(chain=CHAIN, eq_id=e, symbol="lb_over_greedy", value=lbg, role=ROLE_RATIO,
            status=ST_OK if lbg is not None else ST_UNDEFINED, instance=inst)
    ln_bound = (1.0 + math.log(len(pairs))) if pairs else 1.0
    em.emit(chain=CHAIN, eq_id=e, symbol="ln_bound", value=ln_bound, role=ROLE_RHS,
            mode=MODE_FLOAT, instance=inst)
    if found and q_star:
        em.emit(chain=CHAIN, eq_id=e, symbol="greedy_over_ln",
                value=float(len(greedy)) / (ln_bound * float(q_star)), role=ROLE_RATIO,
                mode=MODE_FLOAT, instance=inst,
                note="greedy / ((1+ln P) * OPT); the classical guarantee says <= 1")
    else:
        em.emit(chain=CHAIN, eq_id=e, symbol="greedy_over_ln", value=None,
                role=ROLE_RATIO, status=ST_SKIPPED, mode=MODE_FLOAT, instance=inst,
                note="exact optimum not resolved within the enumeration cap")
    em.emit(chain=CHAIN, eq_id=e, symbol="reduction_valid", value=1,
            role=ROLE_FLAG, instance=inst,
            note="separating-query-set == partial Test Cover by construction")


def build_support_family(world: World, k: int, epsilon: Q, *, max_family: int = 5):
    """Support worlds that actually disagree about the decision.

    Toggling one membership bit at a time and keeping only the toggles that
    move the eps-good set guarantees the Test Cover instance has required
    pairs.  A family built from unconstrained random subsets almost always has
    none, which silently turns the reduction into a trivial instance.
    """
    sup = world.support
    full = Support.cartesian(sup.action_sizes)
    _, base_good = eps_good_sets(world, k, epsilon, sup)
    family = [("base", sup)]
    for a in full.omega:
        if len(family) >= int(max_family):
            break
        if a in set(sup.omega):
            cand = Support(sup.action_sizes, tuple(x for x in sup.omega if x != a))
        else:
            cand = Support(sup.action_sizes, tuple(sorted(set(sup.omega) | {a})))
        if len(cand.omega) < 2:
            continue
        _, g = eps_good_sets(world, k, epsilon, cand)
        if frozenset(g) != frozenset(base_good):
            family.append(("toggle" + str(full.omega.index(a)), cand))
    return family


def run(em: Emitter, world: World, *, budgets: Sequence[int], epsilons: Sequence[Q],
        rng, do_test_cover: bool = True) -> None:
    key = world_key(world)
    for k in budgets:
        if not 0 <= k < world.m:
            continue
        probe_radius(em, world, k, key)
        probe_modular(em, world, k, key)
        probe_brackets(em, world, k, key, rng=rng)
        probe_perturbation(em, world, k, key,
                           noise=lambda j: Q(rng.randint(-2, 2), 8))
        for eps in epsilons:
            if k > 0:
                probe_critical_cells(em, world, k, eps, key)
    # The Test Cover instance is expensive and does not depend on the budget in
    # an interesting way, so it is built once per world at the tightest
    # tolerance rather than for every (k, eps) pair.
    if do_test_cover and world.m >= 2 and len(world.support.omega) <= 32:
        k0 = max(1, min(budgets, key=lambda x: abs(x - world.m // 2)) if budgets else 1)
        eps0 = min(epsilons) if epsilons else ZERO
        fam = build_support_family(world, k0, eps0)
        if len(fam) >= 2:
            probe_test_cover(em, world, fam, k0, eps0, key)
    probe_deficit(em, world, key)
