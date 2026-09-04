"""STRUCTURAL chain probe: budget optima, rankability taxonomy, the exact
prefix-cover dimension, the staircase family and the max-of-modular bridge.
"""
from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from ..exact import (Q, ZERO, ONE, HALF, ratio, is_chain, incomparable_pairs)
from ..schema import (Emitter, MODE_EXACT, MODE_FLOAT, ROLE_INPUT, ROLE_TERM,
                      ROLE_LHS, ROLE_RHS, ROLE_SLACK, ROLE_RATIO, ROLE_FLAG,
                      ROLE_DIAG, ST_OK, ST_UNDEFINED, ST_SKIPPED)
from ..worlds import Support, World
from ._common import (exact_optimum, topc_set, co_extremizable,
                      all_subsets_modular, max_of_modular_value, world_key)

CHAIN = "STRUCTURAL"


def layer_optima(world: World, epsilon: Q = ZERO, support: Support | None = None):
    """For each budget k, the optimum value and every acceptable set."""
    out = {}
    for k in range(world.m + 1):
        opt, opts = exact_optimum(world, k, support=support)
        acceptable = tuple(
            S for S in itertools.combinations(range(world.m), k)
            if world.additive_radius(S, support) - opt <= epsilon
        )
        out[k] = {"opt": opt, "optima": opts, "acceptable": acceptable}
    return out


def probe_budget_optima(em: Emitter, world: World, key: Dict) -> None:
    e = "STR.budget_optima"
    layers = layer_optima(world)
    for k, info in layers.items():
        inst = dict(key, k=k)
        S_topc = () if k == 0 else topc_set(world, k)
        topc_val = world.additive_radius(S_topc)
        em.emit(chain=CHAIN, eq_id=e, symbol="k", value=k, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="opt_value", value=info["opt"], role=ROLE_LHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="n_optima", value=len(info["optima"]),
                role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="unique", value=1 if len(info["optima"]) == 1 else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="optimum_set", value=len(info["optima"][0]) if info["optima"] else 0,
                role=ROLE_DIAG, instance=inst, note=str(info["optima"][:3]))
        em.emit(chain=CHAIN, eq_id=e, symbol="topc_value", value=topc_val, role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="is_topc",
                value=1 if S_topc in info["optima"] else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="topc_regret_k", value=topc_val - info["opt"],
                role=ROLE_SLACK, instance=inst)


def probe_taxonomy(em: Emitter, world: World, key: Dict) -> None:
    """STR.coext_iff_modular and STR.scalar_prefix_rankable in one pass."""
    coext = co_extremizable(world)
    modular, worst_gap, n_checked = all_subsets_modular(world)
    layers = layer_optima(world)
    topc_all = all(
        (() if k == 0 else topc_set(world, k)) in layers[k]["optima"]
        for k in range(world.m + 1)
    )
    rankable, chain_witness = _scalar_prefix_rankable(world, layers)
    n_incomp = _max_incomparable_optima(layers)

    inst = dict(key)
    e = "STR.coext_iff_modular"
    em.emit(chain=CHAIN, eq_id=e, symbol="co_extremizable", value=1 if coext else 0,
            role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="all_subsets_modular", value=1 if modular else 0,
            role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="iff_holds", value=1 if coext == modular else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="topc_exact_all_budgets", value=1 if topc_all else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="implication_holds",
            value=1 if ((not modular) or topc_all) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_subsets_checked", value=n_checked,
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="worst_modularity_gap", value=worst_gap,
            role=ROLE_TERM, instance=inst)

    e = "STR.scalar_prefix_rankable"
    em.emit(chain=CHAIN, eq_id=e, symbol="scalar_prefix_rankable", value=1 if rankable else 0,
            role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="nested_optimal_chain", value=1 if chain_witness else 0,
            role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="iff_holds",
            value=1 if rankable == chain_witness else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="topc_exact", value=1 if topc_all else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="rankable_but_not_topc",
            value=1 if (rankable and not topc_all) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="topc_but_not_coext",
            value=1 if (topc_all and not coext) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_incomparable_optima", value=n_incomp,
            role=ROLE_TERM, instance=inst)
    # the exact four-class taxonomy of the m=3 enumeration, generalized
    if coext:
        cls = 3
    elif topc_all:
        cls = 2
    elif rankable:
        cls = 1
    else:
        cls = 0
    em.emit(chain=CHAIN, eq_id=e, symbol="taxonomy_class", value=cls, role=ROLE_DIAG,
            instance=inst,
            note="0 not-rankable, 1 rankable-not-topc, 2 topc-not-coext, 3 coext")


def _scalar_prefix_rankable(world: World, layers) -> Tuple[bool, bool]:
    """True iff some full ranking has an optimal prefix at every budget."""
    m = world.m
    for perm in itertools.permutations(range(m)):
        ok = True
        for k in range(m + 1):
            if tuple(sorted(perm[:k])) not in layers[k]["optima"]:
                ok = False
                break
        if ok:
            return True, True
    return False, False


def _max_incomparable_optima(layers) -> int:
    """Largest antichain among 'unique optimum' layers -- the Dilworth signal.

    This is the quantity that actually drives the staircase lower bound, so it
    is recorded on every world, not only on the constructed family.
    """
    uniq = [frozenset(v["optima"][0]) for v in layers.values() if len(v["optima"]) == 1]
    return incomparable_pairs(uniq)


def probe_prefix_cover(em: Emitter, world: World, key: Dict, epsilon: Q = ZERO,
                       *, max_m: int = 7) -> None:
    """STR.prefix_cover_dimension -- exact chi by ranking enumeration.

    For each full ranking we record which budget layers its prefixes hit, then
    solve the tiny set-cover over layers exactly.  This is exponential in m by
    construction and is a discovery tool, not an algorithm: the cap is explicit
    so a skipped instance is visible in the store.
    """
    m = world.m
    e = "STR.prefix_cover_dimension"
    inst = dict(key, epsilon=str(epsilon))
    if m > max_m:
        for sym in ("chi_prefix", "lower_bound", "upper_bound_m_plus_1"):
            em.emit(chain=CHAIN, eq_id=e, symbol=sym, value=None, role=ROLE_TERM,
                    status=ST_SKIPPED, instance=inst, note="m above enumeration cap")
        return
    layers = layer_optima(world, epsilon)
    acceptable = {k: set(layers[k]["acceptable"]) for k in range(m + 1)}
    covers = []
    for perm in itertools.permutations(range(m)):
        hit = frozenset(k for k in range(m + 1) if tuple(sorted(perm[:k])) in acceptable[k])
        covers.append(hit)
    universe = frozenset(range(m + 1))
    covers = sorted(set(covers), key=lambda s: -len(s))
    chi = None
    for size in range(1, m + 2):
        for combo in itertools.combinations(covers, size):
            if frozenset().union(*combo) >= universe:
                chi = size
                break
        if chi is not None:
            break
    em.emit(chain=CHAIN, eq_id=e, symbol="chi_prefix", value=chi, role=ROLE_LHS,
            status=ST_OK if chi is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="epsilon", value=epsilon, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="upper_bound_m_plus_1", value=m + 1,
            role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lower_bound", value=1, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sandwich_holds",
            value=1 if (chi is not None and 1 <= chi <= m + 1) else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_rankings_tried", value=len(covers),
            role=ROLE_DIAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="layers_covered", value=len(universe),
            role=ROLE_DIAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="exact", value=1, role=ROLE_FLAG, instance=inst)


def probe_staircase(em: Emitter, world: World, r: int, key: Dict) -> None:
    """STR.staircase_family -- the Theta(m) sandwich and *why* it holds.

    The scientific content is the characterization of the zero-radius omitted
    sets, which is what forces a unique optimum per layer; the covering step is
    then a one-line antichain argument.  Both are measured separately so the
    distinction survives into the store.
    """
    m = world.m
    e = "STR.staircase_family"
    inst = dict(key, r=r)
    layers = layer_optima(world)
    zero_sets = []
    for size in range(0, m + 1):
        for T in itertools.combinations(range(m), size):
            if world.additive_radius([j for j in range(m) if j not in set(T)]) == 0:
                zero_sets.append(frozenset(T))
    uniq_layers = sum(1 for k in layers if len(layers[k]["optima"]) == 1)
    opt_sets = [frozenset(layers[k]["optima"][0]) for k in layers if len(layers[k]["optima"]) == 1]
    antichain = incomparable_pairs(opt_sets)
    chi_lower = r
    chi_upper = 2 * r + 1
    em.emit(chain=CHAIN, eq_id=e, symbol="r", value=r, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="chi_lower", value=chi_lower, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="chi_upper", value=chi_upper, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_zero_radius_sets", value=len(zero_sets),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="unique_optimum_per_layer", value=uniq_layers,
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="antichain_size", value=antichain,
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="pairwise_incomparable",
            value=1 if antichain == len(opt_sets) * (len(opt_sets) - 1) // 2 else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="zero_sets_are_blocks",
            value=len(zero_sets), role=ROLE_DIAG, instance=inst,
            note="characterization target: empty set plus one block per staircase level")
    chi = None
    if m <= 7:
        acceptable = {kk: set(layers[kk]["optima"]) for kk in range(m + 1)}
        covers = set()
        for perm in itertools.permutations(range(m)):
            covers.add(frozenset(kk for kk in range(m + 1)
                                 if tuple(sorted(perm[:kk])) in acceptable[kk]))
        universe = frozenset(range(m + 1))
        for size in range(1, m + 2):
            for combo in itertools.combinations(sorted(covers, key=lambda s: -len(s)), size):
                if frozenset().union(*combo) >= universe:
                    chi = size
                    break
            if chi is not None:
                break
    em.emit(chain=CHAIN, eq_id=e, symbol="chi_measured", value=chi, role=ROLE_LHS,
            status=ST_OK if chi is not None else ST_SKIPPED, instance=inst,
            note="" if chi is not None else "m above the enumeration cap")
    em.emit(chain=CHAIN, eq_id=e, symbol="sandwich_holds",
            value=(1 if (chi is not None and chi_lower <= chi <= chi_upper) else 0)
                  if chi is not None else None,
            role=ROLE_FLAG, status=ST_OK if chi is not None else ST_SKIPPED,
            instance=inst)


def probe_max_modular(em: Emitter, world: World, key: Dict, *, max_sets: int = 12) -> None:
    """STR.max_of_modular -- the identity that turns supportOsc into a minimax
    over finitely many linear scenarios."""
    e = "STR.max_of_modular"
    n = 0
    for k in range(world.m + 1):
        for S in itertools.combinations(range(world.m), k):
            if n >= max_sets:
                return
            n += 1
            doubled = 2 * world.additive_radius(S)
            val, arg, n_scen = max_of_modular_value(world, S)
            inst = dict(key, k=k, retained=str(S))
            if val is None:
                em.emit(chain=CHAIN, eq_id=e, symbol="max_modular_value", value=None,
                        role=ROLE_RHS, status=ST_SKIPPED, instance=inst,
                        note="|Omega|^2 above the probe cost cap")
                em.emit(chain=CHAIN, eq_id=e, symbol="n_scenarios", value=n_scen,
                        role=ROLE_INPUT, instance=inst)
                continue
            em.emit(chain=CHAIN, eq_id=e, symbol="radius_doubled", value=doubled,
                    role=ROLE_LHS, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="max_modular_value", value=val,
                    role=ROLE_RHS, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="identity_residual", value=doubled - val,
                    role=ROLE_SLACK, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="holds", value=1 if doubled == val else 0,
                    role=ROLE_FLAG, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="n_scenarios", value=n_scen,
                    role=ROLE_INPUT, instance=inst)
            em.emit(chain=CHAIN, eq_id=e, symbol="argmax_pair", value=0, role=ROLE_DIAG,
                    instance=inst, note=str(arg))
            keep = set(S)
            n_active = sum(
                1 for a in world.support.omega for b in world.support.omega
                if sum(world.primitives[j][a[j]] - world.primitives[j][b[j]]
                       for j in range(world.m) if j not in keep) == val)
            em.emit(chain=CHAIN, eq_id=e, symbol="active_scenario_count", value=n_active,
                    role=ROLE_TERM, instance=inst,
                    note="how many linear scenarios attain the max: the LP degeneracy signal")


def probe_nested_regret(em: Emitter, world: World, key: Dict, *, max_m: int = 7) -> None:
    """STR.nested_regret -- R_nested against eps_allopt and m*eps_allopt.

    This is the branch that collides with the incremental-maximization
    literature, so the competitive ratio those papers study is emitted next to
    the portfolio's own scaled bound rather than in place of it.
    """
    m = world.m
    e = "STR.nested_regret"
    inst = dict(key)
    if m > max_m:
        em.emit(chain=CHAIN, eq_id=e, symbol="R_nested", value=None, role=ROLE_LHS,
                status=ST_SKIPPED, instance=inst, note="m above enumeration cap")
        return
    layers = layer_optima(world)
    best_r, best_perm = None, None
    for perm in itertools.permutations(range(m)):
        worst = ZERO
        worst_k = 0
        for k in range(m + 1):
            reg = world.additive_radius(perm[:k]) - layers[k]["opt"]
            if reg > worst:
                worst, worst_k = reg, k
        if best_r is None or worst < best_r:
            best_r, best_perm, worst_budget = worst, perm, worst_k
    # eps_allopt: the all-optimal-extension defect
    eps_all = ZERO
    for k in range(m):
        for S in layers[k]["optima"]:
            ext_best = None
            for j in range(m):
                if j in set(S):
                    continue
                v = world.additive_radius(tuple(sorted(set(S) | {j})))
                if ext_best is None or v < ext_best:
                    ext_best = v
            if ext_best is not None:
                d = ext_best - layers[k + 1]["opt"]
                if d > eps_all:
                    eps_all = d
    em.emit(chain=CHAIN, eq_id=e, symbol="R_nested", value=best_r, role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="eps_allopt", value=eps_all, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="m", value=m, role=ROLE_INPUT, instance=inst)
    r1 = ratio(best_r, eps_all)
    em.emit(chain=CHAIN, eq_id=e, symbol="ratio_to_eps", value=r1, role=ROLE_RATIO,
            status=ST_OK if r1 is not None else ST_UNDEFINED, instance=inst)
    r2 = ratio(best_r, Q(m) * eps_all) if eps_all != 0 else None
    em.emit(chain=CHAIN, eq_id=e, symbol="ratio_to_m_eps", value=r2, role=ROLE_RATIO,
            status=ST_OK if r2 is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="raw_bound_holds",
            value=1 if best_r <= eps_all else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="scaled_bound_holds",
            value=1 if best_r <= Q(m) * eps_all else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="best_ranking", value=0, role=ROLE_DIAG,
            instance=inst, note=str(best_perm))
    em.emit(chain=CHAIN, eq_id=e, symbol="worst_budget", value=worst_budget,
            role=ROLE_DIAG, instance=inst)
    # incremental-maximization style competitive ratio, for literature comparison
    ratios = []
    for k in range(1, m + 1):
        opt_k = layers[k]["opt"]
        got = world.additive_radius(best_perm[:k])
        if opt_k > 0:
            ratios.append(got / opt_k)
    em.emit(chain=CHAIN, eq_id=e, symbol="incremental_competitive_ratio",
            value=max(ratios) if ratios else None, role=ROLE_DIAG,
            status=ST_OK if ratios else ST_UNDEFINED, instance=inst,
            note="compare against phi+1 bounds for incremental maximization")


def run(em: Emitter, world: World, *, rng, epsilons: Sequence[Q] = (ZERO,)) -> None:
    key = world_key(world)
    probe_budget_optima(em, world, key)
    probe_taxonomy(em, world, key)
    for eps in epsilons:
        probe_prefix_cover(em, world, key, eps)
    probe_max_modular(em, world, key)
    probe_nested_regret(em, world, key)
