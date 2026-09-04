"""QUERY chain probe: semantic sufficiency, the quantitative error floor,
representation necessity, and a fail-closed method-by-query transfer matrix.
"""
from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from ..exact import Q, ZERO, ONE, HALF, osc, ratio, topk, argsort_desc
from ..schema import (Emitter, MODE_EXACT, MODE_FLOAT, ROLE_INPUT, ROLE_TERM,
                      ROLE_LHS, ROLE_RHS, ROLE_SLACK, ROLE_RATIO, ROLE_FLAG,
                      ROLE_DIAG, ST_OK, ST_UNDEFINED, ST_SKIPPED, ST_BLOCKED)
from ..worlds import World
from ._common import world_key

CHAIN = "QUERY"

# Each query declares the capability its oracle needs.  A method may only be
# scored on a query when the environment exposes that capability; otherwise the
# cell is BLOCKED and no numerical substitute is inserted.
QUERIES = {
    "capacity":   "response_panel",
    "removal":    "removal_semantics",
    "synergy":    "coalition_intervention",
    "direction":  "policy_contrast",
}

METHODS = {
    "span":      ("response_panel",),
    "removal":   ("removal_semantics",),
    "coalition": ("coalition_intervention",),
    "contrast":  ("policy_contrast",),
    "featnorm":  ("response_panel",),
}

NATIVE = {"capacity": "span", "removal": "removal", "synergy": "coalition",
          "direction": "contrast"}


# ------------------------------------------------------------- target values

def target_utility(world: World, query: str) -> List[Q]:
    """Per-relation utility under the declared query; higher is better."""
    m = world.m
    if query == "capacity":
        return list(world.component_spans())
    if query == "removal":
        # value of relation j = loss incurred when j is dropped from the full set
        out = []
        for j in range(m):
            kept = tuple(i for i in range(m) if i != j)
            out.append(world.true_compression_loss(kept))
        return out
    if query == "synergy":
        out = []
        for j in range(m):
            best = ZERO
            for l in range(m):
                if l == j:
                    continue
                pair = world.true_compression_loss(tuple(i for i in range(m) if i not in (j, l)))
                sing_j = world.true_compression_loss(tuple(i for i in range(m) if i != j))
                sing_l = world.true_compression_loss(tuple(i for i in range(m) if i != l))
                syn = pair - sing_j - sing_l
                if abs(syn) > abs(best):
                    best = syn
            out.append(abs(best))
        return out
    if query == "direction":
        out = []
        for j in range(m):
            vals = world.primitives[j]
            out.append(abs(vals[-1] - vals[0]) if len(vals) >= 2 else ZERO)
        return out
    raise ValueError("unknown query: " + str(query))


def method_scores(world: World, method: str) -> List[Q]:
    """What each method actually computes -- deliberately *not* the target."""
    m = world.m
    if method == "span":
        return list(world.component_spans())
    if method == "removal":
        return target_utility(world, "removal")
    if method == "coalition":
        return target_utility(world, "synergy")
    if method == "contrast":
        return target_utility(world, "direction")
    if method == "featnorm":
        # a response-panel proxy: sum of absolute primitive values
        return [sum(abs(v) for v in world.primitives[j]) for j in range(m)]
    raise ValueError("unknown method: " + str(method))


def _spearman(a, b) -> float:
    """Rank correlation, reported only as a secondary diagnostic."""
    n = len(a)
    if n < 2:
        return 0.0
    ra = _ranks(a); rb = _ranks(b)
    ma = sum(ra) / n; mb = sum(rb) / n
    sxx = sum((x - ma) ** 2 for x in ra)
    syy = sum((y - mb) ** 2 for y in rb)
    if sxx <= 0 or syy <= 0:
        return 0.0
    sxy = sum((x - ma) * (y - mb) for x, y in zip(ra, rb))
    return float(sxy / (sxx ** 0.5 * syy ** 0.5))


def _ranks(v):
    order = sorted(range(len(v)), key=lambda i: (v[i], i))
    out = [0.0] * len(v)
    for r, i in enumerate(order):
        out[i] = float(r)
    return out


# ----------------------------------------------------------------- probes

def probe_sufficiency(em: Emitter, worlds: Sequence[World], query: str,
                      key: Dict) -> None:
    """QRY.sufficiency -- does the pairwise summary determine this target?"""
    e = "QRY.sufficiency"
    by_summary: Dict[Tuple, List[int]] = {}
    for i, w in enumerate(worlds):
        s = tuple(w.component_spans())
        by_summary.setdefault(s, []).append(i)
    violations = 0
    worst = ZERO
    for s, idxs in by_summary.items():
        for i, j in itertools.combinations(idxs, 2):
            ti = tuple(target_utility(worlds[i], query))
            tj = tuple(target_utility(worlds[j], query))
            if ti != tj:
                violations += 1
                gap = max(abs(a - b) for a, b in zip(ti, tj))
                if gap > worst:
                    worst = gap
    inst = dict(key, query=query)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_models", value=len(worlds), role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_summary_classes", value=len(by_summary),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sufficient", value=1 if violations == 0 else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_violating_pairs", value=violations,
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="worst_target_gap", value=worst, role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="summary_kind", value=0, role=ROLE_DIAG,
            instance=inst, note="pairwise component spans")
    em.emit(chain=CHAIN, eq_id=e, symbol="target_kind", value=0, role=ROLE_DIAG,
            instance=inst, note=query)

    # -- the quantitative floor on the worst violating pair ---------------
    if violations:
        e2 = "QRY.quantitative_floor"
        for s, idxs in by_summary.items():
            for i, j in itertools.combinations(idxs, 2):
                ti = target_utility(worlds[i], query)
                tj = target_utility(worlds[j], query)
                if ti == tj:
                    continue
                r = max(range(len(ti)), key=lambda x: abs(ti[x] - tj[x]))
                t1, t2 = ti[r], tj[r]
                floor = abs(t1 - t2) * HALF
                mid = (t1 + t2) * HALF
                best_err = max(abs(mid - t1), abs(mid - t2))
                i2 = dict(inst, pair="%d-%d" % (i, j), relation=r)
                em.emit(chain=CHAIN, eq_id=e2, symbol="t1", value=t1, role=ROLE_TERM, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="t2", value=t2, role=ROLE_TERM, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="target_gap", value=abs(t1 - t2),
                        role=ROLE_TERM, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="floor", value=floor, role=ROLE_RHS, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="best_predictor_error", value=best_err,
                        role=ROLE_LHS, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="achieved_by_midpoint",
                        value=1 if best_err == floor else 0, role=ROLE_FLAG, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="slack", value=best_err - floor,
                        role=ROLE_SLACK, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="holds", value=1 if best_err >= floor else 0,
                        role=ROLE_FLAG, instance=i2)
                em.emit(chain=CHAIN, eq_id=e2, symbol="violation",
                        value=1 if best_err < floor else 0, role=ROLE_FLAG, instance=i2)
                return


def probe_representation(em: Emitter, worlds: Sequence[World], query: str,
                         epsilon: Q, key: Dict) -> None:
    """QRY.representation_necessity -- a common good decision on each fibre."""
    e = "QRY.representation_necessity"
    fibres: Dict[Tuple, List[int]] = {}
    for i, w in enumerate(worlds):
        fibres.setdefault(tuple(w.component_spans()), []).append(i)
    n_empty = 0
    for s, idxs in fibres.items():
        goods = []
        for i in idxs:
            u = target_utility(worlds[i], query)
            best = max(u)
            goods.append({j for j in range(len(u)) if best - u[j] <= epsilon})
        inter = set.intersection(*goods) if goods else set()
        n_empty += int(len(inter) == 0)
        inst = dict(key, query=query, epsilon=str(epsilon), fibre_size=len(idxs))
        em.emit(chain=CHAIN, eq_id=e, symbol="fibre_size", value=len(idxs),
                role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="epsilon", value=epsilon, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="intersection_size", value=len(inter),
                role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="common_good_exists",
                value=1 if inter else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="uniform_low_regret_possible",
                value=1 if inter else 0, role=ROLE_FLAG, instance=inst)
    inst = dict(key, query=query, epsilon=str(epsilon))
    em.emit(chain=CHAIN, eq_id=e, symbol="n_fibres", value=len(fibres), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_empty_intersections", value=n_empty,
            role=ROLE_TERM, instance=inst)


def probe_matrix(em: Emitter, world: World, key: Dict,
                 capabilities: Sequence[str], budgets: Dict[str, int],
                 budget_cap: int) -> None:
    """QRY.transfer_regret, QRY.three_gates, QRY.matched_budget.

    Gates are applied in order.  A cell whose capability is absent is BLOCKED
    and carries *no* number: substituting a response proxy there is exactly the
    silent semantic substitution the chain forbids.
    """
    caps = set(capabilities)
    e_t = "QRY.transfer_regret"
    e_g = "QRY.three_gates"
    e_b = "QRY.matched_budget"
    n_blocked = n_insuff = n_eval = 0
    for qname, need in QUERIES.items():
        util = target_utility(world, qname)
        best = max(util)
        for mname, mneeds in METHODS.items():
            inst = dict(key, query=qname, method=mname,
                        is_native=int(NATIVE[qname] == mname))
            cap_ok = need in caps and all(x in caps for x in mneeds)
            if not cap_ok:
                n_blocked += 1
                em.emit(chain=CHAIN, eq_id=e_g, symbol="capability_ok", value=0,
                        role=ROLE_FLAG, instance=inst)
                em.emit(chain=CHAIN, eq_id=e_g, symbol="cell_status", value=0,
                        role=ROLE_DIAG, instance=inst, note="BLOCKED_NA")
                em.emit(chain=CHAIN, eq_id=e_g, symbol="regret_attached", value=0,
                        role=ROLE_FLAG, instance=inst)
                em.emit(chain=CHAIN, eq_id=e_t, symbol="transfer_regret", value=None,
                        role=ROLE_LHS, status=ST_BLOCKED, instance=inst,
                        note="missing capability: " + need)
                continue
            scores = method_scores(world, mname)
            chosen = max(range(len(scores)), key=lambda j: (scores[j], -j))
            regret = best - util[chosen]
            # identifiability: does this method's score vector separate the
            # top-utility relation from the rest at all?
            identifiable = len({scores[j] for j in range(len(scores))}) > 1
            if not identifiable:
                n_insuff += 1
                status_code = 1
            else:
                n_eval += 1
                status_code = 2
            em.emit(chain=CHAIN, eq_id=e_g, symbol="capability_ok", value=1,
                    role=ROLE_FLAG, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_g, symbol="identifiable",
                    value=1 if identifiable else 0, role=ROLE_FLAG, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_g, symbol="cell_status", value=status_code,
                    role=ROLE_DIAG, instance=inst,
                    note={1: "INSUFFICIENT", 2: "EVALUABLE"}[status_code])
            em.emit(chain=CHAIN, eq_id=e_g, symbol="regret_attached",
                    value=1 if status_code == 2 else 0, role=ROLE_FLAG, instance=inst)
            if status_code != 2:
                em.emit(chain=CHAIN, eq_id=e_t, symbol="transfer_regret", value=None,
                        role=ROLE_LHS, status=ST_SKIPPED, instance=inst,
                        note="insufficient summary; no number is attached")
                continue
            em.emit(chain=CHAIN, eq_id=e_t, symbol="transfer_regret", value=regret,
                    role=ROLE_LHS, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_t, symbol="is_native_method",
                    value=1 if NATIVE[qname] == mname else 0, role=ROLE_FLAG, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_t, symbol="native_regret",
                    value=regret if NATIVE[qname] == mname else None, role=ROLE_TERM,
                    status=ST_OK if NATIVE[qname] == mname else ST_UNDEFINED, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_t, symbol="foreign_regret",
                    value=regret if NATIVE[qname] != mname else None, role=ROLE_TERM,
                    status=ST_OK if NATIVE[qname] != mname else ST_UNDEFINED, instance=inst)
            scale = osc(list(util)) if len(set(util)) > 1 else ONE
            em.emit(chain=CHAIN, eq_id=e_t, symbol="normalized_regret",
                    value=ratio(regret, scale), role=ROLE_RATIO,
                    status=ST_OK if scale != 0 else ST_UNDEFINED, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_t, symbol="method", value=0, role=ROLE_DIAG,
                    instance=inst, note=mname)
            em.emit(chain=CHAIN, eq_id=e_t, symbol="query", value=0, role=ROLE_DIAG,
                    instance=inst, note=qname)
            em.emit(chain=CHAIN, eq_id=e_t, symbol="native", value=0, role=ROLE_DIAG,
                    instance=inst, note=NATIVE[qname])
            nat_scores = method_scores(world, NATIVE[qname])
            nat_choice = max(range(len(nat_scores)), key=lambda x: (nat_scores[x], -x))
            nat_reg = best - util[nat_choice]
            em.emit(chain=CHAIN, eq_id=e_t, symbol="native_advantage",
                    value=regret - nat_reg, role=ROLE_SLACK, instance=inst,
                    note="foreign regret minus native regret on the same instance")
            em.emit(chain=CHAIN, eq_id=e_t, symbol="rank_correlation",
                    value=_spearman(scores, util), role=ROLE_DIAG, mode=MODE_FLOAT,
                    instance=inst,
                    note="kept as a secondary diagnostic; regret is the headline")
            em.emit(chain=CHAIN, eq_id=e_b, symbol="advantage_from_budget",
                    value=Q(budgets.get(mname, 1) - budgets.get(NATIVE[qname], 1)),
                    role=ROLE_DIAG, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_t, symbol="topk_overlap",
                    value=len(set(topk(tuple(scores), 1)) & set(topk(tuple(util), 1))),
                    role=ROLE_DIAG, instance=inst)
            used = budgets.get(mname, 1)
            em.emit(chain=CHAIN, eq_id=e_b, symbol="budget_used", value=used,
                    role=ROLE_INPUT, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_b, symbol="budget_cap", value=budget_cap,
                    role=ROLE_INPUT, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_b, symbol="within_budget",
                    value=1 if used <= budget_cap else 0, role=ROLE_FLAG, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_b, symbol="budget_ratio",
                    value=Q(used, max(1, budget_cap)), role=ROLE_RATIO, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_b, symbol="regret_full", value=regret,
                    role=ROLE_TERM, instance=inst)
            em.emit(chain=CHAIN, eq_id=e_b, symbol="regret_matched",
                    value=regret if used <= budget_cap else None, role=ROLE_TERM,
                    status=ST_OK if used <= budget_cap else ST_SKIPPED, instance=inst)
    inst = dict(key)
    n_cells = len(QUERIES) * len(METHODS)
    em.emit(chain=CHAIN, eq_id=e_g, symbol="n_blocked", value=n_blocked, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e_g, symbol="n_insufficient", value=n_insuff, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e_g, symbol="n_evaluable", value=n_eval, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e_g, symbol="n_cells", value=n_cells, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e_g, symbol="matrix_complete",
            value=1 if n_eval == n_cells else 0, role=ROLE_FLAG, instance=inst,
            note="aggregate method presence is not readiness; every cell must be present")
    em.emit(chain=CHAIN, eq_id=e_g, symbol="readiness", value=Q(n_eval, n_cells),
            role=ROLE_RATIO, instance=inst)


def run(em: Emitter, worlds: Sequence[World], *, rng,
        capability_sets: Sequence[Tuple[str, Sequence[str]]] = ()) -> None:
    if not worlds:
        return
    key = world_key(worlds[0])
    key.pop("world_id", None)
    key["n_models"] = len(worlds)
    for qname in QUERIES:
        probe_sufficiency(em, worlds, qname, key)
        for eps in (ZERO, Q(1, 4)):
            probe_representation(em, worlds, qname, eps, key)
    sets = list(capability_sets) or [
        ("full", tuple(set(QUERIES.values()))),
        ("response_only", ("response_panel",)),
        ("no_coalition", ("response_panel", "removal_semantics", "policy_contrast")),
    ]
    budgets = {"span": 1, "removal": 4, "coalition": 32, "contrast": 2, "featnorm": 1}
    # The same-summary twins are deliberately degenerate on the span summary, so
    # a matrix built only from them is entirely INSUFFICIENT and carries no
    # regret at all.  Mix them with ordinary worlds so both the blocked and the
    # evaluable branches of the three-gate contract get exercised.
    degenerate = [w for w in worlds if len({tuple(w.component_spans())}) and
                  len(set(w.component_spans())) <= 1]
    varied = [w for w in worlds if len(set(w.component_spans())) > 1]
    matrix_pool = (varied[:5] + degenerate[:2]) or list(worlds[:6])
    for name, caps in sets:
        for w in matrix_pool:
            k2 = world_key(w)
            k2["capability_set"] = name
            probe_matrix(em, w, k2, caps, budgets, budget_cap=8)
