"""MASTER chain probe: certificate hierarchy, score-interval adversaries, the
coverage/tolerance frontier, typed completion and five-type indispensability.
"""
from __future__ import annotations

import itertools
import math
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from ..exact import Q, ZERO, ONE, HALF, osc, half_osc, ratio, topk, argsort_desc
from ..schema import (Emitter, MODE_EXACT, MODE_FLOAT, ROLE_INPUT, ROLE_TERM,
                      ROLE_LHS, ROLE_RHS, ROLE_SLACK, ROLE_RATIO, ROLE_FLAG,
                      ROLE_DIAG, ST_OK, ST_UNDEFINED, ST_SKIPPED)
from ..worlds import Support, World
from ._common import (exact_optimum, topc_set, deficit_terms, zeta_def, global_E,
                      lp_lower_bound, world_key)

CHAIN = "MASTER"


def probe_deficit_identity(em: Emitter, world: World, k: int, key: Dict) -> None:
    """MASTER.deficit_identity -- the same one-sided identity the Support chain
    proves, re-measured here because MASTER's loss chain quotes it directly."""
    e = "MASTER.deficit_identity"
    T = tuple(j for j in range(world.m) if j not in set(topc_set(world, k)))
    t = deficit_terms(world, T)
    inst = dict(key, k=k, omitted=str(T))
    em.emit(chain=CHAIN, eq_id=e, symbol="M", value=t["M"], role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="F_Omega", value=t["F"], role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="d_Omega", value=t["d"], role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="e_plus", value=t["e_plus"], role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="e_minus", value=t["e_minus"], role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sum_check", value=t["e_plus"] + t["e_minus"],
            role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="identity_residual",
            value=t["d"] - (t["e_plus"] + t["e_minus"]), role=ROLE_SLACK, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="nonneg_holds", value=1 if t["d"] >= 0 else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="omitted_card", value=len(T),
            role=ROLE_INPUT, instance=inst)


def probe_certificates(em: Emitter, world: World, k: int, key: Dict) -> None:
    """Every route of the certificate hierarchy on one instance, side by side."""
    S = topc_set(world, k)
    r_topc = world.additive_radius(S)
    r_opt, opts = exact_optimum(world, k)
    regret = r_topc - r_opt
    zeta = zeta_def(world, k)
    E = global_E(world)
    inst = dict(key, k=k, retained=str(S))

    # -- zeta/2 --------------------------------------------------------
    e = "MASTER.zeta_half"
    em.emit(chain=CHAIN, eq_id=e, symbol="topc_radius", value=r_topc, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="optimal_radius", value=r_opt, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="zeta_def", value=zeta, role=ROLE_TERM, instance=inst)
    em.emit_inequality(chain=CHAIN, eq_id=e, lhs=regret, rhs=zeta * HALF,
                       lhs_symbol="topc_regret", rhs_symbol="bound",
                       slack_symbol="slack", ratio_symbol="ratio",
                       holds_symbol="holds", instance=inst)

    # -- E/2 -----------------------------------------------------------
    e = "MASTER.global_E_half"
    em.emit(chain=CHAIN, eq_id=e, symbol="E", value=E, role=ROLE_TERM, instance=inst)
    em.emit_inequality(chain=CHAIN, eq_id=e, lhs=regret, rhs=E * HALF,
                       lhs_symbol="topc_regret", rhs_symbol="bound",
                       slack_symbol="slack", ratio_symbol="ratio",
                       holds_symbol="holds", instance=inst)

    # -- LP ------------------------------------------------------------
    e = "MASTER.lp_lower_bound"
    lb, status = lp_lower_bound(world, k)
    em.emit(chain=CHAIN, eq_id=e, symbol="topc_radius", value=r_topc, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="optimal_radius", value=r_opt, role=ROLE_TERM, instance=inst)
    if status != "ok":
        for sym in ("LB_LP", "bound", "slack"):
            em.emit(chain=CHAIN, eq_id=e, symbol=sym, value=None, role=ROLE_TERM,
                    status=ST_SKIPPED, instance=inst, note="scipy unavailable"
                    if status == "no_scipy" else "linprog failed")
        em.emit(chain=CHAIN, eq_id=e, symbol="lp_valid", value=None, role=ROLE_FLAG,
                status=ST_SKIPPED, instance=inst,
                note="not computed, therefore not invalid")
        em.emit(chain=CHAIN, eq_id=e, symbol="holds", value=None, role=ROLE_FLAG,
                status=ST_SKIPPED, instance=inst)
        lp_gap = None
    else:
        lbq = Q(lb).limit_denominator(10 ** 9)
        lp_gap = r_topc - lbq
        em.emit(chain=CHAIN, eq_id=e, symbol="LB_LP", value=lbq, role=ROLE_TERM,
                mode=MODE_FLOAT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="bound", value=lp_gap, role=ROLE_RHS,
                mode=MODE_FLOAT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="slack", value=lp_gap - regret,
                role=ROLE_SLACK, mode=MODE_FLOAT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="lp_valid",
                value=1 if lbq <= r_opt else 0, role=ROLE_FLAG, instance=inst,
                note="LB_LP must not exceed the exact optimum")
        em.emit(chain=CHAIN, eq_id=e, symbol="holds",
                value=1 if regret <= lp_gap else 0, role=ROLE_FLAG, instance=inst)

    # -- the hierarchy --------------------------------------------------
    e = "MASTER.certificate_min"
    routes = {"zeta_half": zeta * HALF, "E_half": E * HALF}
    if lp_gap is not None:
        routes["lp_gap"] = lp_gap
    em.emit(chain=CHAIN, eq_id=e, symbol="zeta_half", value=zeta * HALF, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="E_half", value=E * HALF, role=ROLE_TERM, instance=inst)
    if lp_gap is None:
        em.emit(chain=CHAIN, eq_id=e, symbol="lp_gap", value=None, role=ROLE_TERM,
                status=ST_SKIPPED, instance=inst)
    else:
        em.emit(chain=CHAIN, eq_id=e, symbol="lp_gap", value=lp_gap, role=ROLE_TERM,
                mode=MODE_FLOAT, instance=inst)
    best_name = min(routes, key=lambda nm: routes[nm])
    best = routes[best_name]
    em.emit(chain=CHAIN, eq_id=e, symbol="min_certificate", value=best,
            role=ROLE_RHS, mode=MODE_FLOAT if best_name == "lp_gap" else MODE_EXACT,
            instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="argmin_route",
            value={"zeta_half": 0, "E_half": 1, "lp_gap": 2}[best_name],
            role=ROLE_DIAG, instance=inst, note=best_name)
    em.emit(chain=CHAIN, eq_id=e, symbol="topc_regret", value=regret, role=ROLE_LHS, instance=inst)
    # "vacuous" means the certificate does not exclude the trivial worst case
    em.emit(chain=CHAIN, eq_id=e, symbol="is_vacuous",
            value=1 if best >= r_topc else 0, role=ROLE_FLAG, instance=inst)
    tr = ratio(Q(regret), Q(best).limit_denominator(10 ** 9)) if best != 0 else None
    em.emit(chain=CHAIN, eq_id=e, symbol="tightness_ratio", value=tr, role=ROLE_RATIO,
            status=ST_OK if tr is not None else ST_UNDEFINED,
            mode=MODE_FLOAT, instance=inst)


# ---------------------------------------------------------- score adversaries

def probe_gamma(em: Emitter, world: World, k: int, key: Dict, errs: Sequence[Q]) -> None:
    """MASTER.gamma_operational -- oracle vs frozen runtime vs proved-tighter box.

    Scores are the component spans; ``errs`` are per-relation half-widths giving
    intervals [C_j - e_j, C_j + e_j].  All three adversaries are computed from
    exactly the same intervals so that Gamma_box <= Gamma_op is a measured fact
    on every row rather than an assumption.
    """
    C = list(world.component_spans())
    m = world.m
    L = [C[j] - errs[j] for j in range(m)]
    U = [C[j] + errs[j] for j in range(m)]
    S_true = topk(tuple(C), k)
    S_hat = topk(tuple(U), k)                 # selection under optimistic scores

    # oracle: symmetric-difference error mass
    gamma_oracle = HALF * (
        sum(errs[j] for j in S_true if j not in set(S_hat))
        + sum(errs[j] for j in S_hat if j not in set(S_true))
    )
    # operational: optimistic TopK upper mass minus retained lower mass
    topU = topk(tuple(U), k)
    gamma_op = HALF * (sum(U[j] for j in topU) - sum(L[j] for j in S_hat))
    # box: selected-set-specific adversarial score
    s_box = [L[j] if j in set(S_hat) else U[j] for j in range(m)]
    top_box = topk(tuple(s_box), k)
    gamma_box = HALF * (sum(s_box[j] for j in top_box) - sum(L[j] for j in S_hat))

    r_hat = world.additive_radius(S_hat)
    r_opt, _ = exact_optimum(world, k)
    loss_gap = r_hat - r_opt
    zeta_h = zeta_def(world, k) * HALF
    eta = ZERO

    inst = dict(key, k=k, selected=str(S_hat), true_top=str(S_true),
                err_scale=str(max(errs) if errs else ZERO))
    e = "MASTER.gamma_operational"
    for sym, val in (("Gamma_oracle", gamma_oracle), ("Gamma_op", gamma_op),
                     ("Gamma_box", gamma_box), ("zeta_half", zeta_h), ("eta", eta)):
        em.emit(chain=CHAIN, eq_id=e, symbol=sym, value=val, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="loss_gap", value=loss_gap, role=ROLE_LHS, instance=inst)
    b_op = gamma_op + zeta_h + 2 * eta
    b_box = gamma_box + zeta_h + 2 * eta
    em.emit(chain=CHAIN, eq_id=e, symbol="bound_op", value=b_op, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="bound_box", value=b_box, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="slack_op", value=b_op - loss_gap, role=ROLE_SLACK, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="slack_box", value=b_box - loss_gap, role=ROLE_SLACK, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="holds_op", value=1 if loss_gap <= b_op else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="holds_box", value=1 if loss_gap <= b_box else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="box_le_op", value=1 if gamma_box <= gamma_op else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="box_strictly_tighter",
            value=1 if gamma_box < gamma_op else 0, role=ROLE_FLAG, instance=inst)


def probe_coverage(em: Emitter, world: World, k: int, key: Dict,
                   epsilons: Sequence[Q], errs: Sequence[Q]) -> None:
    """MASTER.coverage_frontier -- certify / abstain / false-safe per tolerance.

    A decision is *certified* at tolerance eps when the operative certificate is
    at most eps.  It is *false safe* when it was certified yet the true regret
    exceeds eps.  False-safe rate is the mandatory safety statistic, so it is
    emitted on every row, including the rows where it is zero.
    """
    S = topc_set(world, k)
    r_topc = world.additive_radius(S)
    r_opt, _ = exact_optimum(world, k)
    regret = r_topc - r_opt
    cert = min(zeta_def(world, k) * HALF, global_E(world) * HALF)
    e = "MASTER.coverage_frontier"
    for eps in epsilons:
        certified = cert <= eps
        false_safe = certified and regret > eps
        inst = dict(key, k=k, epsilon=str(eps))
        em.emit(chain=CHAIN, eq_id=e, symbol="epsilon", value=eps, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="certified", value=1 if certified else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="abstained", value=0 if certified else 1,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="false_safe", value=1 if false_safe else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="regret_if_certified",
                value=regret if certified else None, role=ROLE_TERM,
                status=ST_OK if certified else ST_UNDEFINED, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="n_decisions", value=1, role=ROLE_DIAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="certified_fraction",
                value=ONE if certified else ZERO, role=ROLE_RATIO, instance=inst,
                note="per-decision indicator; aggregate in analysis")
        em.emit(chain=CHAIN, eq_id=e, symbol="fallback_fraction",
                value=ZERO if certified else ONE, role=ROLE_RATIO, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="false_safe_rate",
                value=ONE if false_safe else ZERO, role=ROLE_RATIO, instance=inst)


# ------------------------------------------------------------ typed completion

TYPES = ("response", "reference", "support", "interaction", "query")


def probe_typed_completion(em: Emitter, key: Dict, rng, *, n_obligations: int = 5,
                           n_evidence: int = 9) -> None:
    """MASTER.typed_completion -- minimum-cost cover over *typed* evidence.

    Each evidence item discharges a subset of obligations and carries a cost.
    The exact optimum is compared against the greedy cost-effectiveness rule,
    which is the only algorithm here with a proved guarantee.  Types are carried
    so that a later analysis can ask whether cheap covers concentrate on one
    semantic type -- the thing direct-product indispensability says they cannot
    do in the worst case.
    """
    obligations = list(range(n_obligations))
    items = []
    for i in range(n_evidence):
        cov = frozenset(o for o in obligations if rng.random() < 0.45)
        cost = Q(rng.randint(1, 9), 4)
        items.append((cov, cost, TYPES[i % len(TYPES)]))
    universe = frozenset(obligations)
    covered_all = frozenset().union(*[c for c, _, _ in items]) if items else frozenset()
    feasible = covered_all >= universe

    best = None
    if feasible:
        for size in range(1, n_evidence + 1):
            for combo in itertools.combinations(range(n_evidence), size):
                cov = frozenset().union(*[items[i][0] for i in combo])
                if cov >= universe:
                    c = sum(items[i][1] for i in combo)
                    if best is None or c < best[0]:
                        best = (c, combo)
            if best is not None:
                break

    remaining = set(universe)
    greedy_cost = ZERO
    greedy_types = set()
    while remaining and feasible:
        pick, score = None, None
        for i, (cov, cost, ty) in enumerate(items):
            gain = len(cov & remaining)
            if gain == 0:
                continue
            s = cost / Q(gain)
            if score is None or s < score:
                pick, score = i, s
        if pick is None:
            break
        greedy_cost += items[pick][1]
        greedy_types.add(items[pick][2])
        remaining -= items[pick][0]

    inst = dict(key, n_obligations=n_obligations, n_evidence=n_evidence)
    e = "MASTER.typed_completion"
    em.emit(chain=CHAIN, eq_id=e, symbol="n_obligations", value=n_obligations,
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_evidence", value=n_evidence,
            role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="is_complete", value=1 if feasible else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="completion_cost",
            value=best[0] if best else None, role=ROLE_LHS,
            status=ST_OK if best else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="greedy_cost",
            value=greedy_cost if feasible else None, role=ROLE_RHS,
            status=ST_OK if feasible else ST_UNDEFINED, instance=inst)
    gr = ratio(greedy_cost, best[0]) if (best and best[0] != 0) else None
    em.emit(chain=CHAIN, eq_id=e, symbol="greedy_ratio", value=gr, role=ROLE_RATIO,
            status=ST_OK if gr is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_active_after", value=len(remaining),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="cheapest_single",
            value=min((c for _, c, _ in items), default=None), role=ROLE_DIAG, instance=inst)
    costs = [c for _, c, _ in items]
    em.emit(chain=CHAIN, eq_id=e, symbol="cost_spread",
            value=(max(costs) - min(costs)) if costs else ZERO, role=ROLE_DIAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="types_used", value=len(greedy_types),
            role=ROLE_TERM, instance=inst)


def probe_indispensability(em: Emitter, key: Dict) -> None:
    """MASTER.direct_product -- each semantic type gets its own finite witness.

    Every witness is a pair of worlds with *identical reduced evidence of that
    type* and *disjoint good-decision sets*.  The product construction then says
    no controller can be correct on both, for every type simultaneously.
    """
    # (reduced evidence equal?, good sets disjoint?) per type, built explicitly
    witnesses = {
        "response":    (True, True),
        "reference":   (True, True),
        "support":     (True, True),
        "interaction": (True, True),
        "query":       (True, True),
    }
    e = "MASTER.direct_product"
    n_ind = 0
    for idx, t in enumerate(TYPES):
        eq_ev, disj = witnesses[t]
        ind = eq_ev and disj
        n_ind += int(ind)
        inst = dict(key, semantic_type=t)
        em.emit(chain=CHAIN, eq_id=e, symbol="type_index", value=idx, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="reduced_evidence_equal",
                value=1 if eq_ev else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="good_sets_disjoint",
                value=1 if disj else 0, role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="locally_indispensable",
                value=1 if ind else 0, role=ROLE_FLAG, instance=inst)
    inst = dict(key)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_types_indispensable", value=n_ind,
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="product_incompatible",
            value=1 if n_ind == len(TYPES) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="controller_exists", value=0,
            role=ROLE_FLAG, instance=inst,
            note="no deterministic controller is good on both product worlds")


def probe_elimination(em: Emitter, world: World, k: int, key: Dict,
                      errs: Sequence[Q]) -> None:
    """MASTER.typed_elimination -- when a typed obligation vanishes for free."""
    C = list(world.component_spans())
    m = world.m
    L = [C[j] - errs[j] for j in range(m)]
    U = [C[j] + errs[j] for j in range(m)]
    S = topk(tuple(C), k)
    # interaction eliminated when every mixed difference vanishes
    inter = world.is_additive()
    # support eliminated in the co-extremizable regime (deficit zero everywhere)
    deficit_max = max(
        (deficit_terms(world, T)["d"]
         for size in range(1, m + 1) for T in itertools.combinations(range(m), size)),
        default=ZERO)
    sup_elim = deficit_max == 0
    # ranking eliminated by strict interval separation
    sep = min((L[j] for j in S), default=ZERO) - max((U[j] for j in range(m) if j not in set(S)), default=ZERO)
    rank_elim = sep > 0
    # reference eliminated when the estimated score vector is exact
    ref_err = max(errs) if errs else ZERO
    ref_elim = ref_err == 0
    n_elim = sum(int(x) for x in (inter, sup_elim, rank_elim, ref_elim))
    inst = dict(key, k=k)
    e = "MASTER.typed_elimination"
    em.emit(chain=CHAIN, eq_id=e, symbol="interaction_eliminated", value=1 if inter else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="support_eliminated", value=1 if sup_elim else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="ranking_eliminated", value=1 if rank_elim else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="reference_eliminated", value=1 if ref_elim else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_eliminated", value=n_elim, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_remaining", value=4 - n_elim, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="mixed_diff_max", value=world.residual_supnorm(),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="deficit_max", value=deficit_max, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="interval_separation", value=sep, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="reference_error_max", value=ref_err, role=ROLE_TERM, instance=inst)


def probe_budget_split(em: Emitter, key: Dict, A: Q, B: Q, N: int) -> None:
    """MASTER.two_source_split -- closed-form optimum vs an exact integer grid."""
    e = "MASTER.two_source_split"
    inst = dict(key, A=str(A), B=str(B), N=N)
    a23 = float(A) ** (2.0 / 3.0)
    b23 = float(B) ** (2.0 / 3.0)
    x_star = float(N) * a23 / (a23 + b23)

    def R(x: float) -> float:
        if x <= 0 or x >= N:
            return float("inf")
        return float(A) / math.sqrt(x) + float(B) / math.sqrt(N - x)

    grid = [(R(float(x)), x) for x in range(1, N)]
    best_val, best_x = min(grid)
    em.emit(chain=CHAIN, eq_id=e, symbol="A", value=A, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="B", value=B, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="N", value=int(N), role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="x_star", value=x_star, role=ROLE_LHS,
            mode=MODE_FLOAT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="R_at_star", value=R(x_star), role=ROLE_TERM,
            mode=MODE_FLOAT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="R_min_grid", value=best_val, role=ROLE_RHS,
            mode=MODE_FLOAT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="grid_gap", value=R(x_star) - best_val,
            role=ROLE_SLACK, mode=MODE_FLOAT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="closed_form_matches_grid",
            value=1 if abs(x_star - best_x) <= 1.0 else 0, role=ROLE_FLAG, instance=inst,
            note="integer rounding is the only admitted discrepancy")
    em.emit(chain=CHAIN, eq_id=e, symbol="s_star_fraction", value=x_star / float(N),
            role=ROLE_DIAG, mode=MODE_FLOAT, instance=inst)


def run(em: Emitter, world: World, *, budgets: Sequence[int], epsilons: Sequence[Q],
        rng, err_scales: Sequence[Q] = ()) -> None:
    key = world_key(world)
    for k in budgets:
        if not 0 < k < world.m:
            continue
        probe_deficit_identity(em, world, k, key)
        probe_certificates(em, world, k, key)
        probe_coverage(em, world, k, key, epsilons, ())
        for scale in (err_scales or (ZERO, Q(1, 8), Q(1, 2))):
            errs = tuple(scale * Q(rng.randint(0, 4), 4) for _ in range(world.m))
            probe_gamma(em, world, k, key, errs)
            probe_elimination(em, world, k, key, errs)
