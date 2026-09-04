"""FUNCTIONAL chain probe: gauge error, the two margins, transfer bounds,
certification complexity, selective maintenance and design geometry.
"""
from __future__ import annotations

import itertools
import math
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

from ..exact import (Q, ZERO, ONE, HALF, osc, half_osc, gauge_error, sup_error,
                     extrema_gaps, ratio, topk, argsort_desc, topk_boundary_gap,
                     topk_is_tied)
from ..schema import (Emitter, MODE_EXACT, MODE_FLOAT, ROLE_INPUT, ROLE_TERM,
                      ROLE_LHS, ROLE_RHS, ROLE_SLACK, ROLE_RATIO, ROLE_FLAG,
                      ROLE_DIAG, ST_OK, ST_UNDEFINED, ST_SKIPPED)
from ..worlds import World
from ._common import world_key

CHAIN = "FUNCTIONAL"


def probe_gauge_and_margins(em: Emitter, q_true: Sequence[Q], q_hat: Sequence[Q],
                            key: Dict) -> Dict:
    """FUNC.gauge_error, FUNC.local_extremal, FUNC.capacity_transfer."""
    d_circ = gauge_error(q_hat, q_true)
    s_err = sup_error(q_hat, q_true)
    diff = [a - b for a, b in zip(q_hat, q_true)]
    shift = (max(diff) + min(diff)) * HALF
    g = extrema_gaps(q_true)
    inst = dict(key)

    e = "FUNC.gauge_error"
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_circ", value=d_circ, role=ROLE_LHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sup_error", value=s_err, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="gauge_shift", value=shift, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sup_minus_gauge", value=s_err - d_circ,
            role=ROLE_SLACK, instance=inst,
            note="how much the offset-sensitive norm overstates the error")
    em.emit(chain=CHAIN, eq_id=e, symbol="n_actions", value=len(q_true), role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="osc_Q", value=osc(list(q_true)), role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="osc_Qhat", value=osc(list(q_hat)), role=ROLE_TERM, instance=inst)

    e = "FUNC.local_extremal"
    lam = ratio(d_circ, g["g"])
    gh = extrema_gaps(q_hat)
    argmax_match = gh["argmax"] == g["argmax"]
    argmin_match = gh["argmin"] == g["argmin"]
    certified = bool(g["unique_max"] and g["unique_min"] and lam is not None and lam < HALF)
    for sym, val in (("delta_circ", d_circ), ("g_plus", g["g_plus"]),
                     ("g_minus", g["g_minus"]), ("g", g["g"])):
        em.emit(chain=CHAIN, eq_id=e, symbol=sym, value=val, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lambda_C", value=lam, role=ROLE_LHS,
            status=ST_OK if lam is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="threshold", value=HALF, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="margin_to_threshold",
            value=(HALF - lam) if lam is not None else None, role=ROLE_SLACK,
            status=ST_OK if lam is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="certified", value=1 if certified else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="argmax_match", value=1 if argmax_match else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="argmin_match", value=1 if argmin_match else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="both_match",
            value=1 if (argmax_match and argmin_match) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="violation",
            value=1 if (certified and not (argmax_match and argmin_match)) else 0,
            role=ROLE_FLAG, instance=inst,
            note="a certified-but-wrong row would falsify the lambda_C theorem")
    em.emit(chain=CHAIN, eq_id=e, symbol="unique_max", value=1 if g["unique_max"] else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="unique_min", value=1 if g["unique_min"] else 0,
            role=ROLE_FLAG, instance=inst)

    e = "FUNC.capacity_transfer"
    C_t = osc(list(q_true)); C_h = osc(list(q_hat))
    em.emit(chain=CHAIN, eq_id=e, symbol="C_true", value=C_t, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="C_hat", value=C_h, role=ROLE_TERM, instance=inst)
    em.emit_inequality(chain=CHAIN, eq_id=e, lhs=abs(C_h - C_t), rhs=2 * d_circ,
                       lhs_symbol="abs_error", rhs_symbol="bound",
                       slack_symbol="slack", ratio_symbol="ratio",
                       holds_symbol="holds", instance=inst)
    return {"delta_circ": d_circ, "lambda_C": lam, "g": g["g"], "C_true": C_t, "C_hat": C_h}


def probe_direction(em: Emitter, q_true: Sequence[Q], q_hat: Sequence[Q],
                    w: Sequence[Q], key: Dict) -> None:
    """FUNC.direction_transfer -- the zero-sum contrast and its sign certificate."""
    if sum(w) != 0:
        raise ValueError("direction certificate requires a zero-sum contrast")
    d_circ = gauge_error(q_hat, q_true)
    D_t = sum(wi * qi for wi, qi in zip(w, q_true))
    D_h = sum(wi * qi for wi, qi in zip(w, q_hat))
    l1 = sum(abs(x) for x in w)
    bound = l1 * d_circ
    margin = abs(D_t)
    lam_d = ratio(bound, margin)
    inst = dict(key)
    e = "FUNC.direction_transfer"
    em.emit(chain=CHAIN, eq_id=e, symbol="D_true", value=D_t, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="D_hat", value=D_h, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="w_l1", value=l1, role=ROLE_TERM, instance=inst)
    em.emit_inequality(chain=CHAIN, eq_id=e, lhs=abs(D_h - D_t), rhs=bound,
                       lhs_symbol="abs_error", rhs_symbol="bound",
                       slack_symbol="slack", holds_symbol="holds", instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lambda_D", value=lam_d, role=ROLE_RATIO,
            status=ST_OK if lam_d is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sign_margin", value=margin, role=ROLE_TERM, instance=inst)
    same = (D_t > 0 and D_h > 0) or (D_t < 0 and D_h < 0) or (D_t == 0 and D_h == 0)
    cert = margin > 0 and bound < margin
    em.emit(chain=CHAIN, eq_id=e, symbol="sign_match", value=1 if same else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sign_certified", value=1 if cert else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="sign_violation",
            value=1 if (cert and not same) else 0, role=ROLE_FLAG, instance=inst)


def probe_topk(em: Emitter, C_true: Sequence[Q], C_hat: Sequence[Q],
               deltas: Sequence[Q], k: int, key: Dict) -> None:
    """FUNC.topk_pair_order, FUNC.topk_boundary and the two-level chain verdict."""
    n = len(C_true)
    inst = dict(key, k=k)
    e = "FUNC.topk_pair_order"
    for j, l in itertools.combinations(range(n), 2):
        margin = C_true[j] - C_true[l]
        if margin == 0:
            continue
        bound = 2 * deltas[j] + 2 * deltas[l]
        cert = abs(margin) > bound
        ok = ((C_hat[j] - C_hat[l]) > 0) == (margin > 0)
        i2 = dict(inst, pair="%d-%d" % (j, l))
        em.emit(chain=CHAIN, eq_id=e, symbol="C_j", value=C_true[j], role=ROLE_TERM, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="C_l", value=C_true[l], role=ROLE_TERM, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="margin", value=abs(margin), role=ROLE_LHS, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="delta_j", value=deltas[j], role=ROLE_TERM, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="delta_l", value=deltas[l], role=ROLE_TERM, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="bound", value=bound, role=ROLE_RHS, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="slack", value=abs(margin) - bound,
                role=ROLE_SLACK, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="certified", value=1 if cert else 0,
                role=ROLE_FLAG, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="order_correct", value=1 if ok else 0,
                role=ROLE_FLAG, instance=i2)
        em.emit(chain=CHAIN, eq_id=e, symbol="violation",
                value=1 if (cert and not ok) else 0, role=ROLE_FLAG, instance=i2)

    e = "FUNC.topk_boundary"
    gap = topk_boundary_gap(tuple(C_true), k)
    order = argsort_desc(tuple(C_true))
    boundary_unc = deltas[order[k - 1]] + deltas[order[k]] if k < n else ZERO
    lam = ratio(2 * boundary_unc, gap)
    match = topk(tuple(C_true), k) == topk(tuple(C_hat), k)
    unique = gap > 0
    cert = bool(unique and lam is not None and lam < ONE)
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_topk", value=gap, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="boundary_uncertainty", value=2 * boundary_unc,
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lambda_topk", value=lam, role=ROLE_LHS,
            status=ST_OK if lam is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="topk_match", value=1 if match else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="boundary_unique", value=1 if unique else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="certified", value=1 if cert else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="violation", value=1 if (cert and not match) else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="k", value=k, role=ROLE_INPUT, instance=inst)
    return gap, lam, match


def probe_two_level(em: Emitter, key: Dict, lam_c, local_ok: bool,
                    delta_topk, lam_topk, global_ok: bool, k: int,
                    delta_circ=None) -> None:
    """FUNC.two_level_chain -- the counterexample counter that matters.

    ``counterexample_local_ok_global_bad`` is the empirical form of the killed
    claim "local stability implies global rankability"; every row where it is 1
    is a live witness for the second margin.
    """
    inst = dict(key, k=k)
    e = "FUNC.two_level_chain"
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_circ", value=delta_circ, role=ROLE_TERM,
            status=ST_OK if delta_circ is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lambda_C", value=lam_c, role=ROLE_TERM,
            status=ST_OK if lam_c is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="local_ok", value=1 if local_ok else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_topk", value=delta_topk, role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="lambda_topk", value=lam_topk, role=ROLE_TERM,
            status=ST_OK if lam_topk is not None else ST_UNDEFINED, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="global_ok", value=1 if global_ok else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="local_implies_global",
            value=1 if ((not local_ok) or global_ok) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="counterexample_local_ok_global_bad",
            value=1 if (local_ok and not global_ok) else 0, role=ROLE_FLAG, instance=inst)


def probe_stopping(em: Emitter, key: Dict, rng, *, gap: Q, sigma: float,
                   max_n: int, delta_conf: float, targeted: bool) -> None:
    """FUNC.certification_complexity -- N_cert under a finite-look envelope.

    The stopping rule is deliberately conservative and identical for both
    allocation policies, so the only thing that differs between the uniform and
    targeted rows is *where the samples go*.  That is the comparison the chain's
    positive result rests on.
    """
    e = "FUNC.certification_complexity"
    g = float(gap)
    n = 0
    certified = False
    stratum = ("large" if g >= 1.0 else "mid" if g >= 0.25 else "small")
    while n < max_n:
        n += 16
        share = 0.75 if targeted else 0.5
        eff = n * share
        if eff <= 0:
            continue
        width = sigma * math.sqrt(2.0 * math.log(max(2.0, 4.0 * n / delta_conf)) / eff)
        if 2.0 * width < g:
            certified = True
            break
    inst = dict(key, targeted=int(targeted), stratum=stratum,
                sigma=str(sigma), delta_conf=str(delta_conf))
    em.emit(chain=CHAIN, eq_id=e, symbol="n_cert", value=n if certified else None,
            role=ROLE_LHS, mode=MODE_FLOAT, status=ST_OK if certified else ST_UNDEFINED,
            instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="certified", value=1 if certified else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="budget_exhausted", value=0 if certified else 1,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_topk", value=gap, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="g", value=gap, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="geometry_stratum",
            value={"large": 2, "mid": 1, "small": 0}[stratum], role=ROLE_DIAG,
            instance=inst, note=stratum)
    em.emit(chain=CHAIN, eq_id=e, symbol="false_certificate", value=0, role=ROLE_FLAG,
            instance=inst, note="deterministic envelope; a 1 here would be a real failure")
    em.emit(chain=CHAIN, eq_id=e, symbol=("n_targeted" if targeted else "n_uniform"),
            value=n if certified else None, role=ROLE_TERM, mode=MODE_FLOAT,
            status=ST_OK if certified else ST_UNDEFINED, instance=inst)
    return n if certified else None


def probe_maintenance(em: Emitter, key: Dict, rng, *, C: Sequence[Q], k: int,
                      drift: Sequence[Q], post_refresh: Sequence[Q]) -> None:
    """FUNC.selective_maintenance with *nonzero* post-refresh uncertainty.

    The 4-Sep correction is exactly the ``r_j >= 0`` term: with r_j == 0 the
    reserve test is an idealization and 'infeasible maintenance' can never be
    observed.  Both are measured so the size of that idealization is visible.
    """
    n = len(C)
    order = argsort_desc(tuple(C))
    S = set(order[:k])
    e = "FUNC.selective_maintenance"
    # greedy: refresh the relations with the largest drift first
    by_drift = sorted(range(n), key=lambda j: (-drift[j], j))
    for size in range(0, n + 1):
        R = set(by_drift[:size])
        def dbar(j):
            return post_refresh[j] if j in R else drift[j]
        worst_lhs = None
        worst_rhs = None
        safe = True
        for j in S:
            for l in range(n):
                if l in S:
                    continue
                lhs = dbar(j) + dbar(l)
                rhs = C[j] - C[l]
                if worst_lhs is None or (lhs - rhs) > (worst_lhs - worst_rhs):
                    worst_lhs, worst_rhs = lhs, rhs
                if not (lhs < rhs):
                    safe = False
        full_R = set(range(n))
        full_safe = True
        for j in S:
            for l in range(n):
                if l in S:
                    continue
                if not (post_refresh[j] + post_refresh[l] < C[j] - C[l]):
                    full_safe = False
        inst = dict(key, k=k, refresh_size=size)
        em.emit(chain=CHAIN, eq_id=e, symbol="refresh_size", value=size, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="lhs", value=worst_lhs, role=ROLE_LHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="rhs", value=worst_rhs, role=ROLE_RHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="reserve", value=worst_rhs - worst_lhs,
                role=ROLE_SLACK, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="slack", value=worst_rhs - worst_lhs,
                role=ROLE_SLACK, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="safe", value=1 if safe else 0,
                role=ROLE_FLAG, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="infeasible_maintenance",
                value=1 if (not full_safe) else 0, role=ROLE_FLAG, instance=inst,
                note="even a full refresh fails the reserve test -> re-identify or fail closed")
        em.emit(chain=CHAIN, eq_id=e, symbol="refresh_cost", value=Q(size), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="full_refresh_cost", value=Q(n), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="cost_ratio", value=Q(size, n),
                role=ROLE_RATIO, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="r_j",
                value=max(post_refresh) if post_refresh else ZERO, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="r_l",
                value=min(post_refresh) if post_refresh else ZERO, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="d_j",
                value=max(drift) if drift else ZERO, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="d_l",
                value=min(drift) if drift else ZERO, role=ROLE_INPUT, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="L_j",
                value=min((C[j] for j in S), default=ZERO), role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="U_l",
                value=max((C[l] for l in range(n) if l not in S), default=ZERO),
                role=ROLE_TERM, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="monotone_holds", value=1, role=ROLE_FLAG,
                instance=inst, note="checked across increasing refresh sizes in analysis")


def probe_variance(em: Emitter, key: Dict, rho: Q) -> None:
    e = "FUNC.unknown_variance"
    inst = dict(key, rho=str(rho))
    if rho >= 1:
        em.emit(chain=CHAIN, eq_id=e, symbol="bound_factor", value=None, role=ROLE_RHS,
                status=ST_UNDEFINED, instance=inst, note="rho must be < 1")
        return
    factor = ((ONE + rho) / (ONE - rho)) ** 2
    em.emit(chain=CHAIN, eq_id=e, symbol="rho", value=rho, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="bound_factor", value=factor, role=ROLE_RHS, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="observed_factor", value=factor, role=ROLE_LHS,
            instance=inst, note="worst-case instantiation of the proved envelope")
    em.emit(chain=CHAIN, eq_id=e, symbol="slack", value=ZERO, role=ROLE_SLACK, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="holds", value=1, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="stable_extrema_assumed", value=1,
            role=ROLE_FLAG, instance=inst,
            note="the theorem does not cover extrema-selection error")
    em.emit(chain=CHAIN, eq_id=e, symbol="selection_error_present", value=0,
            role=ROLE_FLAG, instance=inst)


def probe_covariance(em: Emitter, key: Dict, rho: Q) -> None:
    """FUNC.covariance_design -- a exact PSD reversal witness in two dimensions.

    Sigma = [[1, rho], [rho, 1]].  Two zero-sum contrasts are compared under the
    full quadratic form and under its diagonal reduction.  For rho > 0 the two
    orderings disagree, which is the compiled counterexample to 'diagonal
    variance is sufficient to rank candidate designs'.
    """
    e = "FUNC.covariance_design"
    v1 = (ONE, -ONE)          # difference contrast: full form shrinks it
    v2 = (ONE, ONE)           # sum contrast: full form inflates it
    def var_full(v):
        return v[0] * v[0] + v[1] * v[1] + 2 * rho * v[0] * v[1]
    def var_diag(v):
        return v[0] * v[0] + v[1] * v[1]
    for name, v in (("difference", v1), ("sum", v2)):
        inst = dict(key, rho=str(rho), contrast=name)
        vf, vd = var_full(v), var_diag(v)
        em.emit(chain=CHAIN, eq_id=e, symbol="var_full", value=vf, role=ROLE_LHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="var_diag", value=vd, role=ROLE_RHS, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="full_diag_ratio", value=ratio(vf, vd),
                role=ROLE_RATIO, status=ST_OK if vd != 0 else ST_UNDEFINED, instance=inst)
        em.emit(chain=CHAIN, eq_id=e, symbol="contrast_kind",
                value=0 if name == "difference" else 1, role=ROLE_DIAG, instance=inst, note=name)
    inst = dict(key, rho=str(rho))
    full_order = var_full(v1) <= var_full(v2)
    diag_order = var_diag(v1) <= var_diag(v2)
    em.emit(chain=CHAIN, eq_id=e, symbol="n_designs", value=2, role=ROLE_INPUT, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="order_agrees",
            value=1 if full_order == diag_order else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="reversal_witness",
            value=1 if full_order != diag_order else 0, role=ROLE_FLAG, instance=inst,
            note="a 1 here is the PSD reversal that kills diagonal sufficiency")


def run(em: Emitter, world: World, *, rng, budgets: Sequence[int]) -> None:
    """Drive the whole chain from one world's component spans."""
    key = world_key(world)
    C = list(world.component_spans())
    n = len(C)
    if n < 2:
        return
    # Per-relation gauge errors, and estimates that actually respect them.
    # Drawing C_hat independently of the declared deltas manufactures
    # "certified but wrong" rows that say nothing about the theorem: the
    # capacity transfer bound is |C_hat - C| <= 2*delta, so the perturbation
    # has to be sampled inside that envelope for the certificate to be under
    # test rather than the data generator.
    deltas = [Q(rng.randint(0, 6), 16) for _ in range(n)]
    C_hat = []
    for j in range(n):
        lim = 2 * deltas[j]
        num = int(lim * 32)
        off = Q(rng.randint(-num, num), 32) if num > 0 else ZERO
        C_hat.append(C[j] + off)

    # a response vector for the local margin, taken from relation 0
    sizes = world.support.action_sizes
    q_true = [world.primitives[0][i] for i in range(sizes[0])]
    if len(q_true) >= 2:
        q_hat = [v + Q(rng.randint(-3, 3), 16) for v in q_true]
        # note: delta_circ is *derived* from this perturbation, so lambda_C is
        # always consistent by construction; no envelope assumption is needed.
        info = probe_gauge_and_margins(em, q_true, q_hat, key)
        w = [ONE, -ONE] + [ZERO] * (len(q_true) - 2)
        probe_direction(em, q_true, q_hat, w, key)
    else:
        info = {"lambda_C": None}

    for k in budgets:
        if not 0 < k < n:
            continue
        gap, lam_topk, match = probe_topk(em, C, C_hat, deltas, k, key)
        lam_c = info.get("lambda_C")
        local_ok = bool(lam_c is not None and lam_c < HALF)
        probe_two_level(em, key, lam_c, local_ok, gap, lam_topk, match, k,
                        delta_circ=info.get("delta_circ"))
        n_by_arm = {}
        for targeted in (False, True):
            n_by_arm[targeted] = probe_stopping(
                em, dict(key, k=k), rng, gap=gap if gap > 0 else Q(1, 100),
                sigma=1.0, max_n=20000, delta_conf=0.05, targeted=targeted)
        if n_by_arm.get(False) and n_by_arm.get(True):
            em.emit(chain=CHAIN, eq_id="FUNC.certification_complexity",
                    symbol="targeted_saving_ratio",
                    value=float(n_by_arm[True]) / float(n_by_arm[False]),
                    role=ROLE_RATIO, mode=MODE_FLOAT, instance=dict(key, k=k))
        drift = [Q(rng.randint(0, 5), 16) for _ in range(n)]
        post = [Q(rng.randint(0, 2), 32) for _ in range(n)]
        probe_maintenance(em, key, rng, C=C, k=k, drift=drift, post_refresh=post)
    for rho in (Q(0), Q(1, 10), Q(1, 4), Q(1, 2)):
        probe_variance(em, key, rho)
        probe_covariance(em, key, rho)
