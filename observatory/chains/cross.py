"""Cross-chain probe: the structural separations that only show up when the
chains are measured on the *same* world.
"""
from __future__ import annotations

import itertools
from typing import Dict, Sequence

from ..exact import Q, ZERO, ONE, HALF, ratio
from ..schema import (Emitter, ROLE_INPUT, ROLE_TERM, ROLE_LHS, ROLE_RHS,
                      ROLE_SLACK, ROLE_RATIO, ROLE_FLAG, ROLE_DIAG,
                      ST_OK, ST_UNDEFINED, ST_SKIPPED)
from ..worlds import World
from ._common import (exact_optimum, topc_set, zeta_def, global_E,
                      co_extremizable, world_key)

CHAIN = "CROSS"


def probe_separation(em: Emitter, world: World, key: Dict) -> None:
    """X.interaction_vs_support -- the two axes are independent, measured.

    The quadrant label is the point: 'additive yet coupled' and 'interacting yet
    Cartesian' both have to be populated for the separation to be more than an
    assertion, and any world that lands in a quadrant the theory says is
    reachable is evidence; an empty quadrant across a large sweep is a finding
    in its own right.
    """
    e = "X.interaction_vs_support"
    coext = co_extremizable(world)
    additive = world.is_additive()
    cart = world.support.is_cartesian
    delta = None
    if cart:
        try:
            delta = world.delta_square()
        except Exception:
            delta = None
    inst = dict(key)
    em.emit(chain=CHAIN, eq_id=e, symbol="residual_supnorm", value=world.residual_supnorm(),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="delta_square", value=delta, role=ROLE_TERM,
            status=ST_OK if delta is not None else ST_SKIPPED, instance=inst,
            note="" if delta is not None else "non-Cartesian support: delta undefined")
    em.emit(chain=CHAIN, eq_id=e, symbol="co_extremizable", value=1 if coext else 0,
            role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="support_density", value=world.support.density(),
            role=ROLE_TERM, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="additive_and_coupled",
            value=1 if (additive and not coext) else 0, role=ROLE_FLAG, instance=inst)
    em.emit(chain=CHAIN, eq_id=e, symbol="interacting_and_cartesian",
            value=1 if ((not additive) and cart) else 0, role=ROLE_FLAG, instance=inst)
    quadrant = (0 if additive else 2) + (0 if coext else 1)
    em.emit(chain=CHAIN, eq_id=e, symbol="quadrant", value=quadrant, role=ROLE_DIAG,
            instance=inst,
            note="0 additive+coext, 1 additive+coupled, 2 interacting+coext, 3 both")


def probe_route_coverage(em: Emitter, world: World, key: Dict,
                         budgets: Sequence[int], epsilons: Sequence[Q]) -> None:
    """X.certificate_coverage -- one row per (route, tolerance) with its verdict."""
    e = "X.certificate_coverage"
    meta = dict(world.meta or {})
    for k in budgets:
        if not 0 < k < world.m:
            continue
        S = topc_set(world, k)
        r_topc = world.additive_radius(S)
        r_opt, _ = exact_optimum(world, k)
        regret = r_topc - r_opt
        routes = {"zeta_half": zeta_def(world, k) * HALF,
                  "E_half": global_E(world) * HALF}
        for rname, cert in routes.items():
            for eps in epsilons:
                fires = cert <= eps
                inst = dict(key, k=k, route=rname, epsilon=str(eps))
                em.emit(chain=CHAIN, eq_id=e, symbol="route",
                        value={"zeta_half": 0, "E_half": 1}[rname], role=ROLE_DIAG,
                        instance=inst, note=rname)
                em.emit(chain=CHAIN, eq_id=e, symbol="family", value=0, role=ROLE_DIAG,
                        instance=inst, note=str(meta.get("family", "unknown")))
                em.emit(chain=CHAIN, eq_id=e, symbol="m", value=world.m, role=ROLE_INPUT, instance=inst)
                em.emit(chain=CHAIN, eq_id=e, symbol="epsilon", value=eps, role=ROLE_INPUT, instance=inst)
                em.emit(chain=CHAIN, eq_id=e, symbol="fires", value=1 if fires else 0,
                        role=ROLE_FLAG, instance=inst)
                em.emit(chain=CHAIN, eq_id=e, symbol="vacuous",
                        value=1 if cert >= r_topc else 0, role=ROLE_FLAG, instance=inst)
                em.emit(chain=CHAIN, eq_id=e, symbol="correct",
                        value=1 if regret <= cert else 0, role=ROLE_FLAG, instance=inst)
                em.emit(chain=CHAIN, eq_id=e, symbol="false_safe",
                        value=1 if (fires and regret > eps) else 0, role=ROLE_FLAG, instance=inst)
                em.emit(chain=CHAIN, eq_id=e, symbol="mean_slack", value=cert - regret,
                        role=ROLE_SLACK, instance=inst)
                em.emit(chain=CHAIN, eq_id=e, symbol="median_slack", value=cert - regret,
                        role=ROLE_SLACK, instance=inst,
                        note="per-instance slack; the median is taken across instances")
                em.emit(chain=CHAIN, eq_id=e, symbol="coverage",
                        value=ONE if fires else ZERO, role=ROLE_RATIO, instance=inst,
                        note="per-instance indicator; aggregate in analysis")


def run(em: Emitter, world: World, *, budgets: Sequence[Q], epsilons: Sequence[Q]) -> None:
    key = world_key(world)
    probe_separation(em, world, key)
    probe_route_coverage(em, world, key, budgets, epsilons)
