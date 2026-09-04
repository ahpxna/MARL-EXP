"""Shared exact computations used by more than one chain probe."""
from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, Iterable, List, Sequence, Tuple

from ..exact import Q, ZERO, ONE, HALF, osc, half_osc, topk, argsort_desc, subsets, complement
from ..worlds import Support, World, Action


def exact_optimum(world: World, k: int, *, true_loss: bool = False,
                  support: Support | None = None):
    """Exact minimum radius at budget k, plus every optimal retained set.

    Ties are collected, not broken: the Structural chain's whole question is
    whether optima at different budgets can be nested, and that is meaningless
    if a tie is silently resolved.
    """
    m = world.m
    k = int(k)
    if not 0 <= k <= m:
        raise ValueError("budget out of range")
    obj = world.true_compression_loss if true_loss else world.additive_radius
    best = None
    opts: List[Tuple[int, ...]] = []
    for S in itertools.combinations(range(m), k):
        v = obj(S, support)
        if best is None or v < best:
            best, opts = v, [S]
        elif v == best:
            opts.append(S)
    return best, tuple(opts)


def topc_set(world: World, k: int, support: Support | None = None) -> Tuple[int, ...]:
    """Marginal Top-C: keep the k largest component spans (index tie-break)."""
    spans = world.component_spans(support)
    return topk(spans, int(k))


def deficit_terms(world: World, omitted: Iterable[int], support: Support | None = None):
    """M(T), F_Omega(T), d = M - F, and the one-sided failures e_plus, e_minus."""
    sup = support or world.support
    T = tuple(sorted({int(j) for j in omitted}))
    if not T:
        return {"M": ZERO, "F": ZERO, "d": ZERO, "e_plus": ZERO, "e_minus": ZERO}
    maxs, mins = {}, {}
    for j in T:
        idx = sup.projection(j)
        vals = [world.primitives[j][i] for i in idx]
        maxs[j], mins[j] = max(vals), min(vals)
    sums = [sum(world.primitives[j][a[j]] for j in T) for a in sup.omega]
    F = osc(sums)
    M = sum(maxs[j] - mins[j] for j in T)
    e_plus = min(sum(maxs[j] - world.primitives[j][a[j]] for j in T) for a in sup.omega)
    e_minus = min(sum(world.primitives[j][a[j]] - mins[j] for j in T) for a in sup.omega)
    return {"M": M, "F": F, "d": M - F, "e_plus": e_plus, "e_minus": e_minus}


def zeta_def(world: World, k: int, support: Support | None = None) -> Q:
    """zeta_k^def = max over omitted sets of size m-k of the exact deficit."""
    m = world.m
    size = m - int(k)
    if size <= 0:
        return ZERO
    return max(deficit_terms(world, T, support)["d"]
               for T in itertools.combinations(range(m), size))


def global_E(world: World, support: Support | None = None) -> Q:
    t = deficit_terms(world, range(world.m), support)
    return t["e_plus"] + t["e_minus"]


def co_extremizable(world: World, support: Support | None = None) -> bool:
    """True when some feasible action attains every component maximum at once
    and some feasible action attains every component minimum at once."""
    sup = support or world.support
    hit_max = False
    hit_min = False
    maxs, mins = [], []
    for j in range(world.m):
        idx = sup.projection(j)
        vals = [world.primitives[j][i] for i in idx]
        maxs.append(max(vals)); mins.append(min(vals))
    for a in sup.omega:
        if all(world.primitives[j][a[j]] == maxs[j] for j in range(world.m)):
            hit_max = True
        if all(world.primitives[j][a[j]] == mins[j] for j in range(world.m)):
            hit_min = True
        if hit_max and hit_min:
            return True
    return False


def all_subsets_modular(world: World, support: Support | None = None):
    """Check r_Omega(S) == (1/2) sum_{j not in S} C_j for every subset.

    Returns (holds, worst_gap, n_checked).  The worst gap is a number, not a
    boolean, because the size of the failure is what separates "coupled a
    little" from "coupled decisively".
    """
    sup = support or world.support
    spans = world.component_spans(sup)
    worst = ZERO
    n = 0
    for k in range(world.m + 1):
        for S in itertools.combinations(range(world.m), k):
            n += 1
            exact = world.additive_radius(S, sup)
            modular = HALF * sum(spans[j] for j in range(world.m) if j not in set(S))
            gap = modular - exact
            if abs(gap) > abs(worst):
                worst = gap
    return worst == 0, worst, n


OMEGA_SQUARED_CAP = 4096   # |Omega|^2 work units a single probe may spend


def max_of_modular_value(world: World, S: Iterable[int], support: Support | None = None):
    """2 r_Omega(S) as max over ordered feasible pairs of a modular scenario."""
    sup = support or world.support
    if len(sup.omega) ** 2 > OMEGA_SQUARED_CAP:
        return None, None, len(sup.omega) ** 2
    keep = set(int(j) for j in S)
    best = None
    arg = None
    n = 0
    for a in sup.omega:
        for b in sup.omega:
            n += 1
            val = sum(
                world.primitives[j][a[j]] - world.primitives[j][b[j]]
                for j in range(world.m) if j not in keep
            )
            if best is None or val > best:
                best, arg = val, (a, b)
    return best, arg, n


def eps_good_sets(world: World, k: int, epsilon: Q, support: Support | None = None):
    """Every retained set whose radius is within epsilon of the optimum."""
    opt, _ = exact_optimum(world, k, support=support)
    good = []
    for S in itertools.combinations(range(world.m), int(k)):
        if world.additive_radius(S, support) - opt <= epsilon:
            good.append(S)
    return opt, tuple(good)


# ------------------------------------------------------------- LP (optional)

def lp_lower_bound(world: World, k: int, support: Support | None = None):
    """Continuous relaxation lower bound; requires scipy.

    Returned as ``(value, status)`` where status is one of 'ok', 'no_scipy',
    'failed'.  The observatory never silently substitutes a different bound.
    """
    try:
        import numpy as np
        from scipy.optimize import linprog
    except Exception:
        return None, "no_scipy"
    sup = support or world.support
    m = world.m
    nvar = m + 2
    c = np.zeros(nvar); c[m] = 0.5; c[m + 1] = -0.5
    A_ub, b_ub = [], []
    for a in sup.omega:
        row_f = np.array([float(world.primitives[j][a[j]]) for j in range(m)])
        total = float(row_f.sum())
        r = np.zeros(nvar); r[:m] = -row_f; r[m] = -1.0
        A_ub.append(r); b_ub.append(-total)
        r = np.zeros(nvar); r[:m] = row_f; r[m + 1] = 1.0
        A_ub.append(r); b_ub.append(total)
    A_eq = np.zeros((1, nvar)); A_eq[0, :m] = 1.0
    try:
        res = linprog(c, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                      A_eq=A_eq, b_eq=np.array([float(k)]),
                      bounds=[(0.0, 1.0)] * m + [(None, None)] * 2, method="highs")
    except Exception:
        return None, "failed"
    if not res.success or res.fun is None:
        return None, "failed"
    return max(0.0, float(res.fun)), "ok"


# ---------------------------------------------------------- instance keys

def world_key(world: World, **extra) -> Dict[str, object]:
    """The instance key stamped on every row produced from this world."""
    meta = dict(world.meta or {})
    key = {
        "world_id": world.content_id(),
        "family": meta.get("family", "unknown"),
        "m": world.m,
        "arity": meta.get("arity", max(world.support.action_sizes)),
        "omega_size": len(world.support.omega),
        "omega_full": world.support.n_full,
        "cartesian": int(world.support.is_cartesian),
        "additive": int(world.is_additive()),
    }
    for k, v in meta.items():
        if k not in key and k != "family":
            key["w_" + str(k)] = v
    key.update(extra)
    return key
