"""FUNCTIONAL: how badly does the scalar proxy mislead on instances nobody built?

The paper separates J_full from J_scalar with two hand-built families, one in
each direction, and that is enough to refute any constant correction factor. It
leaves a different question open, and it is the one a practitioner asks: on an
instance that was not built to break the proxy, how often and by how much is the
proxy wrong, and is the error predicted by the mechanism the families exploit?

Transcription.  A relation's capacity is the range of its response row,
C_r = max_a theta_{r,a} - min_a theta_{r,a}.  The scalar proxy freezes the four
extremal cells and drops the ordering constraints,

    J_scalar = (C_i - C_j)^2 / (2 (1/alpha_{i,a*} + 1/alpha_{i,b*}
                                 + 1/alpha_{j,c*} + 1/alpha_{j,d*})).

The true value is the least energy of a capacity-inverting alternative,

    J_full = min { (1/2) sum_{r,a} alpha_{r,a} (lambda_{r,a} - theta_{r,a})^2
                 : C_i(lambda) <= C_j(lambda) }.

It is computed exactly rather than by a general-purpose optimiser, using the
decomposition the paper's own inner problem exhibits.  Fix a target width z.
Relation i must fit inside a window of width z, which costs S_i(z) -- optimally
clip every cell into some window [l, l+z] and minimise over l, a one-dimensional
convex problem whose breakpoints are the cells themselves.  Relation j must open
some pair (c,d) to width at least z, which for a fixed pair costs
(1/2)[z - (theta_c - theta_d)]_+^2 * alpha_c alpha_d / (alpha_c + alpha_d),
splitting the move between the two cells in inverse proportion to precision.
Both are convex in z for a fixed pair, so the sum is convex and a golden-section
refinement is exact within its bracket; J_full is the minimum over pairs. S_i(z)
itself is solved in closed form: its derivative in the window position is
piecewise linear, so the minimiser is a root on one of the intervals between
breakpoints, and is generally interior rather than at a breakpoint.

Self-checks, which must pass before any sweep result is reported.  On the two
proved families the transcription must reproduce the proved numbers: family 1
must give J_scalar = 1/32 and J_full <= 9 eta / 32, and family 2 must give
J_scalar = eta/(8(1+3eta)) and J_full >= 1/128.  The solver is additionally
checked against SLSQP running on the raw variables, which uses none of the
decomposition; a local optimiser can only land at or above the true minimum, so
any cell where it lands below would be a defect in the decomposition and is
counted rather than averaged away.
"""
import json
import time
import math
import argparse
from pathlib import Path

import numpy as np

import os as _os, sys as _sys
_sys.path.insert(0, _os.path.dirname(_os.path.abspath(__file__)))
import EXP_provenance as _P

MASTER_SEED = 20260916
GOLD = (math.sqrt(5) - 1) / 2


def capacity(theta):
    return float(theta.max() - theta.min())


def j_scalar(ti, ai, tj, aj):
    Ci, Cj = capacity(ti), capacity(tj)
    inv = (1.0 / ai[int(np.argmax(ti))] + 1.0 / ai[int(np.argmin(ti))]
           + 1.0 / aj[int(np.argmax(tj))] + 1.0 / aj[int(np.argmin(tj))])
    return (Ci - Cj) ** 2 / (2.0 * inv)


def shrink_cost(theta, alpha, z):
    """Least energy to fit every cell of the row inside a window of width z.

    For a fixed window position l the optimal row is the clip of theta into
    [l, l+z], so the cost is a sum of one-sided squared hinges and is convex in
    l. Its derivative,

        D(l) = sum_{theta_a < l} alpha_a (l - theta_a)
             - sum_{theta_a > l+z} alpha_a (theta_a - l - z),

    is piecewise linear with breakpoints at the cells and at the cells shifted
    by z, and is linear with known coefficients between consecutive breakpoints.
    So the minimiser is found exactly by solving D(l) = 0 on each interval and
    keeping the root that lies inside it -- no search, and no breakpoint-only
    scan, which would over-estimate because the minimum is generally interior.
    """
    if z >= capacity(theta) - 1e-15:
        return 0.0

    def g(l):
        lam = np.clip(theta, l, l + z)
        return 0.5 * float((alpha * (lam - theta) ** 2).sum())

    pts = np.unique(np.concatenate([theta, theta - z]))
    best = min(g(float(p)) for p in pts)
    lo_edge = float(theta.min()) - z - 1.0
    hi_edge = float(theta.max()) + 1.0
    edges = np.concatenate([[lo_edge], pts, [hi_edge]])
    for u, v in zip(edges[:-1], edges[1:]):
        mid = 0.5 * (u + v)
        L = theta < mid
        U = theta > mid + z
        wa = float(alpha[L].sum() + alpha[U].sum())
        if wa <= 0:
            continue
        num = float((alpha[L] * theta[L]).sum() + (alpha[U] * (theta[U] - z)).sum())
        root = num / wa
        if u <= root <= v:
            best = min(best, g(root))
    return best


def expand_cost_pair(theta, alpha, c, d, z):
    gap = theta[c] - theta[d]
    t = z - gap
    if t <= 0:
        return 0.0
    w = alpha[c] * alpha[d] / (alpha[c] + alpha[d])
    return 0.5 * t * t * w


def _pair_weights(theta, alpha):
    """Gap and effective weight of every ordered pair, as flat arrays."""
    g = theta[:, None] - theta[None, :]
    w = (alpha[:, None] * alpha[None, :]) / (alpha[:, None] + alpha[None, :])
    m = ~np.eye(len(theta), dtype=bool)
    return g[m], w[m], np.argwhere(m)


def j_full(ti, ai, tj, aj, grid=512, refine=80, with_arg=False):
    """Least energy of a capacity-inverting alternative.

    The shrink curve does not depend on which pair of j is opened, so it is
    evaluated once on a grid of target widths and the pair costs are added
    vectorised. The grid locates the minimum; a golden-section refinement on the
    bracketing interval, for the pair that attains it, takes it the rest of the
    way. For a fixed pair the objective is convex in z, so the refinement is
    exact within its bracket.
    """
    hi0 = capacity(ti)
    zs = np.linspace(0.0, hi0, grid)
    S = np.array([shrink_cost(ti, ai, float(z)) for z in zs])
    gaps, ws, idx = _pair_weights(tj, aj)
    t = np.maximum(zs[None, :] - gaps[:, None], 0.0)
    E = 0.5 * t * t * ws[:, None]
    tot = S[None, :] + E
    k = int(np.argmin(tot))
    pi, zi = divmod(k, len(zs))
    lo = zs[max(zi - 1, 0)]; hi = zs[min(zi + 1, len(zs) - 1)]
    c, d = int(idx[pi][0]), int(idx[pi][1])
    f = lambda z: shrink_cost(ti, ai, z) + expand_cost_pair(tj, aj, c, d, z)
    for _ in range(refine):
        m1 = hi - GOLD * (hi - lo); m2 = lo + GOLD * (hi - lo)
        if f(m1) < f(m2):
            hi = m2
        else:
            lo = m1
        if hi - lo < 1e-14:
            break
    best = min(float(tot.flat[k]), f(0.5 * (lo + hi)))
    return (best, (c, d)) if with_arg else best


def j_full_slsqp(ti, ai, tj, aj, starts=6, rng=None):
    """Independent check: a general-purpose optimiser on the raw variables.

    Uses none of the decomposition -- it sees only the energy and the constraint
    C_j(lambda) - C_i(lambda) >= 0 -- so agreement is evidence that the
    decomposition is right rather than that both share an assumption. Returns
    the best feasible value found, or None if no start converged to a feasible
    point; a local optimiser can only land at or above the true minimum.
    """
    from scipy.optimize import minimize
    A = len(ti)
    rng = rng or np.random.default_rng(0)

    def unpack(x):
        return x[:A], x[A:]

    def obj(x):
        li, lj = unpack(x)
        return 0.5 * float((ai * (li - ti) ** 2).sum() + (aj * (lj - tj) ** 2).sum())

    def con(x):
        li, lj = unpack(x)
        return capacity(lj) - capacity(li)

    best = None
    for s in range(starts):
        x0 = np.concatenate([ti, tj])
        if s:
            x0 = x0 + rng.normal(0.0, 0.15, size=2 * A)
        r = minimize(obj, x0, constraints=[{'type': 'ineq', 'fun': con}],
                     method='SLSQP', options={'maxiter': 600, 'ftol': 1e-14})
        if r.success and con(r.x) >= -1e-9:
            v = obj(r.x)
            if best is None or v < best:
                best = v
    return best


def family1(eta):
    return (np.array([0.0, 1.0, 0.5]), np.array([1.0, 1.0, 1.0]),
            np.array([0.0, 0.5, 0.25]), np.array([1.0, 1.0, eta]))


def family2(eta):
    return (np.array([0.0, 1.0, 0.75]), np.array([1.0, eta, 1.0]),
            np.array([0.0, 0.5, 0.25]), np.array([1.0, 1.0, 1.0]))


def extremum_moves(ti, ai, tj, aj):
    """Does the cheapest alternative open a pair of j other than its extrema?

    This is the mechanism family 1 exploits: the cheap route to raising j's
    capacity runs through a cell that is not currently an extremum, which the
    proxy cannot see because it has frozen the extrema.
    """
    _, arg = j_full(ti, ai, tj, aj, with_arg=True)
    c0, d0 = int(np.argmax(tj)), int(np.argmin(tj))
    return arg != (c0, d0), arg


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--out', required=True)
    ap.add_argument('--instances', type=int, default=4000)
    ap.add_argument('--pgd-checks', type=int, default=40)
    a = ap.parse_args()
    t0 = time.time()

    # ---------------- self-checks --------------------------------------
    sc = {'f1_scalar': 0.0, 'f1_full_le': True, 'f2_scalar': 0.0, 'f2_full_ge': True}
    for eta in (1.0, 0.5, 0.1, 0.01, 1e-3, 1e-4):
        ti, ai, tj, aj = family1(eta)
        sc['f1_scalar'] = max(sc['f1_scalar'], abs(j_scalar(ti, ai, tj, aj) - 1 / 32) * 32)
        if j_full(ti, ai, tj, aj) > 9 * eta / 32 + 1e-12:
            sc['f1_full_le'] = False
        ti, ai, tj, aj = family2(eta)
        pred = eta / (8 * (1 + 3 * eta))
        sc['f2_scalar'] = max(sc['f2_scalar'], abs(j_scalar(ti, ai, tj, aj) - pred) / pred)
        if j_full(ti, ai, tj, aj) < 1 / 128 - 1e-9:
            sc['f2_full_ge'] = False
    passed = (sc['f1_scalar'] < 1e-12 and sc['f2_scalar'] < 1e-12
              and sc['f1_full_le'] and sc['f2_full_ge'])
    print(f"self-check: family1 J_scalar rel {sc['f1_scalar']:.1e}, J_full<=9eta/32 "
          f"{sc['f1_full_le']}; family2 J_scalar rel {sc['f2_scalar']:.1e}, "
          f"J_full>=1/128 {sc['f2_full_ge']} -> {'PASS' if passed else 'FAIL'}", flush=True)
    if not passed:
        raise SystemExit('self-check failed; sweep not reported')

    # ---------------- the two families, on a fine eta grid --------------
    fam = []
    for eta in [10 ** (-4 + 4 * i / 60) for i in range(61)]:
        ti, ai, tj, aj = family1(eta)
        s1, f1 = j_scalar(ti, ai, tj, aj), j_full(ti, ai, tj, aj)
        ti, ai, tj, aj = family2(eta)
        s2, f2 = j_scalar(ti, ai, tj, aj), j_full(ti, ai, tj, aj)
        fam.append(dict(eta=eta, f1_scalar=s1, f1_full=f1, f1_ratio=f1 / s1,
                        f1_bound=9 * eta, f2_scalar=s2, f2_full=f2, f2_ratio=f2 / s2,
                        f2_bound=(1 + 3 * eta) / (16 * eta)))

    # ---------------- random instances ---------------------------------
    rng = np.random.default_rng(MASTER_SEED)
    rows = []
    for n in range(a.instances):
        A = int(rng.integers(3, 9))
        ti = rng.uniform(0.0, 1.0, size=A)
        tj = rng.uniform(0.0, 1.0, size=A)
        ai = 10 ** rng.uniform(-2, 1, size=A)
        aj = 10 ** rng.uniform(-2, 1, size=A)
        if capacity(ti) <= capacity(tj):          # i must be the claimed top
            ti, tj = tj, ti; ai, aj = aj, ai
        s = j_scalar(ti, ai, tj, aj)
        if s <= 0:
            continue
        f, arg = j_full(ti, ai, tj, aj, with_arg=True)
        moved = arg != (int(np.argmax(tj)), int(np.argmin(tj)))
        rows.append(dict(A=A, j_scalar=s, j_full=f, ratio=f / s,
                         extremum_moves=bool(moved),
                         cap_i=capacity(ti), cap_j=capacity(tj)))
        if (n + 1) % 500 == 0:
            print(f'{n+1}/{a.instances}  {time.time()-t0:.0f}s', flush=True)

    # ---------------- independent solver check --------------------------
    pgd = []
    for k in range(a.pgd_checks):
        A = int(rng.integers(3, 6))
        ti = rng.uniform(0.0, 1.0, size=A); tj = rng.uniform(0.0, 1.0, size=A)
        ai = 10 ** rng.uniform(-1, 1, size=A); aj = 10 ** rng.uniform(-1, 1, size=A)
        if capacity(ti) <= capacity(tj):
            ti, tj = tj, ti; ai, aj = aj, ai
        exact = j_full(ti, ai, tj, aj)
        approx = j_full_slsqp(ti, ai, tj, aj, rng=rng)
        if approx is None:
            continue
        pgd.append(dict(exact=exact, slsqp=approx,
                        rel=(abs(approx - exact) / exact if exact > 0 else 0.0),
                        slsqp_below=bool(approx < exact - 1e-9 * max(exact, 1e-12))))

    r = np.array([x['ratio'] for x in rows])
    moved = np.array([x['extremum_moves'] for x in rows])
    out = dict(provenance=_P.stamp(__file__), script='EXP_functional_proxy.py',
               design='two proved families on a 61-point eta grid, plus random instances '
                      'with 3-8 actions and precisions log-uniform over three decades; '
                      'J_full computed exactly by convex decomposition and cross-checked '
                      'against projected gradient descent',
               master_seed=MASTER_SEED, instances=len(rows),
               self_check=dict(family1_scalar_rel=sc['f1_scalar'],
                               family1_full_within_bound=sc['f1_full_le'],
                               family2_scalar_rel=sc['f2_scalar'],
                               family2_full_above_bound=sc['f2_full_ge'],
                               passed=bool(passed)),
               solver_check=dict(cells=len(pgd),
                                 max_relative_gap=max(x['rel'] for x in pgd) if pgd else None,
                                 below_count=sum(1 for x in pgd if x['slsqp_below']),
                                 note='a local optimiser can only land at or above the true '
                                      'minimum, so any cell where it lands below is a defect '
                                      'in the decomposition and is counted here'),
               families=fam, rows=rows,
               ratio_median=float(np.median(r)),
               ratio_p05=float(np.percentile(r, 5)), ratio_p95=float(np.percentile(r, 95)),
               ratio_min=float(r.min()), ratio_max=float(r.max()),
               frac_over_2x=float((r > 2).mean()), frac_under_half=float((r < 0.5).mean()),
               frac_extremum_moves=float(moved.mean()),
               ratio_median_when_moved=float(np.median(r[moved])) if moved.any() else None,
               ratio_median_when_fixed=float(np.median(r[~moved])) if (~moved).any() else None,
               wall_seconds=round(time.time() - t0, 1))
    Path(a.out).write_text(json.dumps(out, indent=1))
    print('wrote', a.out, 'instances', len(rows),
          'ratio median %.3f  p05 %.3f  p95 %.3f' % (out['ratio_median'], out['ratio_p05'], out['ratio_p95']),
          'moves %.3f' % out['frac_extremum_moves'],
          'solver gap %.2e' % (out['solver_check']['max_relative_gap'] or 0),
          'below', out['solver_check']['below_count'])


if __name__ == '__main__':
    main()
