"""B3-fiber: linear-fiber (lambda-sweep) search for a direct rank-one D6 counterexample.

Target hypothesis (same as B3 v2)::

    AllCoordinatesInteractionContrastRankOne(q, F)  =>  2 D <= (m - 1) delta_square

with the centred interaction-contrast profile, anchor ``u0 = 0``::

    psi_{i,u}(z) = [F(z[i<-u]) - F(z[i<-u0])] - [Q_i(u) - Q_i(u0)],
    Q_i(u)       = sum_{z_-i} q(z_-i) F(z[i<-u]).

Why this protocol exists
------------------------
``run_d6_direct_rankone_constrained_search.py`` (B3 v2) imposes the 2-by-2
profile minors as SLSQP equality constraints on the raw world.  Those minors are
quadratic and massively redundant; SLSQP answers "More equality constraints than
independent variables" and the rationalized leads mostly fail the exact rank-one
recheck.  m=6/m=8 are recorded BLOCKED.

This protocol removes the nonlinearity instead of fighting it.

(A) ``psi`` is LINEAR in ``F``.  ``Q_i`` is a fixed convex combination of
    F-values, so every ``psi_{i,u}(z)`` is a linear functional of the flat
    vector ``F in R^(K^m)``.

(B) Rank-one is a UNION OF LINEAR SUBSPACES.  Let ``Psi^(i)`` be the
    ``(K-1) x K^(m-1)`` matrix with rows ``u = 1..K-1`` and columns ``z_-i``.
    ``rank Psi^(i) <= 1`` iff there is a direction ``lambda_i`` in ``P^(K-2)``
    with every COLUMN of ``Psi^(i)`` inside ``span(lambda_i)``.  For a FIXED
    ``lambda_i`` that is ``(K-2)`` LINEAR equations per context: pick a basis
    ``{w}`` of ``lambda_i^perp`` and require ``w . Psi^(i)_{:,z} = 0`` for all z.
    Hence for a fixed tuple ``lambda = (lambda_1,...,lambda_m)`` the admissible
    worlds form a LINEAR SUBSPACE ``V_lambda`` of ``R^(K^m)`` -- no nonlinear
    equality constraints at all -- and

        {F : AllCoordinatesInteractionContrastRankOne} = union over lambda of V_lambda,

    so sweeping ``lambda`` is exhaustive in principle, not a heuristic subclass.

    A useful simplification: ``w . Psi^(i)_{:,z} = 0`` for all z is equivalent to
    "``z |-> w . [F(z[i<-u]) - F(z[i<-0])]_u`` is CONSTANT in z", because the
    subtracted ``Q`` term is exactly the q-weighted mean of that same quantity.
    So ``V_lambda`` does not depend on ``q`` and its defining system is sparse.

(C) Scale invariance.  ``L_F(S) = osc[F - sum_{j in S} Q_j] / 2`` and
    ``delta_square`` are maxima/minima of linear functionals of ``F``, hence
    positively homogeneous of degree 1, so ``2 D / ((m-1) delta_square)`` is
    invariant under ``F -> cF`` for ``c > 0``.  The inner search is therefore run
    on the unit sphere of the fiber coordinates.

Algorithm
---------
1. sweep ``lambda`` (deterministic Halton grid, or seeded random, plus a small
   deterministic set of structured directions);
2. build ``A_lambda`` and an orthonormal float basis ``B`` of its nullspace;
3. search ``F = B c`` UNCONSTRAINED with a derivative-free optimizer (the
   objective is piecewise linear and nonsmooth, so SLSQP/BFGS are inappropriate);
   both optimizer budgets are capped in function evaluations.  Measured at
   m=6, K=3, uniform reference, 2 starts: Nelder-Mead reached a best float ratio
   of 0.019 while Powell reached 0.114 on the same fibers, so the default runs
   Nelder-Mead followed by a Powell polish;
4. for each promising lead: rationalize ``F``, then re-project it EXACTLY onto
   ``V_lambda`` in ``fractions.Fraction`` arithmetic, so rank-one holds BY
   CONSTRUCTION rather than by numerical luck; then verify all 2-by-2 minors,
   ``2D`` and ``(m-1) delta_square`` exactly with the shared exact evaluator.

Evidence discipline: a float lead is never a result; only the exact-rational
recheck can kill the law.  Surviving this gate is NOT a proof of the law -- it is
a finite, seeded, incomplete search over a continuum of fibers.

Scope note: the exact re-projection uses one of two exact rational bases of
``V_lambda`` (see ``--exact-basis``).  ``gauss`` is the full fiber
(Fraction Gaussian elimination on the fiber system) but is cubic and only
affordable for small ``K^m``.  ``multiaffine`` is the closed-form rational
subspace spanned by the ``2^m`` products ``prod_{i in S} phi_i(a_i)`` with
``phi_i(0) = 0``, ``phi_i(u) = lambda_{i,u}``; that subspace is always CONTAINED
in ``V_lambda`` (so exactness is never at risk), but it can be a proper subspace
for degenerate lambda, which is recorded per fiber as
``exact_basis_covers_fiber``.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
import json
import math
from pathlib import Path
import random
import sys
import time
from typing import Sequence

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.provenance import write_artifact_with_provenance
from scripts.run_d6_rankone_falsification import (
    actions, evaluate_candidate, fraction_text, q_payload, rank_one_check,
    reference_rows, response_table, world_payload,
)

PROTOCOL_VERSION = "d6_direct_rankone_linear_fiber_search_v1"
PROTOCOL_VERSION_DIMENSION = "d6_rankone_fiber_dimension_exact_certificate_v1"
PROTOCOL_VERSION_CORNERS = "d6_direct_rankone_corner_reference_fiber_sweep_v1"
PROTOCOL_VERSION_HAMMER = "d6_direct_rankone_fiber_cell_lp_hammer_v1"
EVIDENCE_CLASS = "NUMERICAL_LEAD_WITH_EXACT_RATIONAL_RECHECK"
EVIDENCE_CLASS_DIMENSION = "EXACT_INTEGER_CERTIFICATE_OVER_ENUMERATED_CASES"

_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71)


# --------------------------------------------------------------------------
# float evaluator: a vectorized mirror of the exact evaluator in
# scripts/run_d6_rankone_falsification.py.  --self-test checks it agrees with
# that exact evaluator (and with the independent float evaluator in
# scripts/run_d6_half_factor_lemma_falsification.py) on random rational worlds.
# --------------------------------------------------------------------------
class FloatModel:
    def __init__(self, m: int, alphabet: int, q_rows: Sequence[Sequence[Fraction]],
                 min_topc_margin: float = 0.0):
        # min_topc_margin > 0 turns on the StrictTopC gate: a world whose Top-C
        # selection is decided by a tie (or by a margin below the threshold) is
        # reported as UNDEFINED, never as a violation.  The margin is measured
        # relative to delta_square because the whole objective is scale
        # invariant, so an absolute margin threshold would be meaningless.
        self.min_topc_margin = float(min_topc_margin)
        self.m, self.K = int(m), int(alphabet)
        self.k = self.m // 2
        self.q = np.asarray([[float(v) for v in row] for row in q_rows], dtype=float)
        self.subsets = tuple(itertools.combinations(range(self.m), self.k))
        self.ctx_weight = []
        self.bshape = []
        for i in range(self.m):
            w = np.ones(1, dtype=float)
            for j in range(self.m):
                if j != i:
                    w = np.multiply.outer(w, self.q[j]).ravel()
            self.ctx_weight.append(w)
            shape = [1] * self.m
            shape[i] = self.K
            self.bshape.append(tuple(shape))

    def slices(self, F: np.ndarray) -> list[np.ndarray]:
        """slices[i][u, z] = F(z[i<-u]); z ranges over the other coordinates."""
        return [np.moveaxis(F, i, 0).reshape(self.K, -1) for i in range(self.m)]

    def response(self, sl: Sequence[np.ndarray]) -> np.ndarray:
        return np.stack([sl[i] @ self.ctx_weight[i] for i in range(self.m)])

    def evaluate(self, F: np.ndarray) -> dict:
        sl = self.slices(F)
        R = self.response(sl)
        baseline = float(R[0] @ self.q[0])
        comp = R - baseline
        score = R.max(axis=1) - R.min(axis=1)
        delta = 0.0
        for i in range(self.m):
            dif = sl[i][:, None, :] - sl[i][None, :, :]
            delta = max(delta, float((dif.max(axis=2) - dif.min(axis=2)).max()))
        losses = {}
        for S in self.subsets:
            res = F.copy()
            for i in S:
                res = res - comp[i].reshape(self.bshape[i])
            losses[S] = 0.5 * float(res.max() - res.min())
        order = sorted(range(self.m), key=lambda i: (-float(score[i]), i))
        selected = tuple(sorted(order[: self.k]))
        optimum = min(losses.values())
        sel = set(selected)
        if 0 < len(sel) < self.m:
            margin = (min(float(score[i]) for i in range(self.m) if i in sel)
                      - max(float(score[i]) for i in range(self.m) if i not in sel))
        else:
            margin = 0.0
        return {
            "delta_square": delta,
            "topc_margin": margin,
            "topc_margin_relative": (margin / delta) if delta > 1e-12 else 0.0,
            "selected": selected,
            "loss_selected": losses[selected],
            "loss_optimum": optimum,
            "regret": losses[selected] - optimum,
        }

    def ratio(self, F: np.ndarray) -> float | None:
        """2D / ((m-1) delta_square); None when delta_square vanishes (UNDEFINED)."""
        d = self.evaluate(F)
        if d["delta_square"] <= 1e-12:
            return None
        if self.min_topc_margin > 0.0 and \
                d["topc_margin_relative"] < self.min_topc_margin:
            # StrictTopC gate: the Top-C set is a tie-break artifact here, so this
            # world says nothing about the geometry.  UNDEFINED, not a violation.
            return None
        return 2.0 * d["regret"] / ((self.m - 1) * d["delta_square"])

    def psi(self, F: np.ndarray) -> list[np.ndarray]:
        sl = self.slices(F)
        R = self.response(sl)
        return [
            (sl[i][1:, :] - sl[i][0:1, :]) - (R[i, 1:] - R[i, 0])[:, None]
            for i in range(self.m)
        ]

    def rank_one_defect(self, F: np.ndarray) -> tuple[float, float]:
        """(max |2x2 minor|, max sigma_2 / sigma_1) over all coordinate profiles."""
        worst_minor, worst_ratio = 0.0, 0.0
        for P in self.psi(F):
            if P.shape[0] < 2:
                continue
            s = np.linalg.svd(P, compute_uv=False)
            worst_ratio = max(worst_ratio, float(s[1] / s[0]) if s[0] > 0 else 0.0)
            for a, b in itertools.combinations(range(P.shape[0]), 2):
                M = np.outer(P[a], P[b])
                worst_minor = max(worst_minor, float(np.abs(M - M.T).max()))
        return worst_minor, worst_ratio


# --------------------------------------------------------------------------
# fiber construction
# --------------------------------------------------------------------------
def _van_der_corput(n: int, base: int) -> float:
    value, denom = 0.0, 1.0
    while n:
        n, rem = divmod(n, base)
        denom *= base
        value += rem / denom
    return value


def structured_lambdas(m: int, alphabet: int) -> list[np.ndarray]:
    """Deterministic directions worth visiting first."""
    K1 = alphabet - 1
    seeds: list[list[float]] = []
    if K1 == 1:
        seeds = [[1.0]]
    elif K1 == 2:
        # (1,2) is the fiber of the phi = (-1,0,1) multiaffine families used by
        # B1/B_product/B2, so it reproduces the already-searched classes.
        seeds = [[1.0, 2.0], [1.0, 1.0], [1.0, 0.0], [0.0, 1.0], [1.0, -1.0], [2.0, 1.0]]
    else:
        seeds = [[1.0] * K1] + [[1.0 if j == t else 0.0 for j in range(K1)] for t in range(K1)]
    return [np.tile(np.asarray(s, dtype=float), (m, 1)) for s in seeds]


def sample_lambdas(m: int, alphabet: int, count: int, mode: str, seed: int,
                   include_structured: bool) -> list[np.ndarray]:
    K1 = alphabet - 1
    out: list[np.ndarray] = []
    if include_structured:
        out.extend(structured_lambdas(m, alphabet))
    rng = np.random.default_rng(int(seed))
    index = 1
    while len(out) < count:
        if mode == "halton":
            if alphabet == 3:
                if m > len(_PRIMES):
                    raise ValueError("halton lambda grid supports m <= %d" % len(_PRIMES))
                theta = np.asarray([math.pi * _van_der_corput(index, _PRIMES[i]) for i in range(m)])
                lam = np.stack([np.cos(theta), np.sin(theta)], axis=1)
            else:
                # deterministic but crude for K > 3: spherical coordinates are not
                # worth the complexity, so fall back to a seeded quasi-random draw.
                lam = rng.standard_normal((m, K1))
        elif mode == "random":
            lam = rng.standard_normal((m, K1))
        else:
            raise ValueError("unknown lambda mode: %s" % mode)
        norms = np.linalg.norm(lam, axis=1, keepdims=True)
        norms[norms == 0.0] = 1.0
        out.append(lam / norms)
        index += 1
    return out[:count]


def rationalize_lambda(lam: np.ndarray, denominator: int) -> list[tuple[int, ...]] | None:
    """Snap each direction to a primitive integer vector (exactness anchor)."""
    rows: list[tuple[int, ...]] = []
    for vec in lam:
        fr = [Fraction(float(v)).limit_denominator(int(denominator)) for v in vec]
        if all(f == 0 for f in fr):
            return None
        lcm = 1
        for f in fr:
            lcm = lcm * f.denominator // math.gcd(lcm, f.denominator)
        ints = [int(f * lcm) for f in fr]
        g = 0
        for value in ints:
            g = math.gcd(g, abs(value))
        if g > 1:
            ints = [value // g for value in ints]
        for value in ints:  # canonical sign: first nonzero positive (projective point)
            if value != 0:
                if value < 0:
                    ints = [-x for x in ints]
                break
        rows.append(tuple(ints))
    return rows


def frac_rref(rows: Sequence[Sequence[Fraction]], ncols: int):
    mat = [list(r) for r in rows]
    pivots: list[int] = []
    r = 0
    for c in range(ncols):
        piv = None
        for rr in range(r, len(mat)):
            if mat[rr][c] != 0:
                piv = rr
                break
        if piv is None:
            continue
        mat[r], mat[piv] = mat[piv], mat[r]
        inv = Fraction(1) / mat[r][c]
        mat[r] = [x * inv for x in mat[r]]
        for rr in range(len(mat)):
            if rr != r and mat[rr][c] != 0:
                f = mat[rr][c]
                mat[rr] = [a - f * b for a, b in zip(mat[rr], mat[r])]
        pivots.append(c)
        r += 1
        if r == len(mat):
            break
    return mat[:r], pivots


def frac_nullspace(rows: Sequence[Sequence[Fraction]], ncols: int) -> list[list[Fraction]]:
    if not rows:
        return [[Fraction(1) if j == i else Fraction(0) for j in range(ncols)] for i in range(ncols)]
    reduced, pivots = frac_rref(rows, ncols)
    pivot_set = set(pivots)
    basis = []
    for free in (c for c in range(ncols) if c not in pivot_set):
        vec = [Fraction(0)] * ncols
        vec[free] = Fraction(1)
        for ri, pc in enumerate(pivots):
            vec[pc] = -reduced[ri][free]
        basis.append(vec)
    return basis


def perp_basis_exact(lam_int: Sequence[int]) -> list[list[Fraction]]:
    return frac_nullspace([[Fraction(v) for v in lam_int]], len(lam_int))


def fiber_rows(m: int, alphabet: int, perp: Sequence[Sequence[Sequence[Fraction]]],
               *, as_float: bool):
    """Rows of A_lambda in the q-free form 'w . [F(z[i<-u]) - F(z[i<-0])] is constant'."""
    K = alphabet
    N = K ** m
    strides = [K ** (m - 1 - j) for j in range(m)]
    ctxs = list(itertools.product(range(K), repeat=m - 1))
    rows = []
    for i in range(m):
        others = [j for j in range(m) if j != i]
        ref = ctxs[0]
        for w in perp[i]:
            wsum = sum(w)
            for z in ctxs[1:]:
                row = [Fraction(0)] * N
                for ctx, sign in ((z, Fraction(1)), (ref, Fraction(-1))):
                    base = sum(strides[j] * ctx[t] for t, j in enumerate(others))
                    row[base] += -sign * wsum
                    for u in range(1, K):
                        row[base + strides[i] * u] += sign * w[u - 1]
                rows.append(row)
    if as_float:
        return np.asarray([[float(x) for x in row] for row in rows], dtype=float).reshape(len(rows), N)
    return rows


NULLSPACE_BACKEND_USED: list[str] = []


def _svd_right_factor(A: np.ndarray, full: bool):
    """Right singular vectors of ``A``, with LAPACK fallbacks.

    numpy's default driver is ``gesdd``.  On some platforms (notably macOS
    Accelerate) ``gesdd`` raises ``SVD did not converge`` on perfectly ordinary
    matrices.  ``gesvd`` is slower but far more robust, and an eigendecomposition
    of ``A^T A`` is a last resort that never calls the SVD path at all.  Every
    fallback records which backend produced the answer, so an artifact can never
    hide that a less accurate route was taken.
    """
    scale = float(np.max(np.abs(A))) if A.size else 0.0
    As = A / scale if scale > 0.0 else A
    try:
        _, s, Vt = np.linalg.svd(As, full_matrices=full)
        NULLSPACE_BACKEND_USED.append("numpy_gesdd")
        return s * (scale if scale > 0.0 else 1.0), Vt
    except np.linalg.LinAlgError:
        pass
    try:
        from scipy.linalg import svd as _scipy_svd
        _, s, Vt = _scipy_svd(As, full_matrices=full, lapack_driver="gesvd")
        NULLSPACE_BACKEND_USED.append("scipy_gesvd")
        return s * (scale if scale > 0.0 else 1.0), Vt
    except Exception as exc:
        # A Gram-matrix eigendecomposition was tried here and REJECTED: squaring
        # halves the effective precision and it reported nullspace dim 69 where
        # the exact answer is 70 at m=6, K=3.  A silently wrong fibre dimension is
        # worse than no answer, so fail instead and let the caller fall back to
        # the exact closed-form basis, whose dimension is exactly right.
        raise np.linalg.LinAlgError(
            f"both SVD drivers failed on the fibre constraint matrix: {exc}") from exc


def nullspace_float(A: np.ndarray, N: int, tol: float) -> np.ndarray:
    if A.size == 0:
        return np.eye(N)
    if not np.all(np.isfinite(A)):
        raise ValueError("fiber constraint matrix contains non-finite entries")
    full = A.shape[0] < N
    before = len(NULLSPACE_BACKEND_USED)
    s, Vt = _svd_right_factor(A, full)
    smax = float(s[0]) if s.size else 0.0
    thresh = max(float(tol), smax * max(A.shape) * float(np.finfo(float).eps) * 10.0)
    rank = int(np.sum(s > thresh))
    return np.ascontiguousarray(Vt[rank:].T)


# --------------------------------------------------------------------------
# exact rational machinery
# --------------------------------------------------------------------------
def closed_form_fiber_dim(m: int, alphabet: int) -> int:
    """Dimension of V_lambda for a non-degenerate lambda tuple.

    ``1`` (constants) ``+ m (K-1)`` (arbitrary per-coordinate additive parts)
    ``+ 2^m - 1 - m`` (phi-products of order at least two).  Verified against the
    float SVD nullspace dimension for m = 2..6 at K = 3, and against the exact
    Fraction Gaussian nullspace at m <= 4 (see --self-test).
    """
    return 1 + m * (alphabet - 1) + (2 ** m - 1 - m)


def closed_form_raw_fiber_dim(m: int, alphabet: int) -> int:
    """Dimension of the RAW-rank-one fibre V^raw_phi.

    ``1`` (constants) ``+ m`` (one additive direction per coordinate, forced to
    be affine in ``phi_i``) ``+ 2^m - 1 - m`` (phi-products of order at least
    two) ``= 2^m``.  It sits at codimension ``m (K - 2)`` inside V_lambda: the
    centred fibre carries ``K - 1`` free additive degrees of freedom per
    coordinate, the raw fibre carries exactly one.  Verified exactly (rank over
    Q, plus closure under addition) in scripts/verify_raw_fiber.py; see
    research/d6_contrast_rank_falsification/E1_rawfiber_m6_K3.json.
    """
    return 2 ** m


def closed_form_raw_basis_exact(m: int, alphabet: int,
                                lam_int: Sequence[Sequence[int]]):
    """Closed-form integer basis of the RAW-rank-one fibre V^raw_phi.

    Identical to `closed_form_basis_exact` except that the ``m (K - 1)`` free
    additive indicator columns are replaced by the ``m`` columns
    ``phi_i(a_i)``.  Every column has raw local contrast rank one at every
    coordinate with the SAME theta_i = phi_i, which is why the span is closed
    under addition and the fibre is a linear subspace -- exactly as for the
    centred fibre, so the unconstrained per-fibre search applies verbatim.
    """
    phi = [(0,) + tuple(int(v) for v in row) for row in lam_int]
    acts = list(itertools.product(range(alphabet), repeat=m))
    cols: list[tuple[int, ...]] = [tuple(1 for _ in acts)]
    for i in range(m):
        cols.append(tuple(phi[i][a[i]] for a in acts))
    for size in range(2, m + 1):
        for S in itertools.combinations(range(m), size):
            col = []
            for a in acts:
                v = 1
                for i in S:
                    v *= phi[i][a[i]]
                col.append(v)
            cols.append(tuple(col))
    return cols


def closed_form_basis_exact(m: int, alphabet: int, lam_int: Sequence[Sequence[int]]):
    """Closed-form integer basis of V_lambda.

    Membership is a one-line check, so exactness of the recheck never depends on
    this basis being *complete*:

    * additive columns ``F(a) = f_i(a_i)``: the profile difference
      ``F(z[i<-u]) - F(z[i<-0]) = f_i(u) - f_i(0)`` is constant in z and the
      difference at every other coordinate vanishes, so ``Psi`` is identically
      zero -- rank 0 <= 1 at every coordinate;
    * product columns ``prod_{i in S} phi_i(a_i)`` with ``|S| >= 2`` and
      ``phi_i(0) = 0, phi_i(u) = lambda_{i,u}``: for ``i in S`` the difference is
      ``phi_i(u) * prod_{j in S minus i} phi_j(z_j)``, whose centred profile
      column is proportional to ``lambda_i``; for ``i not in S`` it is zero.

    Completeness (that these columns span all of ``V_lambda``) is never assumed:
    it is recorded per fiber as ``exact_basis_covers_fiber``, i.e. the exact basis
    dimension equals the numerically computed nullspace dimension.
    """
    phi = [(0,) + tuple(int(v) for v in row) for row in lam_int]
    acts = list(itertools.product(range(alphabet), repeat=m))
    cols: list[tuple[int, ...]] = [tuple(1 for _ in acts)]
    for i in range(m):
        for u in range(1, alphabet):
            cols.append(tuple(1 if a[i] == u else 0 for a in acts))
    for size in range(2, m + 1):
        for S in itertools.combinations(range(m), size):
            col = []
            for a in acts:
                v = 1
                for i in S:
                    v *= phi[i][a[i]]
                col.append(v)
            cols.append(tuple(col))
    return cols


def frac_dot(a: Sequence[Fraction], b: Sequence[Fraction]) -> Fraction:
    return sum((x * y for x, y in zip(a, b)), Fraction(0))


def frac_solve(matrix: list[list[Fraction]], rhs: list[Fraction]) -> list[Fraction] | None:
    n = len(rhs)
    aug = [list(matrix[r]) + [rhs[r]] for r in range(n)]
    for c in range(n):
        piv = None
        for rr in range(c, n):
            if aug[rr][c] != 0:
                piv = rr
                break
        if piv is None:
            return None
        aug[c], aug[piv] = aug[piv], aug[c]
        inv = Fraction(1) / aug[c][c]
        aug[c] = [x * inv for x in aug[c]]
        for rr in range(n):
            if rr != c and aug[rr][c] != 0:
                f = aug[rr][c]
                aug[rr] = [a - f * b for a, b in zip(aug[rr], aug[c])]
    return [aug[r][n] for r in range(n)]


def exact_project(basis: Sequence[Sequence[Fraction]], target: Sequence[Fraction]):
    """Exact orthogonal projection of ``target`` onto span(basis), all Fractions."""
    d = len(basis)
    if d == 0:
        return None, None
    gram = [[Fraction(0)] * d for _ in range(d)]
    for a in range(d):
        for b in range(a, d):
            value = frac_dot(basis[a], basis[b])
            gram[a][b] = value
            gram[b][a] = value
    coeffs = frac_solve(gram, [frac_dot(basis[a], target) for a in range(d)])
    if coeffs is None:
        return None, None
    out = [Fraction(0)] * len(target)
    for a, ca in enumerate(coeffs):
        if ca == 0:
            continue
        col = basis[a]
        for n in range(len(out)):
            if col[n]:
                out[n] += ca * col[n]
    return out, coeffs


def exact_coefficient_snap(basis: Sequence[Sequence[Fraction]], coeff_float: Sequence[float],
                           denominator: int):
    """Alternative snap: rationalize fiber coordinates, so F = B c is exact by construction."""
    coeffs = [Fraction(float(c)).limit_denominator(int(denominator)) for c in coeff_float]
    out = [Fraction(0)] * len(basis[0])
    for a, ca in enumerate(coeffs):
        if ca == 0:
            continue
        col = basis[a]
        for n in range(len(out)):
            if col[n]:
                out[n] += ca * col[n]
    return out, coeffs


# --------------------------------------------------------------------------
# exact fiber-dimension certificate (integers only -- no floating point)
# --------------------------------------------------------------------------
# The claim certified here is
#
#     dim V_lambda = 1 + m(K-1) + (2^m - 1 - m)  and the closed-form columns
#     {constants} + {per-coordinate additive} + {phi-products of order >= 2}
#     are a BASIS of V_lambda,
#
# which says exactly that rank-one-at-every-coordinate forces the scalar
# multiaffine normal form  F(a) = A(a) + sum_{|T|>=2} w_T prod_{i in T} phi_i(a_i)
# with A coordinate-additive and phi_i(u) = lambda_{i,u}, phi_i(0) = 0.
#
# The certificate has three integer legs and no float step:
#   (i)  A b = 0 over Z for every closed-form column b  ==> nullity_Q >= rank_Q(B);
#   (ii) rank_{F_p}(B) = d for a prime p ==> rank_Q(B) >= d, and <= d trivially,
#        so the columns are independent over Q and nullity_Q >= d;
#   (iii) rank_{F_p}(A) = N - d ==> rank_Q(A) >= N - d (a nonzero minor mod p is a
#        nonzero minor over Z), so nullity_Q <= d.
# Together nullity_Q = d exactly.  Leg (iii) is one-sided in the safe direction:
# a rank drop mod p can only UNDER-state rank_Q, so a passing certificate is
# sound for every prime, and two primes are used only to reduce the chance of a
# false NEGATIVE.  An independent Fraction Gaussian elimination is still run
# whenever it is affordable (--gauss-limit) as a redundant cross-check.
DIMENSION_PRIMES = (1000003, 999983)


def fiber_rows_sparse_int(m: int, alphabet: int,
                          lam_int: Sequence[Sequence[int]]) -> list[list[tuple[int, int]]]:
    """Sparse INTEGER rows of A_lambda, as [(flat index, coefficient), ...]."""
    K = alphabet
    strides = [K ** (m - 1 - j) for j in range(m)]
    ctxs = list(itertools.product(range(K), repeat=m - 1))
    rows: list[list[tuple[int, int]]] = []
    for i in range(m):
        others = [j for j in range(m) if j != i]
        ref = ctxs[0]
        for w in perp_basis_exact(lam_int[i]):
            lcm = 1
            for f in w:
                lcm = lcm * f.denominator // math.gcd(lcm, f.denominator)
            wi = [int(f * lcm) for f in w]
            g = 0
            for value in wi:
                g = math.gcd(g, abs(value))
            if g > 1:
                wi = [value // g for value in wi]
            wsum = sum(wi)
            for z in ctxs[1:]:
                acc: dict[int, int] = {}
                for ctx, sign in ((z, 1), (ref, -1)):
                    base = sum(strides[j] * ctx[t] for t, j in enumerate(others))
                    acc[base] = acc.get(base, 0) - sign * wsum
                    for u in range(1, K):
                        idx = base + strides[i] * u
                        acc[idx] = acc.get(idx, 0) + sign * wi[u - 1]
                rows.append([(k, v) for k, v in acc.items() if v != 0])
    return rows


def rank_mod_p(rows_sparse: Sequence[Sequence[tuple[int, int]]], ncols: int, p: int) -> int:
    """Exact rank over F_p by Gaussian elimination in int64 (p^2 fits in int64)."""
    n = len(rows_sparse)
    if n == 0:
        return 0
    A = np.zeros((n, ncols), dtype=np.int64)
    for r, row in enumerate(rows_sparse):
        for idx, value in row:
            A[r, idx] = value % p
    r = 0
    for c in range(ncols):
        if r >= n:
            break
        nz = np.nonzero(A[r:, c])[0]
        if nz.size == 0:
            continue
        piv = r + int(nz[0])
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        idx = r + 1 + np.nonzero(A[r + 1:, c])[0]
        if idx.size:
            A[idx] = (A[idx] - np.outer(A[idx, c], A[r])) % p
        r += 1
    return r


def _dense_to_sparse(cols: Sequence[Sequence[int]]) -> list[list[tuple[int, int]]]:
    return [[(i, int(v)) for i, v in enumerate(col) if v] for col in cols]


def dimension_certificate(m: int, alphabet: int, lam_int: Sequence[Sequence[int]],
                          *, gauss: bool = False,
                          primes: Sequence[int] = DIMENSION_PRIMES) -> dict:
    N = alphabet ** m
    t0 = time.time()
    rows = fiber_rows_sparse_int(m, alphabet, lam_int)
    seconds_rows = time.time() - t0
    t0 = time.time()
    basis = closed_form_basis_exact(m, alphabet, lam_int)
    seconds_basis = time.time() - t0
    d = len(basis)
    t0 = time.time()
    member = True
    worst_residual = 0
    for col in basis:
        for row in rows:
            total = 0
            for idx, value in row:
                total += value * col[idx]
            if total != 0:
                member = False
                worst_residual = max(worst_residual, abs(total))
    seconds_member = time.time() - t0
    out = {
        "m": m, "alphabet": alphabet, "variables": N, "equations": len(rows),
        "lambda_int": [list(row) for row in lam_int],
        "closed_form_dim": d,
        "closed_form_dim_formula": "1 + m(K-1) + (2^m - 1 - m)",
        "closed_form_columns_in_kernel_exactly": bool(member),
        "worst_integer_residual": int(worst_residual),
        "seconds_rows": round(seconds_rows, 3),
        "seconds_basis": round(seconds_basis, 3),
        "seconds_exact_membership": round(seconds_member, 3),
        "primes": list(map(int, primes)),
    }
    ranks_A, ranks_B = [], []
    for prime in primes:
        t0 = time.time()
        rank_a = rank_mod_p(rows, N, prime)
        ta = time.time() - t0
        t0 = time.time()
        rank_b = rank_mod_p(_dense_to_sparse(basis), N, prime)
        tb = time.time() - t0
        ranks_A.append(rank_a)
        ranks_B.append(rank_b)
        out[f"rank_A_mod_{prime}"] = rank_a
        out[f"rank_closed_form_mod_{prime}"] = rank_b
        out[f"seconds_rank_A_mod_{prime}"] = round(ta, 3)
        out[f"seconds_rank_closed_form_mod_{prime}"] = round(tb, 3)
    out["nullity_upper_bound"] = N - max(ranks_A)
    out["nullity_lower_bound"] = max(ranks_B) if member else 0
    out["exact_dimension_proved"] = bool(
        member and max(ranks_B) == d and (N - max(ranks_A)) == d
    )
    if gauss:
        t0 = time.time()
        dense = [[Fraction(0)] * N for _ in rows]
        for r, row in enumerate(rows):
            for idx, value in row:
                dense[r][idx] = Fraction(value)
        kernel = frac_nullspace(dense, N)
        stacked = [list(v) for v in kernel] + [[Fraction(x) for x in col] for col in basis]
        _, pivots = frac_rref(stacked, N)
        out["gauss_fraction_kernel_dim"] = len(kernel)
        out["gauss_stacked_rank"] = len(pivots)
        out["gauss_agrees_with_closed_form"] = bool(len(kernel) == len(pivots) == d)
        out["seconds_gauss_fraction"] = round(time.time() - t0, 3)
    return out


def named_lambdas(m: int, alphabet: int, kind: str, seed: int, denominator: int):
    K1 = alphabet - 1
    if kind == "generic":
        return rationalize_lambda(
            sample_lambdas(m, alphabet, 1, "random", seed, include_structured=False)[0],
            denominator)
    if kind == "degenerate":
        return [tuple(1 if j == (i % K1) else 0 for j in range(K1)) for i in range(m)]
    if kind == "ones":
        return [tuple(1 for _ in range(K1))] * m
    if kind == "mixed":
        generic = rationalize_lambda(
            sample_lambdas(m, alphabet, 1, "random", seed + 1, include_structured=False)[0],
            denominator)
        return [generic[i] if i % 2 else tuple(1 if j == 0 else 0 for j in range(K1))
                for i in range(m)]
    raise ValueError(f"unknown lambda kind: {kind}")


def run_dimension_check(args: argparse.Namespace) -> dict:
    m, K = int(args.m), int(args.alphabet)
    started = time.time()
    rows = []
    for kind in ("generic", "degenerate", "mixed", "ones"):
        lam = named_lambdas(m, K, kind, int(args.seed), int(args.denominator))
        cert = dimension_certificate(m, K, lam, gauss=(K ** m <= int(args.gauss_limit)))
        rows.append({"lambda_kind": kind, **cert})
    for trial in range(int(args.dimension_trials)):
        lam = rationalize_lambda(
            sample_lambdas(m, K, 1, "random", int(args.seed) + 1000 + trial,
                           include_structured=False)[0], int(args.denominator))
        rows.append({"lambda_kind": f"random_{trial}",
                     **dimension_certificate(m, K, lam)})
    proved = sum(1 for r in rows if r["exact_dimension_proved"])
    failures = [r for r in rows if not r["exact_dimension_proved"]]
    return {
        "protocol_version": PROTOCOL_VERSION_DIMENSION,
        "evidence_class": EVIDENCE_CLASS_DIMENSION,
        "development_only": True,
        "m": m, "alphabet": K, "seed": int(args.seed),
        "denominator": int(args.denominator),
        "lambda_tuples_checked": len(rows),
        "lambda_tuples_proved": proved,
        "failures": failures,
        "status": "EXACT_DIMENSION_IDENTITY_HOLDS" if not failures
                  else "EXACT_DIMENSION_IDENTITY_FAILS",
        "wall_clock_seconds": round(time.time() - started, 3),
        "certificates": rows,
        "interpretation": (
            "For each checked lambda tuple this is an EXACT computation, not a numerical "
            "estimate: integer kernel membership plus two modular ranks pin dim V_lambda "
            "from both sides, and Fraction Gaussian elimination re-derives it independently "
            "where affordable. It therefore establishes, FOR THESE (m, K, lambda) ONLY, that "
            "interaction-contrast rank one at every coordinate is equivalent to the scalar "
            "multiaffine normal form with latent maps phi_i = lambda_i. It is a finite family "
            "of verified instances, NOT a proof for all m, K and lambda: it is a COMPILED "
            "EXACT ARTIFACT over the enumerated cases and nothing more."
        ),
    }


# --------------------------------------------------------------------------
# inner search
# --------------------------------------------------------------------------
def search_fiber(model: FloatModel, B: np.ndarray, starts: int, rng: np.random.Generator,
                 method: str, maxiter: int, *, lp_rounds: int = 20, lp_box: float = 20.0,
                 de_maxiter: int = 200, de_popsize: int = 15):
    from scipy.optimize import minimize

    m, K = model.m, model.K
    dim = B.shape[1]
    shape = (K,) * m

    def negative_ratio(c: np.ndarray) -> float:
        norm = float(np.linalg.norm(c))
        if norm < 1e-12:
            return 0.0
        F = (B @ (c / norm)).reshape(shape)
        r = model.ratio(F)
        # UNDEFINED (delta_square = 0) is never a violation: it is the worst
        # possible objective value here, never +inf and never a counterexample.
        return 0.0 if r is None else -r

    stage_map = {
        "nelder-mead": ["Nelder-Mead"], "powell": ["Powell"],
        "both": ["Nelder-Mead", "Powell"], "de": ["DE"], "lp": ["LP"],
        "de+lp": ["DE", "LP"], "both+lp": ["Nelder-Mead", "Powell", "LP"],
        "de+both+lp": ["DE", "Nelder-Mead", "Powell", "LP"],
    }
    methods = stage_map[method]
    best_ratio, best_c, evaluations = 0.0, None, 0
    lp_rounds_log: list[dict] = []
    lp_consistency = 0.0
    for start_index in range(int(starts)):
        c0 = rng.standard_normal(dim)
        n0 = float(np.linalg.norm(c0))
        c0 = c0 / (n0 if n0 > 0 else 1.0)
        current = c0
        for name in methods:
            if name == "DE":
                # global stage; the start point is irrelevant, so run it once
                if start_index > 0:
                    continue
                value, cand, nfev = differential_evolution_search(
                    model, B, seed=int(rng.integers(1, 2 ** 31 - 1)),
                    maxiter=de_maxiter, popsize=de_popsize)
                evaluations += nfev
                if np.linalg.norm(cand) > 1e-12:
                    current = cand
                continue
            if name == "LP":
                out = cell_lp_ascent(model, B, current, rounds=lp_rounds, box=lp_box)
                lp_consistency = max(lp_consistency,
                                     out["objective_consistency_max_abs_error"])
                lp_rounds_log.append({"start": start_index,
                                      "ratio": out["best_ratio"],
                                      "rounds": len(out["rounds"])})
                if out["best_c"] is not None and np.linalg.norm(out["best_c"]) > 1e-12:
                    current = np.asarray(out["best_c"], dtype=float)
                continue
            # Both budgets are capped in FUNCTION EVALUATIONS: Powell's outer
            # iteration count alone is not a bounded budget in high dimension.
            options = {"maxiter": int(maxiter), "maxfev": int(maxiter) * 4, "disp": False}
            if name == "Nelder-Mead":
                options.update({"xatol": 1e-9, "fatol": 1e-12, "adaptive": True})
            else:
                options.update({"xtol": 1e-8, "ftol": 1e-10})
            res = minimize(negative_ratio, current, method=name, options=options)
            evaluations += int(getattr(res, "nfev", 0) or 0)
            cand = np.asarray(res.x, dtype=float)
            n = float(np.linalg.norm(cand))
            if n > 1e-12:
                current = cand / n
        for candidate in (c0, current):
            value = -negative_ratio(candidate)
            if value > best_ratio:
                nc = float(np.linalg.norm(candidate))
                best_ratio, best_c = value, candidate / (nc if nc > 0 else 1.0)
    return best_ratio, best_c, evaluations, {
        "lp_stage_log": lp_rounds_log,
        "lp_objective_consistency_max_abs_error": float(lp_consistency),
    }


# --------------------------------------------------------------------------
# active-cell LP ascent
# --------------------------------------------------------------------------
# Inside one fiber the map c -> F = B c is linear, and every quantity in the
# objective is piecewise linear in F:
#
#   2 L(S) = max_a res_S(a) - min_a res_S(a),     res_S linear in F,
#   delta_square = max_{i,u,v} ( max_z g - min_z g ),  g linear in F,
#   score_i = max_u Q_i(u) - min_u Q_i(u),        Q_i linear in F.
#
# FIXING the active pattern -- which u attains each score max/min, which set S the
# Top-C rule selects, which actions attain the max/min of res_S and of one
# competitor res_T -- turns all of them into linear forms, and the whole cell into
# a polyhedron.  Maximizing  [res_S(a_S) - res_S(b_S)] - [res_T(a_T) - res_T(b_T)]
# over that polyhedron with delta_square <= 1 is a plain LP in the d fiber
# coordinates, with NO constraints tying it to rank-one: rank-one is already free
# because we never leave the fiber.
#
# The LP objective is a LOWER bound on 2D at its own solution (the fixed T need
# not be the argmin there, and the fixed pattern need not still be active), so a
# solution is never a claim -- it is re-evaluated, and only the exact rational
# recheck decides anything.  Iterating "solve LP -> re-read the active pattern"
# is a cell-wise ascent, not a global optimizer.
def linear_forms(model: FloatModel, B: np.ndarray) -> dict:
    """Linear forms of the D6 quantities in the fiber coordinates c (F = B c)."""
    m, K = model.m, model.K
    N = K ** m
    d = B.shape[1]
    strides = [K ** (m - 1 - j) for j in range(m)]
    ctxs = list(itertools.product(range(K), repeat=m - 1))
    acts = list(itertools.product(range(K), repeat=m))
    # Q_i(u) as a row in c
    Q = np.zeros((m, K, d))
    ctx_index = np.zeros((m, len(ctxs)), dtype=int)
    for i in range(m):
        others = [j for j in range(m) if j != i]
        for t, z in enumerate(ctxs):
            base = sum(strides[j] * z[e] for e, j in enumerate(others))
            ctx_index[i, t] = base
            weight = model.ctx_weight[i][t]
            for u in range(K):
                Q[i, u] += weight * B[base + strides[i] * u]
    baseline = sum(model.q[0][u] * Q[0, u] for u in range(K))
    comp = Q - baseline[None, None, :]
    return {"Q": Q, "comp": comp, "baseline": baseline, "strides": strides,
            "ctxs": ctxs, "ctx_index": ctx_index, "acts": acts, "B": B, "d": d}


def residual_rows(forms: dict, S: Sequence[int]) -> np.ndarray:
    R = forms["B"].copy()
    for n, a in enumerate(forms["acts"]):
        for i in S:
            R[n] -= forms["comp"][i, a[i]]
    return R


def delta_pattern_rows(model: FloatModel, forms: dict, current: np.ndarray):
    """delta_square <= 1 in active-pattern form.

    ``delta_square = max_{i,u,v} (max_z g - min_z g)`` with ``g`` linear.  Writing
    it with all ordered context pairs costs ``K^(2m-2)`` rows per (i,u,v) and is
    hopeless past m=4.  Fixing the argmax/argmin context per (i,u,v) at the current
    point instead costs ``2 K^(m-1) + 1`` rows and is exactly the same active-cell
    device used for the losses: one row ``g(z+) - g(z-) <= 1`` plus the rows that
    keep ``z+`` and ``z-`` extremal.  It restricts the cell, never the exactness --
    every LP output is re-evaluated from scratch and only the exact rational recheck
    decides anything.
    """
    le_one, le_zero = [], []
    for i in range(model.m):
        base = forms["ctx_index"][i]
        for u in range(model.K):
            for v in range(u + 1, model.K):
                G = forms["B"][base + forms["strides"][i] * u] - \
                    forms["B"][base + forms["strides"][i] * v]
                values = G @ current
                hi, lo = int(values.argmax()), int(values.argmin())
                le_one.append(G[hi] - G[lo])
                le_zero.append(-(G[hi][None, :] - G))
                le_zero.append(-(G - G[lo][None, :]))
    return np.asarray(le_one, dtype=float), np.concatenate(le_zero, axis=0)


def cell_lp_ascent(model: FloatModel, B: np.ndarray, c0: np.ndarray, *, rounds: int,
                   box: float) -> dict:
    from scipy.optimize import linprog

    m, K = model.m, model.K
    forms = linear_forms(model, B)
    subsets = model.subsets
    current = np.asarray(c0, dtype=float)
    best_c, best_ratio = current.copy(), (model.ratio((B @ current).reshape((K,) * m)) or 0.0)
    history = []
    consistency = 0.0
    for round_index in range(int(rounds)):
        F = (B @ current).reshape((K,) * m)
        details = model.evaluate(F)
        sl = model.slices(F)
        R = model.response(sl)
        umax = [int(np.argmax(R[i])) for i in range(m)]
        umin = [int(np.argmin(R[i])) for i in range(m)]
        S = tuple(details["selected"])
        losses = {}
        for T in subsets:
            RT = residual_rows(forms, T)
            values = RT @ current
            losses[T] = (0.5 * (values.max() - values.min()), int(values.argmax()),
                         int(values.argmin()), RT)
        T_star = min(subsets, key=lambda T: losses[T][0])
        if T_star == S:
            others = [T for T in subsets if T != S]
            if not others:
                break
            T_star = min(others, key=lambda T: losses[T][0])
        _, aS, bS, RS = losses[S]
        _, aT, bT, RT = losses[T_star]
        objective = (RS[aS] - RS[bS]) - (RT[aT] - RT[bT])
        # sanity: at the current point the LP objective must equal the evaluated 2D
        # whenever T_star is the true argmin competitor
        consistency = max(consistency, abs(float(objective @ current)
                                           - 2.0 * details["regret"]))
        delta_le_one, delta_le_zero = delta_pattern_rows(model, forms, current)
        A = [delta_le_one, delta_le_zero]
        b = [np.ones(delta_le_one.shape[0]), np.zeros(delta_le_zero.shape[0])]
        pattern = []
        for i in range(m):
            for u in range(K):
                pattern.append(-(forms["Q"][i, umax[i]] - forms["Q"][i, u]))
                pattern.append(-(forms["Q"][i, u] - forms["Q"][i, umin[i]]))
        score = [forms["Q"][i, umax[i]] - forms["Q"][i, umin[i]] for i in range(m)]
        for i in S:
            for j in range(m):
                if j not in S:
                    pattern.append(-(score[i] - score[j]))
        pattern.extend(list(-(RS[aS][None, :] - RS)))
        pattern.extend(list(-(RS - RS[bS][None, :])))
        pattern.extend(list(-(RT[aT][None, :] - RT)))
        pattern.extend(list(-(RT - RT[bT][None, :])))
        A.append(np.asarray(pattern, dtype=float))
        b.append(np.zeros(len(pattern)))
        res = linprog(-objective, A_ub=np.concatenate(A, axis=0),
                      b_ub=np.concatenate(b), bounds=[(-box, box)] * forms["d"],
                      method="highs")
        entry = {"round": round_index, "selected": list(S), "competitor": list(T_star),
                 "lp_status": int(res.status), "lp_message": str(res.message)[:80]}
        if res.status != 0 or res.x is None:
            history.append(entry)
            break
        vertex = np.asarray(res.x, dtype=float)
        if float(np.linalg.norm(vertex)) < 1e-12:
            entry["outcome"] = "LP_RETURNED_ORIGIN"
            history.append(entry)
            break
        # An LP optimum sits on a vertex, where the active pattern is maximally
        # degenerate: ties let the evaluator's Top-C tie-break pick a different S,
        # so the ratio AT the vertex can collapse even though the LP objective grew.
        # Search the segment from the incumbent to the vertex instead of trusting
        # the vertex itself.  This keeps the ascent monotone in the real objective.
        ratio, candidate = best_ratio, None
        for step in (1.0, 0.99, 0.95, 0.9, 0.75, 0.5, 0.35, 0.2, 0.1, 0.05, 0.02):
            point = current * (1.0 - step) + step * vertex
            norm = float(np.linalg.norm(point))
            if norm < 1e-12:
                continue
            point = point / norm
            value = model.ratio((B @ point).reshape((K,) * m))
            if value is not None and value > ratio + 1e-14:
                ratio, candidate = float(value), point
        entry["ratio"] = float(ratio)
        entry["at_box_bound"] = bool(np.max(np.abs(vertex)) >= box * (1 - 1e-9))
        entry["lp_objective"] = float(objective @ vertex)
        history.append(entry)
        if candidate is None:
            break
        best_ratio, best_c = ratio, candidate
        current = candidate
    return {"best_ratio": float(best_ratio), "best_c": best_c, "rounds": history,
            "objective_consistency_max_abs_error": float(consistency)}


def differential_evolution_search(model: FloatModel, B: np.ndarray, *, seed: int,
                                  maxiter: int, popsize: int):
    from scipy.optimize import differential_evolution

    K, m = model.K, model.m
    shape = (K,) * m

    def negative_ratio(c):
        norm = float(np.linalg.norm(c))
        if norm < 1e-12:
            return 0.0
        r = model.ratio((B @ (c / norm)).reshape(shape))
        return 0.0 if r is None else -r

    res = differential_evolution(
        negative_ratio, bounds=[(-1.0, 1.0)] * B.shape[1], seed=int(seed),
        maxiter=int(maxiter), popsize=int(popsize), tol=1e-10, polish=False,
        init="sobol", updating="deferred", workers=1,
    )
    c = np.asarray(res.x, dtype=float)
    norm = float(np.linalg.norm(c))
    c = c / (norm if norm > 1e-12 else 1.0)
    return float(-res.fun), c, int(res.nfev)


# --------------------------------------------------------------------------
# self tests
# --------------------------------------------------------------------------
def self_test(m: int, alphabet: int, reference: str, seed: int, denominator: int,
              nullspace_tol: float) -> dict:
    rng = np.random.default_rng(int(seed))
    q_rows = reference_rows(m, alphabet, reference)
    model = FloatModel(m, alphabet, q_rows)
    acts = actions(m, alphabet)
    N = alphabet ** m
    report: dict = {}

    # 0. float evaluator agrees with the shared exact evaluator.
    worst = 0.0
    for _ in range(3):
        world = {a: Fraction(int(rng.integers(-9, 10)), int(rng.integers(1, 5))) for a in acts}
        exact = evaluate_candidate(world, q_rows, m, alphabet)
        F = np.asarray([float(world[a]) for a in acts], dtype=float).reshape((alphabet,) * m)
        got = model.evaluate(F)
        worst = max(worst, abs(got["delta_square"] - float(Fraction(exact["delta_square"]))))
        worst = max(worst, abs(2.0 * got["regret"] - float(Fraction(exact["doubled_decision_gap"]))))
    report["float_vs_exact_evaluator_max_abs_error"] = worst
    report["float_vs_exact_evaluator_ok"] = bool(worst < 1e-9)

    # 0b. cross-check against the independent float evaluator of the half-factor lab.
    try:
        from scripts.run_d6_half_factor_lemma_falsification import evaluate_float
        F = rng.standard_normal((alphabet,) * m)
        mine = model.evaluate(F)
        theirs = evaluate_float(F, np.asarray([[float(v) for v in r] for r in q_rows]), m // 2)
        err = max(abs(mine["delta_square"] - float(theirs["delta_square"])),
                  abs(mine["regret"] - float(theirs["true_decision_regret"])))
        report["float_vs_half_factor_lab_max_abs_error"] = float(err)
        report["float_vs_half_factor_lab_ok"] = bool(err < 1e-9)
    except Exception as exc:  # pragma: no cover - diagnostic only
        report["float_vs_half_factor_lab_ok"] = False
        report["float_vs_half_factor_lab_error"] = f"{type(exc).__name__}: {exc}"

    # 1. nullspace construction: F = B c is numerically rank-one at every coordinate.
    lam = sample_lambdas(m, alphabet, 4, "random", seed + 1, include_structured=False)
    worst_minor, worst_sigma, dims = 0.0, 0.0, []
    exact_ok = True
    exact_failures = []
    for raw in lam:
        lam_int = rationalize_lambda(raw, denominator)
        perp = [perp_basis_exact(row) for row in lam_int]
        A = fiber_rows(m, alphabet, perp, as_float=True)
        B = nullspace_float(A, N, nullspace_tol)
        dims.append(int(B.shape[1]))
        if B.shape[1] == 0:
            continue
        c = rng.standard_normal(B.shape[1])
        F = (B @ c).reshape((alphabet,) * m)
        minor, sigma = model.rank_one_defect(F)
        scale = float(np.abs(F).max()) or 1.0
        worst_minor = max(worst_minor, minor / (scale * scale))
        worst_sigma = max(worst_sigma, sigma)
        # exact leg: rationalize then exactly re-project, then check exact minors.
        basis = closed_form_basis_exact(m, alphabet, lam_int)
        target = [Fraction(float(v)).limit_denominator(denominator) for v in (F / scale).ravel()]
        projected, _ = exact_project(basis, target)
        world = {a: projected[idx] for idx, a in enumerate(acts)}
        ok, failure = rank_one_check(world, response_table(world, q_rows, acts), m, alphabet)
        exact_ok = exact_ok and ok
        if not ok:
            exact_failures.append(failure)
    report["fiber_dims_sampled"] = dims
    report["closed_form_dim"] = closed_form_fiber_dim(m, alphabet)
    report["closed_form_dim_matches_float_nullspace"] = bool(
        all(d == closed_form_fiber_dim(m, alphabet) for d in dims))
    report["float_rankone_max_scaled_minor"] = worst_minor
    report["float_rankone_max_sigma2_over_sigma1"] = worst_sigma
    report["float_rankone_ok"] = bool(worst_minor < 1e-8 and worst_sigma < 1e-7)
    report["exact_projection_rankone_ok"] = bool(exact_ok)
    report["exact_projection_failures"] = exact_failures

    # 2. gate is not vacuous: a deliberately rank-two world must be rejected.
    rank_two_world = {a: Fraction(int(rng.integers(-9, 10))) for a in acts}
    ok2, failure2 = rank_one_check(rank_two_world, response_table(rank_two_world, q_rows, acts), m, alphabet)
    F2 = np.asarray([float(rank_two_world[a]) for a in acts], dtype=float).reshape((alphabet,) * m)
    minor2, sigma2 = model.rank_one_defect(F2)
    report["rank_two_world_rejected_exactly"] = bool(not ok2)
    report["rank_two_world_first_nonzero_minor"] = failure2
    report["rank_two_world_float_max_minor"] = minor2
    report["rank_two_world_float_sigma2_over_sigma1"] = sigma2
    report["rank_two_gate_ok"] = bool((not ok2) and sigma2 > 1e-6)

    # 3. exact Gaussian fiber vs the closed-form basis (only affordable for small K^m).
    if N <= 128:
        lam_int = rationalize_lambda(sample_lambdas(m, alphabet, 1, "random", seed + 7,
                                                    include_structured=False)[0], denominator)
        perp = [perp_basis_exact(row) for row in lam_int]
        rows = fiber_rows(m, alphabet, perp, as_float=False)
        gauss = frac_nullspace(rows, N)
        closed = closed_form_basis_exact(m, alphabet, lam_int)
        stacked = [list(v) for v in gauss] + [[Fraction(x) for x in col] for col in closed]
        _, pivots = frac_rref(stacked, N)
        report["exact_gauss_fiber_dim"] = len(gauss)
        report["exact_closed_form_dim"] = len(closed)
        report["exact_stacked_rank"] = len(pivots)
        # equal stacked rank proves the closed-form columns lie inside the exact
        # fiber (soundness); equal dimensions prove they span it (completeness).
        report["closed_form_equals_exact_fiber"] = bool(
            len(pivots) == len(gauss) == len(closed))
    # 4. corner references form one relabeling orbit (justifies the corner-sweep
    #    interpretation).  Checked EXACTLY: relabel each coordinate's alphabet so a
    #    random corner becomes the all-zero corner and require every exact quantity
    #    to be unchanged.
    orbit_mismatches = []
    py_rng = random.Random(int(seed) + 31)
    for _ in range(3):
        world = {a: Fraction(py_rng.randint(-9, 9), py_rng.randint(1, 4)) for a in acts}
        for _ in range(3):
            corner = tuple(py_rng.randrange(alphabet) for _ in range(m))
            relabel = []
            for i in range(m):
                order = list(range(alphabet))
                order[0], order[corner[i]] = order[corner[i]], order[0]
                back = [0] * alphabet
                for new, old_symbol in enumerate(order):
                    back[new] = old_symbol
                relabel.append(back)
            moved = {a: world[tuple(relabel[i][a[i]] for i in range(m))] for a in acts}
            got = evaluate_candidate(moved, corner_reference_rows(m, alphabet, (0,) * m),
                                     m, alphabet)
            ref = evaluate_candidate(world, corner_reference_rows(m, alphabet, corner),
                                     m, alphabet)
            keys = ("delta_square", "doubled_decision_gap", "m_minus_one_delta",
                    "selected_loss", "optimal_loss", "rank_one_verified", "strict_violation")
            diff = {k: [got[k], ref[k]] for k in keys if got[k] != ref[k]}
            if diff:
                orbit_mismatches.append({"corner": list(corner), "difference": diff})
    report["corner_orbit_mismatches"] = orbit_mismatches
    report["corner_references_single_orbit_ok"] = bool(not orbit_mismatches)

    report["all_ok"] = bool(
        report["float_vs_exact_evaluator_ok"] and report["float_rankone_ok"]
        and report["exact_projection_rankone_ok"] and report["rank_two_gate_ok"]
        and report["closed_form_dim_matches_float_nullspace"]
        and report.get("closed_form_equals_exact_fiber", True)
        and report["corner_references_single_orbit_ok"]
    )
    return report


# --------------------------------------------------------------------------
# main protocol
# --------------------------------------------------------------------------
def corner_reference_rows(m: int, alphabet: int,
                          corner: Sequence[int]) -> tuple[tuple[Fraction, ...], ...]:
    """Deterministic product reference q = delta_{corner}.

    Chain D's stated reference assumption is "explicit nonnegative normalized
    product weights" -- nonnegative, not strictly positive -- so a point mass is
    admissible, and the deterministic product references are exactly the VERTICES
    of the admissible reference set.
    """
    return tuple(tuple(Fraction(1) if u == corner[i] else Fraction(0)
                       for u in range(alphabet)) for i in range(m))


def run(args: argparse.Namespace, *, q_rows: Sequence[Sequence[Fraction]] | None = None,
        reference_label: str | None = None) -> dict:
    m, K = int(args.m), int(args.alphabet)
    denominator = int(args.denominator)
    if q_rows is None:
        q_rows = reference_rows(m, K, args.reference)
    model = FloatModel(m, K, q_rows, min_topc_margin=float(getattr(args, "min_topc_margin", 0.0)))
    acts = actions(m, K)
    N = K ** m
    started = time.time()

    try:
        import scipy.optimize  # noqa: F401
    except ModuleNotFoundError:
        return {
            "protocol_version": PROTOCOL_VERSION,
            "status": "BLOCKED_REQUIRED_RUNTIME",
            "reason": "this protocol needs scipy.optimize derivative-free minimizers",
            "m": m, "alphabet": K,
        }

    raw_lambdas = sample_lambdas(m, K, int(args.fibers), args.lambda_mode, int(args.seed),
                                 include_structured=not bool(args.no_structured))
    rng = np.random.default_rng(int(args.seed) + 101)

    fibers: list[dict] = []
    seen: set = set()
    duplicates = degenerate = undefined = 0
    for index, raw in enumerate(raw_lambdas):
        lam_int = rationalize_lambda(raw, denominator)
        if lam_int is None:
            degenerate += 1
            continue
        key = tuple(lam_int)
        if key in seen:
            duplicates += 1
            continue
        seen.add(key)
        perp = [perp_basis_exact(row) for row in lam_int]
        A = fiber_rows(m, K, perp, as_float=True)
        method = str(getattr(args, "nullspace_method", "auto"))

        fiber_kind = str(getattr(args, "fiber_kind", "centred"))

        def _closed_form_float_basis():
            cols = (closed_form_raw_basis_exact(m, K, lam_int)
                    if fiber_kind == "raw"
                    else closed_form_basis_exact(m, K, lam_int))
            M = np.asarray([[float(x) for x in col] for col in cols], dtype=float).T
            Q, _ = np.linalg.qr(M)
            return np.ascontiguousarray(Q)

        if fiber_kind == "raw":
            # The numerical nullspace route computes V_lambda, the CENTRED
            # fibre.  The raw fibre is a proper subspace of it, so it must come
            # from its own closed-form basis; there is no nullspace shortcut.
            B = _closed_form_float_basis()
            basis_source = "raw_closed_form_qr"
        elif method == "closed_form":
            B = _closed_form_float_basis()
            basis_source = "closed_form_qr"
        else:
            try:
                B = nullspace_float(A, N, float(args.nullspace_tol))
                basis_source = (NULLSPACE_BACKEND_USED[-1]
                                if NULLSPACE_BACKEND_USED else "numpy_gesdd")
            except Exception as exc:
                if method == "svd":
                    raise
                # macOS Accelerate's gesdd can fail to converge on ordinary
                # matrices.  The exact closed-form columns provably lie in
                # V_lambda, so falling back to them is sound; only completeness
                # of the float span depends on the dimension identity, which is
                # recorded per fiber.
                B = _closed_form_float_basis()
                basis_source = "closed_form_qr_after_" + type(exc).__name__
        dim = int(B.shape[1])
        record = {
            "fiber_index": index,
            "lambda_int": [list(row) for row in lam_int],
            "lambda_angles": (
                [float(math.atan2(row[1], row[0]) % math.pi) for row in lam_int] if K == 3 else None
            ),
            "nullspace_dim": dim,
            "float_basis_source": basis_source,
            "fiber_kind": fiber_kind,
            "closed_form_dim": (closed_form_raw_fiber_dim(m, K)
                                if fiber_kind == "raw"
                                else closed_form_fiber_dim(m, K)),
            "nullspace_dim_equals_closed_form": bool(
                dim == (closed_form_raw_fiber_dim(m, K) if fiber_kind == "raw"
                        else closed_form_fiber_dim(m, K))),
        }
        if dim <= 1:
            record["skipped"] = "DEGENERATE_FIBER_DIM_LE_1"
            record["best_float_ratio"] = None
            fibers.append(record)
            degenerate += 1
            continue
        ratio, best_c, evaluations, extra = search_fiber(
            model, B, int(args.starts), rng, args.optimizer, int(args.maxiter),
            lp_rounds=int(args.lp_rounds), lp_box=float(args.lp_box),
            de_maxiter=int(args.de_maxiter), de_popsize=int(args.de_popsize),
        )
        record["objective_evaluations"] = evaluations
        if extra["lp_stage_log"]:
            record["lp_stage_log"] = extra["lp_stage_log"]
            record["lp_objective_consistency_max_abs_error"] = \
                extra["lp_objective_consistency_max_abs_error"]
        record["best_float_ratio"] = float(ratio)
        if best_c is None:
            # Every start had 2D = 0 or delta_square = 0 (UNDEFINED); the fiber is
            # recorded with objective 0 and is never eligible for the exact leg.
            record["best_float_ratio"] = 0.0
            record["no_positive_objective"] = True
            undefined += 1
            fibers.append(record)
            continue
        F = (B @ best_c).reshape((K,) * m)
        details = model.evaluate(F)
        minor, sigma = model.rank_one_defect(F)
        scale = float(np.abs(F).max()) or 1.0
        record["float_delta_square"] = float(details["delta_square"])
        record["float_selected"] = list(details["selected"])
        record["float_rankone_max_scaled_minor"] = float(minor / (scale * scale))
        record["float_rankone_sigma2_over_sigma1"] = float(sigma)
        record["_best_c"] = best_c
        record["_basis"] = B
        record["_lambda_int"] = lam_int
        fibers.append(record)

    ranked = sorted(
        (f for f in fibers if f.get("_best_c") is not None),
        key=lambda f: -float(f["best_float_ratio"]),
    )[: int(args.exact_leads)]

    exact_counterexample = None
    exact_verified = 0
    internal_failure = None
    best_exact_ratio: Fraction | None = None
    best_witness_ratio: Fraction | None = None
    tightness_witness = None
    best_strict_ratio: Fraction | None = None
    best_admissible_ratio: Fraction | None = None
    strict_witness = None
    for record in ranked:
        lam_int = record["_lambda_int"]
        B = record["_basis"]
        best_c = record["_best_c"]
        F = (B @ best_c).reshape((K,) * m)
        scale = float(np.abs(F).max()) or 1.0
        basis_kind = args.exact_basis
        if basis_kind == "auto":
            # The closed form is exact and, for non-degenerate lambda, complete; the
            # cubic Fraction elimination is only needed when the closed form provably
            # misses part of this fiber and the system is small enough to eliminate.
            if record["nullspace_dim_equals_closed_form"] or N > int(args.gauss_limit):
                basis_kind = "closed_form"
            else:
                basis_kind = "gauss"
        t0 = time.time()
        if basis_kind == "gauss":
            basis = frac_nullspace(fiber_rows(m, K, [perp_basis_exact(r) for r in lam_int],
                                              as_float=False), N)
        else:
            basis = closed_form_basis_exact(m, K, lam_int)
        record["exact_basis_kind"] = basis_kind
        record["exact_basis_dim"] = len(basis)
        record["exact_basis_covers_fiber"] = bool(len(basis) >= record["nullspace_dim"])
        record["exact_basis_seconds"] = round(time.time() - t0, 3)
        if not basis:
            record["exact_status"] = "EMPTY_EXACT_BASIS"
            continue
        # Snapping a float lead to rationals moves it, and the objective is
        # piecewise linear: a sharp optimum can be snapped across a kink and lose
        # all of its regret.  Both snaps below land EXACTLY inside V_lambda, so
        # trying several and keeping the best is sound, not p-hacking: each
        # attempt is an independent exact witness candidate, recorded in full.
        basis_float = np.asarray([[float(x) for x in col] for col in basis], dtype=float).T
        coeff_float = np.linalg.lstsq(basis_float, (F / scale).ravel(), rcond=None)[0]
        ladder = [denominator * (4 ** step) for step in range(max(1, int(args.denominator_ladder)))]
        kinds = ["project", "coefficients"] if args.snap == "both" else [args.snap]
        attempts = []
        best_attempt = None
        exact = None
        world_vec = None
        for den in ladder:
            for kind in kinds:
                t0 = time.time()
                if kind == "project":
                    target = [Fraction(float(v)).limit_denominator(den)
                              for v in (F / scale).ravel()]
                    candidate, _ = exact_project(basis, target)
                else:
                    candidate, _ = exact_coefficient_snap(basis, coeff_float, den)
                snap_seconds = time.time() - t0
                if candidate is None or all(v == 0 for v in candidate):
                    attempts.append({"snap": kind, "denominator": den,
                                     "status": "EXACT_SNAP_DEGENERATE"})
                    continue
                candidate_world = {a: candidate[idx] for idx, a in enumerate(acts)}
                t0 = time.time()
                candidate_exact = evaluate_candidate(candidate_world, q_rows, m, K)
                delta = Fraction(candidate_exact["delta_square"])
                ratio_exact = (None if delta == 0 else
                               Fraction(candidate_exact["doubled_decision_gap"]) / ((m - 1) * delta))
                attempts.append({
                    "snap": kind, "denominator": den,
                    "snap_seconds": round(snap_seconds, 3),
                    "evaluate_seconds": round(time.time() - t0, 3),
                    "max_denominator": max(v.denominator for v in candidate),
                    "rank_one_verified": bool(candidate_exact["rank_one_verified"]),
                    "strict_violation": bool(candidate_exact["strict_violation"]),
                    "exact_ratio": None if ratio_exact is None else fraction_text(ratio_exact),
                    "exact_ratio_float": None if ratio_exact is None else float(ratio_exact),
                })
                better = (best_attempt is None
                          or (ratio_exact is not None
                              and (best_attempt[0] is None or ratio_exact > best_attempt[0])))
                if better:
                    best_attempt = (ratio_exact, candidate, candidate_exact)
                if candidate_exact["rank_one_verified"] and candidate_exact["strict_violation"]:
                    break
            if best_attempt is not None and best_attempt[2]["strict_violation"] \
                    and best_attempt[2]["rank_one_verified"]:
                break
        record["exact_attempts"] = attempts
        if best_attempt is None:
            record["exact_status"] = "EXACT_SNAP_DEGENERATE"
            continue
        ratio_exact, world_vec, exact = best_attempt
        world = {a: world_vec[idx] for idx, a in enumerate(acts)}
        record["exact_rank_one_verified"] = bool(exact["rank_one_verified"])
        record["exact_strict_violation"] = bool(exact["strict_violation"])
        record["exact_delta_square"] = exact["delta_square"]
        record["exact_doubled_decision_gap"] = exact["doubled_decision_gap"]
        record["exact_m_minus_one_delta"] = exact["m_minus_one_delta"]
        record["exact_max_denominator"] = max(v.denominator for v in world_vec)
        if ratio_exact is None:
            record["exact_ratio"] = None
            record["exact_status"] = "UNDEFINED_ZERO_DELTA_SQUARE"
        else:
            record["exact_ratio"] = fraction_text(ratio_exact)
            record["exact_ratio_float"] = float(ratio_exact)
            record["exact_status"] = "EXACT_RECHECK_COMPLETE"
            if best_exact_ratio is None or ratio_exact > best_exact_ratio:
                best_exact_ratio = ratio_exact
        if not exact["rank_one_verified"]:
            # By construction every basis column lies in V_lambda exactly, so this
            # can only be an implementation defect.  Fail closed rather than
            # silently downgrading the lead.
            internal_failure = {
                "fiber_index": record["fiber_index"],
                "lambda_int": record["lambda_int"],
                "rank_one_failure": exact["rank_one_failure"],
            }
            continue
        exact_verified += 1
        # StrictTopC (LeanD6ContrastRankPhaseDefinitionsV2): every selected coordinate
        # must have STRICTLY larger response oscillation than every unselected one.
        # A witness sitting on a Top-C tie is decided by tie-breaking, not by the
        # geometry, so strict and non-strict extrema are tracked separately.
        _scores = [Fraction(t) for t in exact.get("scores", [])]
        _sel = set(exact.get("selected", []))
        if _scores and _sel and len(_sel) < len(_scores):
            _lo = min(_scores[i] for i in range(len(_scores)) if i in _sel)
            _hi = max(_scores[i] for i in range(len(_scores)) if i not in _sel)
            strict_top_c = bool(_lo > _hi)
            score_margin = fraction_text(_lo - _hi)
        else:
            strict_top_c = False
            score_margin = None
        record["strict_top_c"] = strict_top_c
        record["top_c_score_margin"] = score_margin
        if strict_top_c and ratio_exact is not None and (
                best_strict_ratio is None or ratio_exact > best_strict_ratio):
            best_strict_ratio = ratio_exact
            strict_witness = {
                "fiber_index": record["fiber_index"],
                "lambda_int": record["lambda_int"],
                "exact_ratio": fraction_text(ratio_exact),
                "exact_ratio_float": float(ratio_exact),
                "top_c_score_margin": score_margin,
                "exact": exact,
                "q": q_payload(q_rows),
                "world": world_payload(world, acts),
            }
        if ratio_exact is not None and (best_witness_ratio is None
                                        or ratio_exact > best_witness_ratio):
            # Additive record only: the exactly-verified rank-one world attaining the
            # largest exact ratio seen.  A ratio of exactly 1 is NOT a counterexample;
            # it is a sharpness witness for 2D <= (m-1) delta_square and is recorded so
            # the equality case can be audited independently.
            best_witness_ratio = ratio_exact
            tightness_witness = {
                "fiber_index": record["fiber_index"],
                "lambda_int": record["lambda_int"],
                "exact_ratio": fraction_text(ratio_exact),
                "exact_ratio_float": float(ratio_exact),
                "tight_equality": bool(ratio_exact == 1),
                "exact": exact,
                "q": q_payload(q_rows),
                "world": world_payload(world, acts),
            }
        if float(getattr(args, "min_topc_margin", 0.0)) > 0.0 and not strict_top_c:
            # The float gate can still be snapped across a kink onto a tie.  With the
            # StrictTopC gate on, such a lead is NOT an admissible counterexample.
            record["exact_status"] = "SKIPPED_NON_STRICT_TOPC"
            continue
        if ratio_exact is not None and (best_admissible_ratio is None
                                        or ratio_exact > best_admissible_ratio):
            best_admissible_ratio = ratio_exact
        if exact["strict_violation"]:
            exact_counterexample = {
                "fiber_index": record["fiber_index"],
                "lambda_int": record["lambda_int"],
                "exact": exact,
                "q": q_payload(q_rows),
                "world": world_payload(world, acts),
            }
            break

    for record in fibers:
        record.pop("_best_c", None)
        record.pop("_basis", None)
        record.pop("_lambda_int", None)

    searched = [f for f in fibers if f.get("best_float_ratio") is not None]
    best_float = max((float(f["best_float_ratio"]) for f in searched), default=None)
    if internal_failure is not None:
        status = "INTERNAL_CONSISTENCY_FAILURE_EXACT_RANKONE"
    elif exact_counterexample is not None:
        status = "KILLED"
    elif exact_verified == 0:
        status = "INCONCLUSIVE_NO_EXACT_RANKONE_LEAD"
    else:
        status = "NO_EXACT_COUNTEREXAMPLE_FROM_NUMERICAL_LEADS"
    return {
        "protocol_version": (PROTOCOL_VERSION_HAMMER
                             if ("lp" in args.optimizer or "de" in args.optimizer)
                             else PROTOCOL_VERSION),
        "evidence_class": EVIDENCE_CLASS,
        "development_only": True,
        "stage": "B3_direct_rank_one_linear_fiber",
        "m": m,
        "alphabet": K,
        "reference_mode": reference_label or args.reference,
        "seed": int(args.seed),
        "lambda_mode": args.lambda_mode,
        "fibers_requested": int(args.fibers),
        "fibers_constructed": len(fibers),
        "fibers_searched": len(searched),
        "fibers_skipped_duplicate": duplicates,
        "fibers_skipped_degenerate": degenerate,
        "fibers_no_positive_objective": undefined,
        "starts_per_fiber": int(args.starts),
        "optimizer": args.optimizer,
        "maxiter": int(args.maxiter),
        "rational_denominator": denominator,
        "snap": args.snap,
        "denominator_ladder": int(args.denominator_ladder),
        "exact_leads_requested": int(args.exact_leads),
        "exact_leads_evaluated": len(ranked),
        "exact_rankone_verified_count": exact_verified,
        "best_float_ratio": best_float,
        "best_exact_ratio": None if best_exact_ratio is None else fraction_text(best_exact_ratio),
        "best_exact_ratio_float": None if best_exact_ratio is None else float(best_exact_ratio),
        "wall_clock_seconds": round(time.time() - started, 3),
        "internal_failure": internal_failure,
        "counterexample": exact_counterexample,
        "tightness_witness": tightness_witness,
        "best_strict_top_c_exact_ratio": (None if best_strict_ratio is None
                                          else fraction_text(best_strict_ratio)),
        "strict_top_c_witness": strict_witness,
        "float_basis_sources": sorted({f.get("float_basis_source")
                                       for f in fibers if f.get("float_basis_source")}),
        "nullspace_method": str(getattr(args, "nullspace_method", "auto")),
        "strict_gate_active": bool(float(getattr(args, "min_topc_margin", 0.0)) > 0.0),
        "min_topc_margin": float(getattr(args, "min_topc_margin", 0.0)),
        "best_exact_ratio_admissible": (None if best_admissible_ratio is None
                                        else fraction_text(best_admissible_ratio)),
        "best_exact_ratio_admissible_float": (None if best_admissible_ratio is None
                                              else float(best_admissible_ratio)),
        "gate_note": (
            "With strict_gate_active true, best_exact_ratio may come from a lead whose "
            "exact snap landed on a Top-C tie; such a lead is NOT an admissible "
            "counterexample and is recorded as SKIPPED_NON_STRICT_TOPC. Read "
            "best_exact_ratio_admissible, not best_exact_ratio, when the gate is on."
            if float(getattr(args, "min_topc_margin", 0.0)) > 0.0 else
            "Strict Top-C gate disabled; ties are admissible and best_exact_ratio is the "
            "unrestricted maximum."),
        "status": status,
        "fibers": fibers,
        "interpretation": (
            "Each lambda fiber V_lambda is an exact linear subspace of raw worlds whose "
            "interaction-contrast profiles have rank at most one at every coordinate, so the "
            "inner search is unconstrained and the exact recheck is rank-one BY CONSTRUCTION. "
            "Only the exact-rational leg (2D > (m-1) delta_square in Fraction arithmetic) can "
            "kill the law. Surviving this gate is NOT a proof: the lambda sweep is a finite "
            "seeded sample of a continuum, each fiber gets only a finite derivative-free search "
            "of a nonsmooth objective, and rationalization moves every lead. This artifact is "
            "NUMERICAL EVIDENCE, never a compiled or proved statement."
        ),
    }


def run_corner_sweep(args: argparse.Namespace) -> dict:
    """Exhaustive sweep over the vertices of the admissible product-reference set.

    NOTE ON WHAT THIS CAN AND CANNOT SHOW.  All ``K^m`` corner references lie in a
    SINGLE orbit of the per-coordinate symbol-relabeling group: relabeling each
    coordinate's alphabet so that ``z*`` becomes the all-zero corner is an exact
    isomorphism of the whole problem (it preserves delta_square, both losses, the
    Top-C score, the selection, and rank-one membership, which is anchor- and
    q-independent).  That equivalence is checked exactly in ``--self-test``.  So
    the SUPREMUM of the ratio is identical at every corner and ``point0`` is not
    special.  What the sweep genuinely adds is search diversity: the lambda sample
    is NOT equivariant under that relabeling, so different corners explore
    different parts of the same union of fibers.  Differences between corners in
    this artifact are search noise, not geometry.
    """
    import copy

    m, K = int(args.m), int(args.alphabet)
    corners = list(itertools.product(range(K), repeat=m))
    lo, hi = 0, len(corners)
    if args.corner_range:
        text = str(args.corner_range).split(":")
        lo = int(text[0] or 0)
        hi = int(text[1] or len(corners)) if len(text) > 1 else len(corners)
    started = time.time()
    rows = []
    counterexample = None
    best_exact: Fraction | None = None
    best_witness_ratio: Fraction | None = None
    tightness_witness = None
    best_strict_ratio: Fraction | None = None
    strict_witness = None
    best_float = None
    for index in range(lo, min(hi, len(corners))):
        corner = corners[index]
        sub = copy.copy(args)
        sub.fibers = int(args.corner_fibers)
        sub.starts = int(args.corner_starts)
        sub.exact_leads = int(args.corner_exact_leads)
        sub.maxiter = int(args.corner_maxiter)
        result = run(sub, q_rows=corner_reference_rows(m, K, corner),
                     reference_label="corner:" + "".join(map(str, corner)))
        exact_text = result.get("best_exact_ratio")
        rows.append({
            "corner_index": index, "corner": list(corner),
            "status": result["status"],
            "fibers_searched": result.get("fibers_searched"),
            "best_float_ratio": result.get("best_float_ratio"),
            "best_exact_ratio": exact_text,
            "best_exact_ratio_float": result.get("best_exact_ratio_float"),
            "exact_rankone_verified_count": result.get("exact_rankone_verified_count"),
            "wall_clock_seconds": result.get("wall_clock_seconds"),
        })
        if result.get("best_float_ratio") is not None:
            best_float = result["best_float_ratio"] if best_float is None \
                else max(best_float, result["best_float_ratio"])
        if exact_text is not None:
            value = Fraction(exact_text)
            if best_exact is None or value > best_exact:
                best_exact = value
        sw = result.get("strict_top_c_witness")
        if sw is not None:
            value = Fraction(sw["exact_ratio"])
            if best_strict_ratio is None or value > best_strict_ratio:
                best_strict_ratio = value
                strict_witness = {"corner": list(corner), **sw}
        witness = result.get("tightness_witness")
        if witness is not None:
            value = Fraction(witness["exact_ratio"])
            if best_witness_ratio is None or value > best_witness_ratio:
                best_witness_ratio = value
                tightness_witness = {"corner": list(corner), **witness}
        if result.get("counterexample") is not None:
            counterexample = {"corner": list(corner), **result["counterexample"]}
            break
    return {
        "protocol_version": PROTOCOL_VERSION_CORNERS,
        "evidence_class": EVIDENCE_CLASS,
        "development_only": True,
        "stage": "B3_direct_rank_one_corner_reference_sweep",
        "m": m, "alphabet": K, "seed": int(args.seed),
        "corners_total": len(corners),
        "corner_range": [lo, min(hi, len(corners))],
        "corners_swept": len(rows),
        "corner_fibers": int(args.corner_fibers),
        "corner_starts": int(args.corner_starts),
        "corner_maxiter": int(args.corner_maxiter),
        "corner_exact_leads": int(args.corner_exact_leads),
        "best_float_ratio": best_float,
        "best_exact_ratio": None if best_exact is None else fraction_text(best_exact),
        "best_exact_ratio_float": None if best_exact is None else float(best_exact),
        "wall_clock_seconds": round(time.time() - started, 3),
        "counterexample": counterexample,
        "tightness_witness": tightness_witness,
        "best_strict_top_c_exact_ratio": (None if best_strict_ratio is None
                                          else fraction_text(best_strict_ratio)),
        "strict_top_c_witness": strict_witness,
        "status": "KILLED" if counterexample else "NO_EXACT_COUNTEREXAMPLE_FROM_NUMERICAL_LEADS",
        "corners": rows,
        "interpretation": (
            "Corner (deterministic product) references are admissible under Chain D's stated "
            "nonnegative-normalized-product assumption and are the vertices of that set. All "
            "corners are exactly isomorphic to one another under per-coordinate symbol "
            "relabeling, so per-corner differences here are search noise, not geometry, and a "
            "clean sweep is NOT independent evidence from K^m directions. Only the exact "
            "rational recheck can kill the law; nothing here is a proof."
        ),
    }


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--m", type=int, default=4)
    parser.add_argument("--alphabet", type=int, default=3)
    parser.add_argument("--fiber-kind", choices=("centred", "raw"), default="centred",
                        help=("Which rank-one variety to search. 'centred' is the "
                              "original V_lambda (D6's hypothesis, known FALSE). "
                              "'raw' is V^raw_phi, the RAW local contrast rank one "
                              "fibre, of dimension 2^m at codimension m(K-2) inside "
                              "V_lambda. Both are linear subspaces, so the search "
                              "path is identical and an A/B comparison at matched "
                              "budget and seed is meaningful."))
    parser.add_argument("--reference", choices=["uniform", "point0", "skew_cycle", "corners"],
                        default="uniform",
                        help="corners: exhaustively sweep every deterministic product reference "
                             "(the vertices of the admissible reference set); own protocol_version")
    parser.add_argument("--corner-range", default=None,
                        help="shard the corner sweep, e.g. 0:27")
    parser.add_argument("--corner-fibers", type=int, default=8)
    parser.add_argument("--corner-starts", type=int, default=1)
    parser.add_argument("--corner-maxiter", type=int, default=400)
    parser.add_argument("--corner-exact-leads", type=int, default=2)
    parser.add_argument("--fibers", type=int, default=24)
    parser.add_argument("--starts", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20260904)
    parser.add_argument("--denominator", type=int, default=40,
                        help="bounded denominator for lambda snapping and lead rationalization")
    parser.add_argument("--lambda-mode", choices=["halton", "random"], default="halton")
    parser.add_argument("--no-structured", action="store_true",
                        help="omit the deterministic structured lambda seeds")
    parser.add_argument("--optimizer",
                        choices=["nelder-mead", "powell", "both", "de", "lp", "de+lp",
                                 "both+lp", "de+both+lp"],
                        default="both",
                        help="derivative-free only; the objective is piecewise linear and "
                             "nonsmooth. Powell dominates Nelder-Mead once the fiber dimension "
                             "passes ~20, so the default runs Nelder-Mead then a Powell polish.")
    parser.add_argument("--maxiter", type=int, default=2000)
    parser.add_argument("--lp-rounds", type=int, default=20,
                        help="active-cell LP ascent rounds per start")
    parser.add_argument("--lp-box", type=float, default=20.0,
                        help="box bound on fiber coordinates inside the LP")
    parser.add_argument("--de-maxiter", type=int, default=200)
    parser.add_argument("--de-popsize", type=int, default=15)
    parser.add_argument("--exact-leads", type=int, default=8)
    parser.add_argument("--exact-basis", choices=["auto", "gauss", "closed_form"], default="auto")
    parser.add_argument("--gauss-limit", type=int, default=81,
                        help="use exact Fraction Gaussian elimination only when K^m <= this")
    parser.add_argument("--snap", choices=["project", "coefficients", "both"], default="both",
                        help="project: rationalize the lead then exactly orthogonally project "
                             "it onto V_lambda; coefficients: rationalize the fiber coordinates "
                             "so F = B c is exact by construction. Both land exactly in V_lambda.")
    parser.add_argument("--denominator-ladder", type=int, default=3,
                        help="number of denominator refinements (x4 each) tried per lead")
    parser.add_argument("--nullspace-tol", type=float, default=1e-9)
    parser.add_argument("--nullspace-method", choices=("auto", "svd", "closed_form"),
                        default="auto",
                        help=("How to build the float fiber basis. 'svd' is the original "
                              "path; 'closed_form' builds it from the exact closed-form "
                              "columns and QR, never calling LAPACK's SVD (use this if "
                              "numpy raises 'SVD did not converge', as macOS Accelerate "
                              "does); 'auto' tries the SVD and falls back."))
    parser.add_argument("--min-topc-margin", type=float, default=0.0,
                        help=("StrictTopC gate. Require (min selected score - max unselected "
                              "score) / delta_square >= this value; worlds below it are "
                              "UNDEFINED, never violations. 0 disables the gate. Use a small "
                              "positive value (e.g. 1e-3) to exclude Top-C ties."))
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--exact-dimension-check", action="store_true",
                        help="certify dim V_lambda exactly (integers only) for structured and "
                             "random lambda at this (m, K); writes its own protocol_version")
    parser.add_argument("--dimension-trials", type=int, default=8,
                        help="extra random lambda tuples for --exact-dimension-check")
    parser.add_argument("--out", default=None)
    args = parser.parse_args(argv)

    if args.exact_dimension_check:
        result = run_dimension_check(args)
        out = Path(args.out) if args.out else (
            ROOT / "research" / "d6_contrast_rank_falsification"
            / f"B3fiberdim_rankone_m{int(args.m)}_K{int(args.alphabet)}.json"
        )
        if out.exists():
            raise SystemExit(f"refusing to overwrite existing ledger artifact: {out}")
        write_artifact_with_provenance(
            out, result,
            protocol={"protocol_version": PROTOCOL_VERSION_DIMENSION, "m": int(args.m),
                      "alphabet": int(args.alphabet), "denominator": int(args.denominator),
                      "dimension_trials": int(args.dimension_trials),
                      "gauss_limit": int(args.gauss_limit), "primes": list(DIMENSION_PRIMES)},
            seed=int(args.seed), evidence_class=EVIDENCE_CLASS_DIMENSION, chain="D6",
        )
        print(json.dumps({
            "status": result["status"], "m": result["m"], "alphabet": result["alphabet"],
            "closed_form_dim": result["certificates"][0]["closed_form_dim"],
            "lambda_tuples_proved": result["lambda_tuples_proved"],
            "lambda_tuples_checked": result["lambda_tuples_checked"],
            "wall_clock_seconds": result["wall_clock_seconds"], "out": str(out),
        }, indent=2))
        return 0 if result["status"] == "EXACT_DIMENSION_IDENTITY_HOLDS" else 3

    if args.self_test:
        report = self_test(int(args.m), int(args.alphabet), args.reference, int(args.seed),
                           int(args.denominator), float(args.nullspace_tol))
        print(json.dumps(report, indent=2, sort_keys=True))
        return 0 if report["all_ok"] else 1

    corners_mode = args.reference == "corners"
    suffix = args.reference
    if corners_mode and args.corner_range:
        suffix = "corners_" + str(args.corner_range).replace(":", "_")
    out = Path(args.out) if args.out else (
        ROOT / "research" / "d6_contrast_rank_falsification"
        / f"B3fiber{'corner' if corners_mode else ''}_rankone_m{int(args.m)}_{suffix}.json"
    )
    if out.exists():
        # The research tree is an append-only ledger: never overwrite a result.
        raise SystemExit(f"refusing to overwrite existing ledger artifact: {out}")

    result = run_corner_sweep(args) if corners_mode else run(args)
    write_artifact_with_provenance(
        out, result,
        protocol={
            "protocol_version": result.get("protocol_version", PROTOCOL_VERSION),
            "stage": result.get("stage", "B3_direct_rank_one_linear_fiber"),
            "corner_range": args.corner_range,
            "corner_fibers": int(args.corner_fibers), "corner_starts": int(args.corner_starts),
            "corner_maxiter": int(args.corner_maxiter),
            "corner_exact_leads": int(args.corner_exact_leads),
            "m": int(args.m), "alphabet": int(args.alphabet), "reference": args.reference,
            "fibers": int(args.fibers), "starts": int(args.starts),
            "lambda_mode": args.lambda_mode, "structured_seeds": not bool(args.no_structured),
            "optimizer": args.optimizer, "maxiter": int(args.maxiter),
            "denominator": int(args.denominator), "exact_leads": int(args.exact_leads),
            "exact_basis": args.exact_basis, "gauss_limit": int(args.gauss_limit),
            "snap": args.snap, "denominator_ladder": int(args.denominator_ladder), "nullspace_tol": float(args.nullspace_tol),
        },
        seed=int(args.seed), evidence_class=EVIDENCE_CLASS, chain="D6",
    )
    print(json.dumps({
        "status": result["status"],
        "corners_swept": result.get("corners_swept"),
        "fibers_searched": result.get("fibers_searched"),
        "fibers_skipped_degenerate": result.get("fibers_skipped_degenerate"),
        "fibers_skipped_duplicate": result.get("fibers_skipped_duplicate"),
        "best_float_ratio": result.get("best_float_ratio"),
        "best_exact_ratio": result.get("best_exact_ratio"),
        "exact_rankone_verified_count": result.get("exact_rankone_verified_count"),
        "wall_clock_seconds": result.get("wall_clock_seconds"),
        "out": str(out),
    }, indent=2))
    if result["status"] == "KILLED":
        return 2
    if str(result["status"]).startswith(("INCONCLUSIVE", "BLOCKED", "INTERNAL")):
        return 3
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
