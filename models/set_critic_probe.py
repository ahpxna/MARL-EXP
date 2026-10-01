"""Measurement of message interaction and score margins on a frozen set-valued critic (P3).

Object.  For one agent i with neighbours j_1..j_n, a frozen evaluator gives
F(x), x in U^n.  x_j = actual means neighbour j's fresh message is used, and
x_j = reference means its reference (cached value with age, or a local
prediction) is used.  With U = {0: reference, 1: actual}, F(x) = F(1_S) is the
set function "value of the decision taken with heard set S", evaluated at the
true state.  See PROTOCOL_v0.md.

Two objectives are kept apart:

* D6 compression loss (the object of the Lean theorems), transcribed from
  LeanProductMixedDifferenceV4 / LeanProductSurrogateV4 / LeanSupportGeometryV4:
    jointWeight q c        = prod_i q_i(c_i)
    productResponse q F i u = sum_c jointWeight q c * F(c[i := u])
    score_i                = osc(productResponse q F i) = max_u - min_u
    mixedDifference F i x c = F x - F(x[i := c_i]) - F(c[i := x_i]) + F c
    delta (theorem's)      = max_{i,x,c} |mixedDifference F i x c|   (i versus REST)
    productCompressionLoss F Q T = osc_x(F x - sum_{j in T} Q_j(x_j)) / 2
  `margin_two_sufficient` (LeanD6SharpMarginThresholdV1): if T is Top-k by score
  and every i in T, j not in T has score_i >= score_j + rho, with rho >= 2 delta,
  then loss(T) <= loss(S) for every |S| = k.  check_margin_two() asserts
  exactly this and can fail.

* Subset decision objective: maximise F(1_T) over |T| = k.  Signed first-order
  gains g_j = F(e_j) - F(0).  Since |F(A+i) - F(A) - g_i| <= delta (an instance
  of the mixed difference with x = 1_{A+i}, c = 0), an exchange chain gives for
  the gain-ranking prefix P_k:
      max_{|T|=k} F(T) - max_{|T|=k, |P_k \\ T| <= R} F(T) <= 2 delta (d_k - R)_+,
  where d_k = min over optimal T* of |P_k \\ T*|.  So the price is 0 when every
  cut margin is >= 2 delta.  This is an ELEMENTARY bound derived for P3 and NOT
  formalised in Lean.  check_exchange_bound() asserts it and can fail.

Pairwise interaction (diagnostic only, NOT the theorem's delta):
    delta_pair = max_{j != l, A} |F(A+j+l) - F(A+j) - F(A+l) + F(A)|  <=  delta.
"""
from __future__ import annotations

import itertools
from typing import Callable, Dict, List, Optional, Sequence, Tuple

import numpy as np


def lattice_table(value_of_set: Callable[[Tuple[int, ...]], float], n: int) -> np.ndarray:
    """F on {0,1}^n from a set function of heard coordinate indices."""
    F = np.zeros((2,) * int(n), dtype=np.float64)
    for x in itertools.product((0, 1), repeat=int(n)):
        F[x] = float(value_of_set(tuple(j for j in range(n) if x[j] == 1)))
    return F


def point_reference(n: int, L: int = 2, level: int = 0) -> np.ndarray:
    q = np.zeros((int(n), int(L)), dtype=np.float64)
    q[:, int(level)] = 1.0
    return q


def product_responses(F: np.ndarray, q: np.ndarray) -> np.ndarray:
    """resp[i, u] = E_{c ~ q}[F(c[i := u])]."""
    n, L = F.ndim, F.shape[0]
    if q.shape != (n, L) or (q < 0).any() or not np.allclose(q.sum(axis=1), 1.0):
        raise ValueError("q must be a product of probability vectors of shape (n, L)")
    resp = np.zeros((n, L), dtype=np.float64)
    for i in range(n):
        for u in range(L):
            G = np.take(F, u, axis=i)
            for j in reversed([j for j in range(n) if j != i]):
                axis = j if j < i else j - 1
                G = np.tensordot(G, q[j], axes=([axis], [0]))
            resp[i, u] = float(G)
    return resp


def _coords(n: int, L: int) -> np.ndarray:
    return np.asarray(list(itertools.product(range(L), repeat=n)), dtype=np.int64)


def d6_delta(F: np.ndarray) -> float:
    """max_{i,x,c} |F x - F(x[i:=c_i]) - F(c[i:=x_i]) + F c| over the whole grid."""
    n, L = F.ndim, F.shape[0]
    C = _coords(n, L)
    flat = F.reshape(-1)
    strides = np.asarray([L ** (n - 1 - i) for i in range(n)], dtype=np.int64)
    idx = C @ strides
    best = 0.0
    for i in range(n):
        xi = C[:, i][:, None]
        ci = C[:, i][None, :]
        x_upd = idx[:, None] + (ci - xi) * strides[i]
        c_upd = idx[None, :] + (xi - ci) * strides[i]
        md = flat[idx][:, None] - flat[x_upd] - flat[c_upd] + flat[idx][None, :]
        best = max(best, float(np.abs(md).max()))
    return best


def compression_loss(F: np.ndarray, resp: np.ndarray, T: Sequence[int]) -> float:
    n, L = F.ndim, F.shape[0]
    C = _coords(n, L)
    resid = F.reshape(-1).copy()
    for j in T:
        resid -= resp[int(j)][C[:, int(j)]]
    return float(resid.max() - resid.min()) / 2.0


def top_k(scores: Sequence[float], k: int) -> Tuple[int, ...]:
    order = sorted(range(len(scores)), key=lambda j: (-float(scores[j]), j))
    return tuple(sorted(order[:int(k)]))


def ranking_by(scores: Sequence[float]) -> Tuple[int, ...]:
    return tuple(sorted(range(len(scores)), key=lambda j: (-float(scores[j]), j)))


def cut_margin(scores: Sequence[float], T: Sequence[int]) -> float:
    inside = [float(scores[i]) for i in T]
    outside = [float(scores[j]) for j in range(len(scores)) if j not in set(T)]
    if not inside or not outside:
        return float("inf")
    return min(inside) - max(outside)


def check_margin_two(F: np.ndarray, q: np.ndarray, tol: float = 1e-9) -> dict:
    """Transcription of margin_two_sufficient; returns per-k records and violations."""
    n = F.ndim
    resp = product_responses(F, q)
    scores = resp.max(axis=1) - resp.min(axis=1)
    delta = d6_delta(F)
    rows, violations = [], []
    for k in range(1, n):
        T = top_k(scores, k)
        rho = cut_margin(scores, T)
        lossT = compression_loss(F, resp, T)
        best = min(compression_loss(F, resp, S) for S in itertools.combinations(range(n), k))
        hyp = rho >= 2.0 * delta - 1e-12
        rows.append({"k": k, "top": T, "margin": rho, "hypothesis": hyp, "loss_top": lossT, "loss_min": best})
        if hyp and lossT > best + tol:
            violations.append(rows[-1])
    return {"delta": delta, "scores": scores.tolist(), "rows": rows, "violations": violations}


def subset_values(F: np.ndarray) -> Dict[Tuple[int, ...], float]:
    n = F.ndim
    out = {}
    for r in range(n + 1):
        for S in itertools.combinations(range(n), r):
            x = tuple(1 if j in S else 0 for j in range(n))
            out[S] = float(F[x])
    return out


def delta_pair(F: np.ndarray) -> float:
    n = F.ndim
    v = subset_values(F)
    best = 0.0
    for j, l in itertools.combinations(range(n), 2):
        rest = [x for x in range(n) if x not in (j, l)]
        for r in range(len(rest) + 1):
            for A in itertools.combinations(rest, r):
                A = set(A)
                md = (v[tuple(sorted(A | {j, l}))] - v[tuple(sorted(A | {j}))]
                      - v[tuple(sorted(A | {l}))] + v[tuple(sorted(A))])
                best = max(best, abs(md))
    return best


def revision_price(F: np.ndarray, ranking: Sequence[int], k: int, R: Optional[int]) -> dict:
    """Subset objective: gap between the best k-set and the best set within R of prefix_k."""
    n = F.ndim
    v = subset_values(F)
    k = min(int(k), n)
    prefix = set(ranking[:k])
    ks = list(itertools.combinations(range(n), k))
    best = max(v[S] for S in ks)
    optimal = [S for S in ks if v[S] >= best - 1e-12]
    reach = [S for S in ks if R is None or len(prefix - set(S)) <= int(R)]
    best_reach = max(v[S] for S in reach)
    d = min(len(prefix - set(S)) for S in optimal)
    return {"k": k, "best": best, "best_reachable": best_reach, "price": best - best_reach,
            "d_k": d, "oracle_set": max(ks, key=lambda S: (v[S], tuple(-x for x in S)))}


def check_exchange_bound(F: np.ndarray, Rs: Sequence[Optional[int]] = (0, 1, 2), tol: float = 1e-9) -> dict:
    """Assert price_R(gain ranking) <= 2 delta (d_k - R)_+ at every k (elementary bound, not Lean)."""
    n = F.ndim
    v = subset_values(F)
    gains = [v[(j,)] - v[()] for j in range(n)]
    rank = ranking_by(gains)
    delta = d6_delta(F)
    rows, violations = [], []
    for k in range(1, n):
        P = tuple(sorted(rank[:k]))
        margin = cut_margin(gains, P)
        for R in Rs:
            rp = revision_price(F, rank, k, R)
            bound = 2.0 * delta * max(0, rp["d_k"] - (n if R is None else int(R)))
            row = {"k": k, "R": R, "price": rp["price"], "bound": bound, "d_k": rp["d_k"], "margin": margin}
            rows.append(row)
            if rp["price"] > bound + tol:
                violations.append(row)
            if margin >= 2.0 * delta - 1e-12 and rp["price"] > tol and R == 0:
                violations.append(dict(row, reason="zero-price regime violated"))
    return {"delta": delta, "delta_pair": delta_pair(F), "gains": gains, "ranking": rank, "rows": rows,
            "violations": violations}
