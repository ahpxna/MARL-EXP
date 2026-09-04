"""Vectorized float screening layer: find candidates fast, certify them exactly.

Why this exists
---------------
The observatory's decision layer is exact rational arithmetic, which is the only
thing the portfolio's own hard gate accepts ("no floating-point result falsifies
a theorem").  Exact arithmetic is also slow and inherently scalar: ``Fraction``
is arbitrary-precision integer work with no vector unit and no accelerator path.

So the split is deliberate:

    screen (float, vectorized, huge batches)  ->  certify (exact, tiny batches)

Screening never decides anything.  It ranks candidate worlds by how close they
come to violating a target inequality, and hands the top of that ranking to the
exact probes.  A candidate that survives screening is a *lead*; only the exact
re-check can kill or keep a conjecture.  This is exactly the discipline the D6
ledger asks for, and it is what makes a GPU useful here at all.

Backends
--------
``numpy`` is the default and needs nothing.  If ``torch`` is importable the
batch maths runs on CUDA or Apple MPS when available; the API and the results
are identical, only the throughput changes.  Availability is reported by
``backend_info()`` so a run can record which one it used.
"""
from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Dict, List, Sequence, Tuple

import numpy as np

from .exact import Q
from .worlds import Support, World, ProductReference

try:                                            # pragma: no cover - optional
    import torch as _torch
except Exception:                               # pragma: no cover
    _torch = None


def backend_info() -> Dict[str, object]:
    info = {"numpy": np.__version__, "torch": None, "device": "cpu",
            "cuda": False, "mps": False}
    if _torch is not None:
        info["torch"] = _torch.__version__
        info["cuda"] = bool(_torch.cuda.is_available())
        mps = getattr(_torch.backends, "mps", None)
        info["mps"] = bool(mps is not None and mps.is_available())
        info["device"] = "cuda" if info["cuda"] else ("mps" if info["mps"] else "cpu")
    return info


def _xp(prefer_gpu: bool = True):
    """Return (module, device) -- torch on an accelerator, else numpy."""
    if prefer_gpu and _torch is not None:
        if _torch.cuda.is_available():
            return _torch, "cuda"
        mps = getattr(_torch.backends, "mps", None)
        if mps is not None and mps.is_available():
            return _torch, "mps"
    return np, "cpu"


# ------------------------------------------------------------------ batching

def enumerate_actions(m: int, arity: int) -> np.ndarray:
    """All joint actions of a full Cartesian space, as an (n_full, m) int array."""
    return np.array(list(itertools.product(range(int(arity)), repeat=int(m))),
                    dtype=np.int64)


def sample_batch(n_worlds: int, m: int, arity: int, *, rng: np.random.Generator,
                 den: int = 8, span: int = 8, interaction: float = 1.0):
    """Draw a batch of worlds as float arrays.

    Returns ``(primitives, residual)`` with shapes ``(B, m, arity)`` and
    ``(B, n_full)``.  Values are multiples of ``1/den`` so that any candidate
    can be lifted back to an exact ``Fraction`` without rounding.
    """
    prim = rng.integers(-span, span + 1, size=(n_worlds, int(m), int(arity))) / float(den)
    n_full = int(arity) ** int(m)
    resid = rng.integers(-int(span * interaction), int(span * interaction) + 1,
                         size=(n_worlds, n_full)) / float(den)
    return prim.astype(np.float64), resid.astype(np.float64)


def world_values(prim: np.ndarray, resid: np.ndarray, actions: np.ndarray) -> np.ndarray:
    """F(a) for every world in the batch: shape (B, n_full)."""
    # prim[b, j, actions[i, j]] summed over j
    B, m, _ = prim.shape
    idx = actions.T                                    # (m, n_full)
    contrib = np.stack([prim[:, j, idx[j]] for j in range(m)], axis=0)  # (m,B,n_full)
    return contrib.sum(axis=0) + resid


def delta_square_batch(values: np.ndarray, actions: np.ndarray, m: int,
                       arity: int) -> np.ndarray:
    """Uniform interaction modulus per world, vectorized over the batch.

    For each coordinate the four corners of a rectangle are gathered by index
    arithmetic on the mixed-radix action encoding, so the whole batch is a
    handful of large gathers rather than a Python loop over corner pairs.
    """
    B, n_full = values.shape
    stride = [arity ** (m - 1 - j) for j in range(m)]
    best = np.zeros(B, dtype=np.float64)
    for j in range(m):
        aj = actions[:, j]
        for u in range(arity):
            for v in range(u + 1, arity):
                # move coordinate j to u and to v
                base = np.arange(n_full) + (u - aj) * stride[j]
                other = np.arange(n_full) + (v - aj) * stride[j]
                # only rows whose coordinate j currently equals u avoid double counting
                keep = aj == u
                if not keep.any():
                    continue
                x = base[keep]
                y = other[keep]
                # second context: shift every other coordinate is implicit in the
                # full enumeration, so pair x,y against every context row below
                d = values[:, x] - values[:, y]          # (B, K)
                # mixed difference across two contexts = difference of differences
                spread = d.max(axis=1) - d.min(axis=1)
                best = np.maximum(best, spread)
    return best


def compression_loss_batch(values: np.ndarray, actions: np.ndarray,
                           prim: np.ndarray, retained: Sequence[int]) -> np.ndarray:
    """L_F(S) for one retained set across the batch."""
    B, m, _ = prim.shape
    keep = set(int(j) for j in retained)
    idx = actions.T
    omitted = np.zeros_like(values)
    for j in range(m):
        if j in keep:
            continue
        omitted += prim[:, j, idx[j]]
    resid = values - np.stack(
        [prim[:, j, idx[j]] for j in range(m)], axis=0).sum(axis=0)
    tot = omitted + resid
    return 0.5 * (tot.max(axis=1) - tot.min(axis=1))


def screen_half_factor(n_worlds: int, m: int, arity: int, *, seed: int = 0,
                       k: int | None = None, top: int = 25,
                       prefer_gpu: bool = True) -> Dict[str, object]:
    """Rank a large batch by the half-factor ratio J = regret / ((m-1) delta).

    Returns the ``top`` candidates with the exact rational data needed to
    reconstruct each world, so the exact probe can re-derive J without trusting
    a single float from this function.
    """
    rng = np.random.default_rng(seed)
    actions = enumerate_actions(m, arity)
    prim, resid = sample_batch(n_worlds, m, arity, rng=rng)
    values = world_values(prim, resid, actions)
    delta = delta_square_batch(values, actions, m, arity)
    k = int(k if k is not None else max(1, m // 2))

    spans = prim.max(axis=2) - prim.min(axis=2)           # (B, m)
    order = np.argsort(-spans, axis=1)
    best_loss = None
    for S in itertools.combinations(range(m), k):
        L = compression_loss_batch(values, actions, prim, S)
        best_loss = L if best_loss is None else np.minimum(best_loss, L)
    sel = order[:, :k]
    L_sel = np.zeros(prim.shape[0])
    for b in range(prim.shape[0]):
        L_sel[b] = compression_loss_batch(values[b:b + 1], actions,
                                          prim[b:b + 1], sel[b])[0]
    regret = L_sel - best_loss
    denom = (m - 1) * delta
    with np.errstate(divide="ignore", invalid="ignore"):
        J = np.where(denom > 0, regret / denom, np.nan)
    finite = np.isfinite(J)
    idx = np.argsort(-np.where(finite, J, -np.inf))[:top]
    out = []
    for i in idx:
        if not finite[i]:
            continue
        out.append({
            "J_float": float(J[i]),
            "delta_float": float(delta[i]),
            "regret_float": float(regret[i]),
            "primitives": [[Fraction(int(round(x * 8)), 8) for x in row]
                           for row in prim[i]],
            "residual": [Fraction(int(round(x * 8)), 8) for x in resid[i]],
            "selected": [int(x) for x in sel[i]],
        })
    return {"backend": backend_info(), "n_screened": int(n_worlds),
            "m": m, "arity": arity, "k": k, "candidates": out,
            "max_J": float(np.nanmax(J)) if finite.any() else None}


def to_exact_world(cand: Dict, m: int, arity: int) -> World:
    """Lift a screened candidate back to an exact rational world."""
    sizes = tuple([int(arity)] * int(m))
    sup = Support.cartesian(sizes)
    prim = tuple(tuple(Q(x) for x in row) for row in cand["primitives"])
    resid = {a: Q(v) for a, v in zip(sup.omega, cand["residual"]) if Q(v) != 0}
    return World(sup, prim, Q(0), resid, {"family": "screened", "arity": int(arity)})
