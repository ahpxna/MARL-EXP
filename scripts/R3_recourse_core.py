#!/usr/bin/env python3
"""R3 core: exact fixed-tolerance recourse R_eps, fast transition step.

Instance: an integer support matrix `matrix[i][a]`, i < m components, a < h
scenarios.  For S subset of components ("selected", i.e. removed from the
residual) the normalized residual oscillation is

    val(S) = osc( sum_{i notin S} matrix[i][.] ) / D,    D = sum_i span(row i).

S is eps-good at budget k=|S| when val(S) <= min_{|T|=k} val(T) + eps.
R_eps = min over chains (S_k)_{k<=m}, |S_k| = k, every S_k eps-good, of
        max_k |S_k \\ S_{k+1}|   (deletions forced at one budget step).

ALL comparisons are integer/Fraction exact: val(S) is stored as the INTEGER
oscillation `vals[S]`, and `val(S) <= opt/D + eps` is tested as
    vals[S] * eps.denominator <= opt * eps.denominator + eps.numerator * D,
so no float ever decides an answer.

The published probe (research/worker_distinct_completion_20260913/
fixed_epsilon_recourse.py) does the same DP with a Python double loop over
layer pairs.  `solve` here is the same recurrence with the transition step
vectorized; `solve_reference` is a literal transcription of the published
loop, and `scripts/R3_recourse_push.py` asserts the two agree cell by cell.
"""
from fractions import Fraction as F

import numpy as np


def instance_data(matrix):
    """Exact integer oscillation of every subset's residual, plus D."""
    m = len(matrix)
    h = len(matrix[0])
    spans = [max(r) - min(r) for r in matrix]
    D = sum(spans)
    if D <= 0:
        raise ValueError("degenerate instance: total component span is zero")
    v = np.array(matrix, dtype=np.int64)
    N = 1 << m
    sums = np.zeros((N, h), dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    for b in range(m):
        bit = 1 << b
        sel = (idx & bit) != 0
        sums[sel] = sums[idx[sel] ^ bit] + v[b]
    res = v.sum(axis=0)[None, :] - sums
    vals = (res.max(axis=1) - res.min(axis=1)).astype(np.int64)
    return vals, D, spans


def good_layers(vals, D, eps, m):
    """eps-good layer masks, exact integer test."""
    eps = F(eps)
    en, ed = eps.numerator, eps.denominator
    pc = np.bitwise_count(np.arange(1 << m, dtype=np.uint32)).astype(np.int64)
    layers = []
    for k in range(m + 1):
        layer = np.flatnonzero(pc == k).astype(np.uint32)
        opt = int(vals[layer].min())
        keep = vals[layer] * ed <= opt * ed + en * D
        layers.append(layer[keep])
    return layers


def _transition(prev, Dv, cur):
    """value(T) = min_S max(Dv[S], |S \\ T|) over S in prev; returns values, argmin."""
    best = np.empty(len(cur), dtype=np.int64)
    barg = np.empty(len(cur), dtype=np.int64)
    step = max(1, (1 << 22) // max(1, len(prev)))
    Dv8 = Dv.astype(np.uint8)[None, :]
    for s in range(0, len(cur), step):
        T = cur[s:s + step]
        cand = np.maximum(np.bitwise_count(prev[None, :] & ~T[:, None]), Dv8)
        a = cand.argmin(axis=1)
        barg[s:s + step] = a
        best[s:s + step] = cand[np.arange(len(T)), a]
    return best, barg


def solve(matrix, eps, _data=None):
    """Exact R_eps plus a witnessing chain.  Raises AssertionError on any
    internal inconsistency (chain not eps-good, or cost != reported value)."""
    m = len(matrix)
    vals, D, spans = instance_data(matrix) if _data is None else _data
    layers = good_layers(vals, D, eps, m)
    for k, L in enumerate(layers):
        assert len(L) > 0, f"empty eps-good layer at k={k}"
    prev = layers[0]
    Dv = np.zeros(len(prev), dtype=np.int64)
    chain_back = []
    for k in range(1, m + 1):
        cur = layers[k]
        best, barg = _transition(prev, Dv, cur)
        chain_back.append((prev, barg))
        prev, Dv = cur, best
    assert len(prev) == 1 and int(prev[0]) == (1 << m) - 1
    value = int(Dv[0])
    path = [int(prev[0])]
    j = 0
    for pl, barg in reversed(chain_back):
        j = int(barg[j])
        path.append(int(pl[j]))
    path.reverse()
    # re-verify the witness independently of the DP bookkeeping
    good = [set(int(x) for x in L) for L in layers]
    for k, S in enumerate(path):
        assert S.bit_count() == k and S in good[k], f"chain member not eps-good at k={k}"
    assert max((S & ~T).bit_count() for S, T in zip(path, path[1:])) == value
    return value, path, [len(L) for L in layers]


def solve_reference(matrix, eps):
    """Literal transcription of the published O(layer^2) DP (validation only)."""
    m = len(matrix)
    h = len(matrix[0])
    denom = sum(max(row) - min(row) for row in matrix)
    if not denom:
        raise ValueError("zero normalization")
    eps = F(eps)
    vals = []
    layers = [[] for _ in range(m + 1)]
    for S in range(1 << m):
        residual = [sum(matrix[i][a] for i in range(m) if not S >> i & 1) for a in range(h)]
        vals.append(F(max(residual) - min(residual), denom))
    for k in range(m + 1):
        layer = [S for S in range(1 << m) if S.bit_count() == k]
        opt = min(vals[S] for S in layer)
        layers[k] = [S for S in layer if vals[S] <= opt + eps]
    Dm = {0: 0}
    for layer in layers[1:]:
        new = {}
        for T in layer:
            new[T] = min(max(v, (S & ~T).bit_count()) for S, v in Dm.items())
        Dm = new
    return Dm[(1 << m) - 1]


def topspan_chain(matrix):
    """The nested chain S_k = the k components of largest span (index ties broken
    by component index).  Returns [S_0,...,S_m] as bitmasks."""
    m = len(matrix)
    spans = [max(r) - min(r) for r in matrix]
    order = sorted(range(m), key=lambda i: (-spans[i], i))
    out, S = [0], 0
    for i in order:
        S |= 1 << i
        out.append(S)
    return out
