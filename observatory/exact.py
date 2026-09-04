"""Exact rational primitives shared by every chain probe.

The portfolio's own hard gate says no floating-point result may falsify a
theorem.  So every decision-bearing quantity here is a ``Fraction``: spans,
oscillations, compression radii, deficits, decision gaps, interaction moduli.
Floats appear only where a quantity is genuinely statistical (an estimate, a
sample mean) and such rows are tagged ``mode="float"`` by the caller.

Nothing in this module rounds, and nothing uses a tolerance.  Ties are exact
ties, and that matters: several of the portfolio's counterexamples are tied
Top-k instances, and a 1e-12 tolerance would have silently discarded them.
"""
from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Iterable, Sequence, Tuple

Q = Fraction

ZERO = Q(0)
ONE = Q(1)
HALF = Q(1, 2)


def q(value) -> Q:
    """Coerce to an exact rational without ever going through binary float."""
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Q(value)
    if isinstance(value, str):
        return Q(value)
    if isinstance(value, float):
        # Fraction(float) is exact w.r.t. the binary value, which is the honest
        # reading of a float that already exists.  Callers that want a decimal
        # should pass a string.
        return Q(value).limit_denominator(10 ** 12)
    raise TypeError("cannot coerce %r to an exact rational" % (type(value).__name__,))


def qvec(values: Iterable) -> Tuple[Q, ...]:
    return tuple(q(v) for v in values)


# ------------------------------------------------------------ oscillation

def osc(values: Sequence[Q]) -> Q:
    """max - min, the portfolio's universal spread primitive."""
    if not values:
        raise ValueError("oscillation of an empty family is undefined")
    return max(values) - min(values)


def half_osc(values: Sequence[Q]) -> Q:
    """The exact minimax constant-approximation radius: inf_c max|v - c|."""
    return osc(values) * HALF


def gauge_error(estimate: Sequence[Q], truth: Sequence[Q]) -> Q:
    """delta^circ = inf_c ||est - truth - c||_inf = (1/2) osc(est - truth).

    This is the gauge-invariant error the Functional chain uses; it is the
    correct primitive whenever the downstream functional is invariant to an
    additive constant (spans, zero-sum contrasts).
    """
    if len(estimate) != len(truth):
        raise ValueError("estimate/truth length mismatch")
    return half_osc([a - b for a, b in zip(estimate, truth)])


def sup_error(estimate: Sequence[Q], truth: Sequence[Q]) -> Q:
    """The offset-sensitive sup norm, kept for explicit comparison."""
    if len(estimate) != len(truth):
        raise ValueError("estimate/truth length mismatch")
    return max(abs(a - b) for a, b in zip(estimate, truth))


# ------------------------------------------------------------------ order

def argsort_desc(values: Sequence[Q]) -> Tuple[int, ...]:
    """Deterministic descending order; ties broken by index (documented, exact)."""
    return tuple(sorted(range(len(values)), key=lambda i: (-values[i], i)))


def topk(values: Sequence[Q], k: int) -> Tuple[int, ...]:
    if not 0 < int(k) <= len(values):
        raise ValueError("k must lie in [1, n]")
    return tuple(sorted(argsort_desc(values)[: int(k)]))


def topk_is_tied(values: Sequence[Q], k: int) -> bool:
    """True when the k-th and (k+1)-th values coincide -> Top-k is non-strict.

    Several portfolio counterexamples live exactly here, so this is reported as
    its own quantity rather than hidden inside a selection routine.
    """
    k = int(k)
    if k >= len(values):
        return False
    order = argsort_desc(values)
    return values[order[k - 1]] == values[order[k]]


def topk_boundary_gap(values: Sequence[Q], k: int) -> Q:
    k = int(k)
    if k >= len(values):
        return ZERO
    order = argsort_desc(values)
    return values[order[k - 1]] - values[order[k]]


def extrema_gaps(values: Sequence[Q]):
    """Return (argmax, argmin, g_plus, g_minus, g, unique_max, unique_min).

    ``g_plus`` is the gap from the maximum to the runner-up; zero when the
    maximum is attained more than once.  ``g`` is the binding extremal gap that
    the lambda_C < 1/2 theorem divides by.
    """
    n = len(values)
    if n < 2:
        raise ValueError("extrema gaps need at least two actions")
    mx = max(values)
    mn = min(values)
    n_max = sum(1 for v in values if v == mx)
    n_min = sum(1 for v in values if v == mn)
    a_plus = min(i for i in range(n) if values[i] == mx)
    a_minus = min(i for i in range(n) if values[i] == mn)
    if n_max == 1:
        g_plus = mx - max(v for i, v in enumerate(values) if i != a_plus)
    else:
        g_plus = ZERO
    if n_min == 1:
        g_minus = min(v for i, v in enumerate(values) if i != a_minus) - mn
    else:
        g_minus = ZERO
    return {
        "argmax": a_plus,
        "argmin": a_minus,
        "n_argmax": n_max,
        "n_argmin": n_min,
        "g_plus": g_plus,
        "g_minus": g_minus,
        "g": min(g_plus, g_minus),
        "unique_max": n_max == 1,
        "unique_min": n_min == 1,
    }


# ------------------------------------------------------------- set utils

def subsets(n: int, k: int):
    return itertools.combinations(range(int(n)), int(k))


def complement(n: int, s: Iterable[int]) -> Tuple[int, ...]:
    s = set(int(x) for x in s)
    return tuple(j for j in range(int(n)) if j not in s)


def is_chain(sets: Sequence[frozenset]) -> bool:
    """True when the family is totally ordered by inclusion."""
    ordered = sorted(sets, key=len)
    for a, b in zip(ordered, ordered[1:]):
        if not a <= b:
            return False
    return True


def incomparable_pairs(sets: Sequence[frozenset]) -> int:
    n = 0
    for a, b in itertools.combinations(sets, 2):
        if not (a <= b or b <= a):
            n += 1
    return n


# --------------------------------------------------------- safe division

def ratio(numer: Q, denom: Q):
    """Exact ratio, or ``None`` when the denominator vanishes.

    Returning ``None`` rather than an infinity keeps 'undefined' distinguishable
    from 'enormous' in the store, which matters for lambda_C on tied extrema.
    """
    if denom == 0:
        return None
    return numer / denom
