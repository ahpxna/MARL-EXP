"""Executable finite revision search for a FROZEN actor and a supplied set evaluator.

No simulator or oracle is imported. The caller must supply an evaluator using only
permitted deployment inputs. Exhaustive search removes the candidate-coverage and
search gaps; it does NOT establish evaluator accuracy or actor realization.
Latency covers enumeration and evaluation, not upstream ranking preparation,
packet transmission, or traffic time. There is no hard real-time deadline guarantee.
"""
from dataclasses import dataclass
from itertools import combinations
from math import comb, isfinite
from time import perf_counter
from typing import Callable, FrozenSet, Mapping, Sequence

Subset = FrozenSet[int]


def _validate(ranking, k, radius):
    ranking = tuple(ranking)
    if any(type(i) is not int for i in ranking) or len(set(ranking)) != len(ranking):
        raise ValueError('ranking must contain distinct integer message IDs')
    if type(k) is not int or not 0 <= k <= len(ranking):
        raise ValueError('budget must be between zero and number of messages')
    if type(radius) is not int or radius < 0:
        raise ValueError('revision radius must be a nonnegative integer')
    return ranking


def candidate_count(m: int, k: int, radius: int) -> int:
    if any(type(x) is not int for x in (m, k, radius)) or not 0 <= k <= m or radius < 0:
        raise ValueError('invalid size, budget, or radius')
    return sum(comb(k, r) * comb(m-k, r) for r in range(min(radius, k, m-k)+1))


def reachable_sets(ranking: Sequence[int], k: int, radius: int):
    """Each legal k-set exactly once; prefix first, then increasing edit count.

    IDs need not be contiguous. An edit removes one prefix item and adds one
    outside item. This is replacement count, not symmetric-difference size.
    """
    ranking = _validate(ranking, k, radius)
    inside, outside = ranking[:k], ranking[k:]
    prefix = frozenset(inside)
    for r in range(min(radius, k, len(outside))+1):
        for removed in combinations(inside, r):
            for added in combinations(outside, r):
                yield (prefix - frozenset(removed)) | frozenset(added)


@dataclass(frozen=True)
class RevisionResult:
    selected: Subset
    prefix: Subset
    predicted_value: float
    candidates_evaluated: int
    replacements: int
    enumeration_seconds: float
    evaluation_seconds: float
    selection_seconds: float
    # Errors relative to the supplied deterministic evaluator, not true returns.
    search_gap: float = 0.0
    coverage_gap: float = 0.0


def select_revision(ranking: Sequence[int], k: int, radius: int,
                    evaluate: Callable[[Subset], float], *,
                    max_candidates: int | None = None) -> RevisionResult:
    """Exact finite argmax; ties prefer fewer replacements, then ranking order.

    With max_candidates, fail BEFORE evaluation if complete search is too large.
    Never silently substitute a beam/greedy search and still report zero gaps.
    evaluate must be deterministic during this call (freeze model, disable dropout).
    """
    start = perf_counter()
    ranking = _validate(ranking, k, radius)
    count = candidate_count(len(ranking), k, radius)
    if max_candidates is not None:
        if type(max_candidates) is not int or max_candidates < 1:
            raise ValueError('max_candidates must be a positive integer')
        if count > max_candidates:
            raise ValueError(f'complete search needs {count} candidates, cap is {max_candidates}')
    candidates = tuple(reachable_sets(ranking, k, radius))
    enumerated = perf_counter()
    best, value = candidates[0], float('-inf')
    for subset in candidates:
        score = float(evaluate(subset))
        if not isfinite(score):
            raise ValueError('evaluator returned a nonfinite value')
        if score > value:
            best, value = subset, score
    finished = perf_counter()
    prefix = frozenset(ranking[:k])
    return RevisionResult(best, prefix, value, count, len(best-prefix),
                          enumerated-start, finished-enumerated, finished-start)


def complete_table_bounds(items: Sequence[int], values: Mapping[Subset, float],
                          radii: Mapping[Subset, float], scores: Mapping[int, float]):
    """Deterministic transfer ON an externally justified simultaneous CI event.

    If |f(S)-values[S]| <= radii[S] for EVERY subset, returned bounds control
    true interaction delta, score residual eta, and singleton-score error u.
    This does not estimate coverage probability. Sampled maxima, neural training
    loss and ensemble variance cannot be supplied as certified radii by fiat.
    Reject incomplete tables: unobserved interactions can be arbitrarily large.
    """
    items = _validate(items, 0, 0)
    if not items:
        raise ValueError('at least one item is required')
    subsets = [frozenset(c) for n in range(len(items)+1) for c in combinations(items, n)]
    expected = set(subsets)
    if set(values) != expected or set(radii) != expected or set(scores) != set(items):
        raise ValueError('need every subset and every item score, with no extra keys')
    if any(not isfinite(float(v)) for v in values.values()) or any(
            not isfinite(float(v)) for v in scores.values()):
        raise ValueError('values and scores must be finite')
    if any(not isfinite(float(r)) or r < 0 for r in radii.values()):
        raise ValueError('radii must be finite and nonnegative')
    empty = frozenset()
    delta = eta = u = 0.0
    for i in items:
        single = frozenset([i])
        estimated_gain = values[single]-values[empty]
        u = max(u, abs(scores[i]-estimated_gain)+radii[single]+radii[empty])
        for A in subsets:
            if i in A:
                continue
            Ai = A | single
            marginal = values[Ai]-values[A]
            eta = max(eta, abs(marginal-scores[i])+radii[Ai]+radii[A])
            # A=empty has identically zero interaction; avoid counting the same
            # noisy quantities twice and making the certificate needlessly loose.
            if A:
                delta = max(delta, abs(marginal-estimated_gain)+radii[Ai]+radii[A]
                            +radii[single]+radii[empty])
    return {'delta_upper': float(delta), 'score_residual_upper': float(eta),
            'score_error_upper': float(u),
            'scope': 'conditional on simultaneous coverage of the complete value table'}
