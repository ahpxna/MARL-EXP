"""Score-uncertainty to support-aware decision-regret transfer."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence

import numpy as np

from .certificates import topk_indices


@dataclass(frozen=True)
class ScoreErrorTerm:
    """A score-error radius tied to one explicit estimand/target key.

    The MASTER theorem only permits additive composition when every radius
    covers the same underlying score target.  Keeping the target key next to
    each term makes that invariant executable instead of relying on comments.
    """

    target_key: str
    values: Sequence[float]
    source: str = "unspecified"


def compose_score_error(*terms: Sequence[float]) -> np.ndarray:
    """Legacy untyped vector sum retained for backwards compatibility.

    New scientific code should prefer :func:`compose_same_target_score_error`
    so that incompatible estimands fail closed.
    """
    if not terms:
        raise ValueError("at least one error term is required")
    arrays = [np.asarray(term, dtype=np.float64) for term in terms]
    shape = arrays[0].shape
    if len(shape) != 1 or any(arr.shape != shape for arr in arrays):
        raise ValueError("all error terms must be same-length vectors")
    if any(np.any(arr < -1e-12) or not np.all(np.isfinite(arr)) for arr in arrays):
        raise ValueError("error terms must be finite and non-negative")
    return np.sum(arrays, axis=0)


def compose_same_target_score_error(*terms: ScoreErrorTerm) -> np.ndarray:
    """Compose non-negative score radii only when all terms share one target.

    This mirrors the P12 ``SameTargetScoreChain`` contract.  It deliberately
    rejects silent composition across isolated-reference, feasible-reference,
    product-reference, or otherwise distinct score semantics.
    """
    if not terms:
        raise ValueError("at least one typed error term is required")
    target_keys = {str(term.target_key) for term in terms}
    if len(target_keys) != 1:
        raise ValueError(f"score-error terms do not share one target: {sorted(target_keys)}")
    return compose_score_error(*(term.values for term in terms))


def sharp_gamma(true_scores: Sequence[float], estimated_scores: Sequence[float], errors: Sequence[float], k: int) -> float:
    true_scores = np.asarray(true_scores, dtype=np.float64)
    estimated_scores = np.asarray(estimated_scores, dtype=np.float64)
    errors = np.asarray(errors, dtype=np.float64)
    if np.any(np.abs(estimated_scores - true_scores) - errors > 1e-10):
        raise ValueError("supplied score errors do not cover the true scores")
    true_set = set(topk_indices(true_scores, int(k)))
    estimated_set = set(topk_indices(estimated_scores, int(k)))
    swapped = true_set - estimated_set, estimated_set - true_set
    return 0.5 * float(sum(errors[j] for part in swapped for j in part))


def operational_gamma(estimated_scores: Sequence[float], errors: Sequence[float], k: int, selected: Sequence[int] | None = None) -> float:
    estimated_scores = np.asarray(estimated_scores, dtype=np.float64)
    errors = np.asarray(errors, dtype=np.float64)
    if estimated_scores.shape != errors.shape or estimated_scores.ndim != 1:
        raise ValueError("estimated_scores/errors must be same-length vectors")
    if np.any(errors < -1e-12) or not np.all(np.isfinite(estimated_scores)) or not np.all(np.isfinite(errors)):
        raise ValueError("scores/errors must be finite and errors non-negative")
    lower = estimated_scores - errors
    upper = estimated_scores + errors
    selected = topk_indices(estimated_scores, int(k)) if selected is None else tuple(int(j) for j in selected)
    if len(set(selected)) != int(k):
        raise ValueError("selected must contain exactly k unique indices")
    optimistic = topk_indices(upper, int(k))
    value = 0.5 * (float(np.sum(upper[list(optimistic)])) - float(np.sum(lower[list(selected)])))
    return max(0.0, value)


def topk_interval_certified(estimated_scores: Sequence[float], errors: Sequence[float], k: int) -> bool:
    scores = np.asarray(estimated_scores, dtype=np.float64)
    errors = np.asarray(errors, dtype=np.float64)
    chosen = set(topk_indices(scores, int(k)))
    lower = scores - errors; upper = scores + errors
    if len(chosen) == scores.size:
        return True
    return float(min(lower[list(chosen)])) > float(max(upper[[j for j in range(scores.size) if j not in chosen]]))


def pairwise_master_bound(gamma: float, zeta_def_value: float, eta: float) -> float:
    if min(gamma, zeta_def_value, eta) < -1e-12:
        raise ValueError("bound components must be non-negative")
    return float(gamma + 0.5 * zeta_def_value + 2.0 * eta)
