"""Finite feasible-support objects and uncertainty brackets."""

from __future__ import annotations

from dataclasses import dataclass
import itertools
from typing import Iterable, Sequence, Tuple

import numpy as np


Action = Tuple[int, ...]


def _normalize_actions(actions: Iterable[Sequence[int]]) -> Tuple[Action, ...]:
    return tuple(sorted({tuple(int(x) for x in action) for action in actions}))


@dataclass(frozen=True)
class SupportModel:
    action_sizes: Tuple[int, ...]
    omega: Tuple[Action, ...]
    key: str = "support"

    def __post_init__(self) -> None:
        sizes = tuple(int(x) for x in self.action_sizes)
        if not sizes or any(x <= 0 for x in sizes):
            raise ValueError("action_sizes must contain positive integers")
        normalized = _normalize_actions(self.omega)
        if not normalized:
            raise ValueError("omega must be non-empty")
        for action in normalized:
            if len(action) != len(sizes):
                raise ValueError("joint action has wrong dimensionality")
            if any(a < 0 or a >= sizes[j] for j, a in enumerate(action)):
                raise ValueError(f"joint action outside action alphabet: {action}")
        object.__setattr__(self, "action_sizes", sizes)
        object.__setattr__(self, "omega", normalized)
        if not str(self.key).strip():
            raise ValueError("support key must be non-empty")

    @property
    def n_relations(self) -> int:
        return len(self.action_sizes)

    def projection(self, j: int) -> Tuple[int, ...]:
        j = int(j)
        return tuple(sorted({action[j] for action in self.omega}))

    def contains(self, action: Sequence[int]) -> bool:
        return tuple(int(x) for x in action) in set(self.omega)

    def full_product(self) -> Tuple[Action, ...]:
        return tuple(itertools.product(*(range(size) for size in self.action_sizes)))

    def is_subset_of(self, other: "SupportModel") -> bool:
        return self.action_sizes == other.action_sizes and set(self.omega) <= set(other.omega)


@dataclass(frozen=True)
class SupportBracket:
    lower: SupportModel
    upper: SupportModel

    def __post_init__(self) -> None:
        if self.lower.action_sizes != self.upper.action_sizes:
            raise ValueError("support brackets must share action alphabets")
        if not self.lower.is_subset_of(self.upper):
            raise ValueError("support lower bracket must be a subset of upper bracket")

    def validates(self, truth: SupportModel) -> bool:
        return self.lower.is_subset_of(truth) and truth.is_subset_of(self.upper)


def projected_span_bracket(primitives, bracket: SupportBracket):
    """Return C^- and C^+ implied only by nested projected supports."""
    minus, plus = [], []
    for j, values in enumerate(primitives):
        values = np.asarray(values, dtype=np.float64)
        lo_idx = np.asarray(bracket.lower.projection(j), dtype=int)
        hi_idx = np.asarray(bracket.upper.projection(j), dtype=int)
        minus.append(float(np.max(values[lo_idx]) - np.min(values[lo_idx])))
        plus.append(float(np.max(values[hi_idx]) - np.min(values[hi_idx])))
    return np.asarray(minus), np.asarray(plus)
