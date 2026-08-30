"""Finite additive / near-additive response worlds for exact chain tests."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence, Tuple

import numpy as np

from .support import Action, SupportModel


@dataclass(frozen=True)
class FiniteResponseWorld:
    support: SupportModel
    primitives: Tuple[np.ndarray, ...]
    baseline: float = 0.0
    residual: Mapping[Action, float] | None = None

    def __post_init__(self) -> None:
        arrays = tuple(np.asarray(values, dtype=np.float64).copy() for values in self.primitives)
        if len(arrays) != self.support.n_relations:
            raise ValueError("one primitive component is required per relation")
        for j, (values, size) in enumerate(zip(arrays, self.support.action_sizes)):
            if values.shape != (size,):
                raise ValueError(f"primitive {j} must have shape ({size},)")
            if not np.all(np.isfinite(values)):
                raise ValueError("primitive components must be finite")
        object.__setattr__(self, "primitives", arrays)
        if not np.isfinite(self.baseline):
            raise ValueError("baseline must be finite")
        if self.residual is not None:
            clean = {tuple(k): float(v) for k, v in self.residual.items()}
            full = set(self.support.full_product())
            if not set(clean) <= full:
                raise ValueError("residual contains actions outside full product")
            if not all(np.isfinite(v) for v in clean.values()):
                raise ValueError("residual values must be finite")
            object.__setattr__(self, "residual", clean)

    def additive_value(self, action: Sequence[int]) -> float:
        action = tuple(int(x) for x in action)
        return float(self.baseline + sum(self.primitives[j][a] for j, a in enumerate(action)))

    def residual_value(self, action: Sequence[int]) -> float:
        if self.residual is None:
            return 0.0
        return float(self.residual.get(tuple(int(x) for x in action), 0.0))

    def true_value(self, action: Sequence[int]) -> float:
        return self.additive_value(action) + self.residual_value(action)

    def residual_supnorm(self) -> float:
        return float(max((abs(self.residual_value(a)) for a in self.support.full_product()), default=0.0))

    def component_span(self, j: int, support: SupportModel | None = None) -> float:
        support = self.support if support is None else support
        idx = np.asarray(support.projection(j), dtype=int)
        values = self.primitives[int(j)][idx]
        return float(np.max(values) - np.min(values))

    def component_spans(self, support: SupportModel | None = None) -> np.ndarray:
        return np.asarray([
            self.component_span(j, support=support)
            for j in range(self.support.n_relations)
        ], dtype=np.float64)

    def omitted_values(self, retained: Sequence[int], support: SupportModel | None = None) -> np.ndarray:
        support = self.support if support is None else support
        retained = {int(j) for j in retained}
        return np.asarray([
            sum(self.primitives[j][a[j]] for j in range(self.support.n_relations) if j not in retained)
            for a in support.omega
        ], dtype=np.float64)

    def additive_radius(self, retained: Sequence[int], support: SupportModel | None = None) -> float:
        values = self.omitted_values(retained, support=support)
        return 0.5 * float(np.max(values) - np.min(values))

    def true_compression_loss(self, retained: Sequence[int], support: SupportModel | None = None) -> float:
        """Best scalar residual after retaining the primitive additive terms.

        F = baseline + retained primitives + [omitted primitives + residual].
        The best scalar correction therefore has half the oscillation of the
        bracketed residual on the declared support.
        """
        support = self.support if support is None else support
        retained = {int(j) for j in retained}
        values = []
        for a in support.omega:
            omitted = sum(
                self.primitives[j][a[j]]
                for j in range(self.support.n_relations)
                if j not in retained
            )
            values.append(omitted + self.residual_value(a))
        values = np.asarray(values, dtype=np.float64)
        return 0.5 * float(np.max(values) - np.min(values))
