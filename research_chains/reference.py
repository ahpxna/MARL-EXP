"""Reference-kernel semantics, isolation deviation and product-surrogate route."""

from __future__ import annotations

from dataclasses import dataclass
import itertools
from typing import Dict, Mapping, Sequence, Tuple

import numpy as np

from .certificates import oscillation
from .finite_world import FiniteResponseWorld
from .support import Action, SupportModel


Distribution = Mapping[Action, float]


@dataclass(frozen=True)
class ConditionalReferenceKernel:
    source: int
    action_sizes: Tuple[int, ...]
    by_source_action: Mapping[int, Distribution]
    key: str = "kappa"

    def __post_init__(self) -> None:
        source = int(self.source)
        sizes = tuple(int(x) for x in self.action_sizes)
        if source < 0 or source >= len(sizes):
            raise ValueError("invalid source coordinate")
        expected = set(range(sizes[source]))
        if set(int(a) for a in self.by_source_action) != expected:
            raise ValueError("kernel must define every source action")
        clean: Dict[int, Dict[Action, float]] = {}
        for source_action, dist in self.by_source_action.items():
            source_action = int(source_action)
            row = {}
            total = 0.0
            for joint, probability in dist.items():
                joint = tuple(int(x) for x in joint)
                probability = float(probability)
                if len(joint) != len(sizes) or joint[source] != source_action:
                    raise ValueError("kernel joint action disagrees with conditioned source action")
                if any(a < 0 or a >= sizes[j] for j, a in enumerate(joint)):
                    raise ValueError("kernel references action outside alphabet")
                if probability < 0.0 or not np.isfinite(probability):
                    raise ValueError("kernel probabilities must be finite and non-negative")
                if probability > 0.0:
                    row[joint] = row.get(joint, 0.0) + probability
                    total += probability
            if not np.isclose(total, 1.0, rtol=1e-10, atol=1e-12):
                raise ValueError(f"kernel row must sum to one; got {total}")
            clean[source_action] = row
        object.__setattr__(self, "source", source)
        object.__setattr__(self, "action_sizes", sizes)
        object.__setattr__(self, "by_source_action", clean)
        if not str(self.key).strip():
            raise ValueError("kernel key must be non-empty")

    @classmethod
    def uniform_feasible(cls, support: SupportModel, source: int, key: str = "uniform_feasible"):
        rows = {}
        for a in range(support.action_sizes[source]):
            compatible = [joint for joint in support.omega if joint[source] == a]
            if not compatible:
                raise ValueError(f"source action {a} has no feasible co-action")
            p = 1.0 / len(compatible)
            rows[a] = {joint: p for joint in compatible}
        return cls(source=source, action_sizes=support.action_sizes, by_source_action=rows, key=key)

    @classmethod
    def product(cls, action_sizes: Sequence[int], source: int, marginals: Mapping[int, Sequence[float]], key: str = "product"):
        sizes = tuple(int(x) for x in action_sizes)
        other = [j for j in range(len(sizes)) if j != int(source)]
        probs = {}
        for j in other:
            row = np.asarray(marginals[j], dtype=np.float64)
            if row.shape != (sizes[j],) or np.any(row < 0.0) or not np.isclose(row.sum(), 1.0):
                raise ValueError(f"invalid product marginal for coordinate {j}")
            probs[j] = row
        rows = {}
        for source_action in range(sizes[int(source)]):
            dist = {}
            for values in itertools.product(*(range(sizes[j]) for j in other)):
                joint = [0] * len(sizes); joint[int(source)] = source_action
                probability = 1.0
                for j, value in zip(other, values):
                    joint[j] = value; probability *= float(probs[j][value])
                dist[tuple(joint)] = probability
            rows[source_action] = dist
        return cls(source=int(source), action_sizes=sizes, by_source_action=rows, key=key)

    def support_compatible(self, support: SupportModel) -> bool:
        if support.action_sizes != self.action_sizes:
            return False
        omega = set(support.omega)
        return all(joint in omega for dist in self.by_source_action.values() for joint, p in dist.items() if p > 0.0)

    def response_vector(self, world: FiniteResponseWorld, *, true_response: bool = True) -> np.ndarray:
        fn = world.true_value if true_response else world.additive_value
        return np.asarray([
            sum(prob * fn(joint) for joint, prob in self.by_source_action[a].items())
            for a in range(self.action_sizes[self.source])
        ], dtype=np.float64)

    def complement_expectation(self, world: FiniteResponseWorld) -> np.ndarray:
        j = self.source
        return np.asarray([
            sum(
                prob * sum(world.primitives[l][joint[l]] for l in range(len(self.action_sizes)) if l != j)
                for joint, prob in self.by_source_action[a].items()
            )
            for a in range(self.action_sizes[j])
        ], dtype=np.float64)

    def isolation_deviation(self, world: FiniteResponseWorld) -> float:
        return oscillation(self.complement_expectation(world))

    def residual_deviation(self, world: FiniteResponseWorld) -> float:
        values = np.asarray([
            sum(prob * world.residual_value(joint) for joint, prob in self.by_source_action[a].items())
            for a in range(self.action_sizes[self.source])
        ], dtype=np.float64)
        return oscillation(values)

    def marginal(self, source_action: int, coordinate: int) -> np.ndarray:
        coordinate = int(coordinate)
        if coordinate == self.source:
            raise ValueError("complement marginal requires coordinate != source")
        out = np.zeros(self.action_sizes[coordinate], dtype=np.float64)
        for joint, prob in self.by_source_action[int(source_action)].items():
            out[joint[coordinate]] += prob
        return out

    def complement_marginals_invariant(self, atol: float = 1e-12) -> bool:
        """Finite iff condition for all additive complement functions.

        Expectations of every separable complement function are independent of
        the source action iff each complement-coordinate marginal is invariant.
        """
        for coordinate in range(len(self.action_sizes)):
            if coordinate == self.source:
                continue
            reference = self.marginal(0, coordinate)
            for action in range(1, self.action_sizes[self.source]):
                if not np.allclose(reference, self.marginal(action, coordinate), atol=atol, rtol=0.0):
                    return False
        return True

    def tv_diameter(self) -> float:
        """Max TV distance between full complement distributions."""
        source_actions = range(self.action_sizes[self.source])
        support = sorted({
            tuple(joint[l] for l in range(len(self.action_sizes)) if l != self.source)
            for dist in self.by_source_action.values() for joint in dist
        })
        rows = []
        for a in source_actions:
            lookup = {}
            for joint, prob in self.by_source_action[a].items():
                key = tuple(joint[l] for l in range(len(self.action_sizes)) if l != self.source)
                lookup[key] = lookup.get(key, 0.0) + prob
            rows.append(np.asarray([lookup.get(key, 0.0) for key in support]))
        best = 0.0
        for left in range(len(rows)):
            for right in range(left + 1, len(rows)):
                best = max(best, 0.5 * float(np.abs(rows[left] - rows[right]).sum()))
        return best

    def tv_isolation_upper_bound(self, world: FiniteResponseWorld) -> float:
        complement_span_sum = sum(
            world.component_span(l)
            for l in range(world.support.n_relations)
            if l != self.source
        )
        return float(complement_span_sum * self.tv_diameter())


def product_reference_surrogate(world: FiniteResponseWorld, marginals: Mapping[int, Sequence[float]]):
    """Paper-13-style product-reference additive surrogate of the true F."""
    m = world.support.n_relations
    rows = []
    baseline = 0.0
    for action in world.support.full_product():
        p = 1.0
        for j, a in enumerate(action):
            p *= float(np.asarray(marginals[j])[a])
        baseline += p * world.true_value(action)
    for j in range(m):
        kernel = ConditionalReferenceKernel.product(world.support.action_sizes, j, marginals, key=f"product_j{j}")
        rows.append(kernel.response_vector(world, true_response=True))
    def surrogate(action):
        return float(sum(rows[j][action[j]] for j in range(m)) - (m - 1) * baseline)
    return float(baseline), tuple(rows), surrogate

def reference_fidelity_characterization(kernel: ConditionalReferenceKernel, atol: float = 1e-12):
    """Finite characterization for universal additive-complement isolation.

    For the function class H(a_-j)=sum_{l!=j} h_l(a_l), the conditional
    expectation E_kappa[H | a_j] is constant for every H iff every complement
    coordinate marginal is invariant in a_j.  When the condition fails this
    routine returns an indicator-basis witness.
    """
    invariant = kernel.complement_marginals_invariant(atol=atol)
    witness = None
    if not invariant:
        for coordinate in range(len(kernel.action_sizes)):
            if coordinate == kernel.source:
                continue
            for value in range(kernel.action_sizes[coordinate]):
                expectations = np.asarray([
                    kernel.marginal(a, coordinate)[value]
                    for a in range(kernel.action_sizes[kernel.source])
                ], dtype=np.float64)
                if float(np.max(expectations) - np.min(expectations)) > atol:
                    witness = {
                        "coordinate": int(coordinate),
                        "value": int(value),
                        "conditional_expectations": expectations.tolist(),
                        "oscillation": float(np.max(expectations) - np.min(expectations)),
                    }
                    break
            if witness is not None:
                break
    return {"marginal_invariant": bool(invariant), "witness": witness}
