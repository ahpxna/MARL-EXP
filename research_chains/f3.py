"""Generic paired-shadow protocol for moving-estimand experiments.

This module does not claim a CIG-AMF learned-policy result by itself.  It
provides the reusable contract needed to compare a no-measurement branch with
an intervention branch while tracking learner/policy/estimand versions.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Generic, Protocol, TypeVar
import copy


S = TypeVar("S")
L = TypeVar("L")


class CloneableEnvironment(Protocol):
    def clone_state(self): ...
    def restore_state(self, state): ...


@dataclass(frozen=True)
class ShadowSnapshot:
    environment_state: object
    learner_state: object
    policy_version: str
    estimand_key: str


@dataclass(frozen=True)
class ShadowOutcome:
    no_measurement_target: float
    measurement_target: float
    target_drift: float
    no_measurement_policy_version: str
    measurement_policy_version: str
    target_key_changed: bool


def paired_shadow_experiment(
    *,
    environment,
    learner,
    clone_learner: Callable[[L], L] = copy.deepcopy,
    policy_version: Callable[[L], str],
    estimand_key: Callable[[L], str],
    step_branch: Callable[[object, L, bool], None],
    measure_target: Callable[[object, L], float],
) -> ShadowOutcome:
    """Run exactly paired no-measurement and measurement learner branches.

    ``step_branch(env, learner, measurement)`` owns the full rollout/update.
    The caller must make both branches deterministic/common-random-number when
    that is scientifically required.
    """
    state = copy.deepcopy(environment.clone_state())
    learner0 = clone_learner(learner)

    # No-measurement counterfactual.
    environment.restore_state(copy.deepcopy(state))
    no_learner = clone_learner(learner0)
    step_branch(environment, no_learner, False)
    no_target = float(measure_target(environment, no_learner))
    no_policy = str(policy_version(no_learner))
    no_key = str(estimand_key(no_learner))

    # Measurement/intervention branch.
    environment.restore_state(copy.deepcopy(state))
    yes_learner = clone_learner(learner0)
    step_branch(environment, yes_learner, True)
    yes_target = float(measure_target(environment, yes_learner))
    yes_policy = str(policy_version(yes_learner))
    yes_key = str(estimand_key(yes_learner))

    return ShadowOutcome(
        no_measurement_target=no_target,
        measurement_target=yes_target,
        target_drift=abs(yes_target - no_target),
        no_measurement_policy_version=no_policy,
        measurement_policy_version=yes_policy,
        target_key_changed=(no_key != yes_key),
    )
