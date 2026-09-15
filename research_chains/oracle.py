"""Clone-state joint-response oracle adapter for MARL environments.

The adapter intentionally knows nothing about C/D/Paper-A/Paper-B. It exposes
finite joint responses over a chosen subset of source agents while all other
agents follow a frozen baseline action vector. This is the bridge from actual
environments to the finite support/reference/compression harness.

Execution semantics are deliberately explicit.  Environments are allowed to
store ``last_actions`` either as a sequence or as an ``agent_id -> action``
mapping.  The adapter normalizes both representations before checking whether
an intervention request was honored.  This prevents dictionary keys from being
mistaken for executed actions (the historical OmniArena bridge bug).
"""

from __future__ import annotations

from dataclasses import dataclass
import copy
import itertools
from typing import Mapping, Sequence, Tuple

import numpy as np

from .support import SupportModel


def trusted_execution_receipt(env):
    """Return an explicit post-resolution execution receipt.

    ``last_actions`` is not a universal execution contract: several external
    adapters only use it to remember submitted commands.  Scientific oracles
    therefore require the environment to opt in with a callable
    ``trusted_execution_receipt`` provider.  This prevents requested commands
    from being silently relabelled as executed actions.
    """
    provider = getattr(env, "trusted_execution_receipt", None)
    if not callable(provider):
        raise RuntimeError(
            "environment does not expose trusted post-resolution executed-action telemetry / execution "
            "receipt; submitted/requested actions cannot be treated as executed"
        )
    receipt = provider()
    if receipt is None:
        raise RuntimeError("trusted execution-receipt provider returned None")
    return receipt


@dataclass(frozen=True)
class JointOracleRecord:
    """One clone-state joint intervention.

    ``execution_verified`` is the CETERIS-PARIBUS gate: it is true only when the
    whole requested joint action vector was executed, sources and frozen
    baseline alike.  Verifying only the source coordinates does not establish
    the intended counterfactual ``F(a_S, a_baseline_{-S})``: an environment that
    honours the intervention while quietly overriding some other agent's
    baseline action has executed a DIFFERENT joint action, and the response is
    then not a response at the requested point.  The weaker source-only check is
    still reported, separately, as ``execution_verified_sources``.

    ``estimand`` names what ``reward`` actually is, so a one-step reward is never
    read as a continuation return.
    """

    assignment: Tuple[int, ...]
    reward: float
    requested_joint_actions: Tuple[int, ...]
    executed_joint_actions: Tuple[int, ...]
    execution_verified: bool
    execution_verified_sources: bool = True
    estimand: str = "Q_one_step"
    horizon: int = 1
    discount: float = 1.0


class CloneStateJointOracle:
    @staticmethod
    def _copy_snapshot(env, snapshot):
        """Copy an environment snapshot through the adapter contract when available.

        Some external simulators expose opaque native snapshot handles (for
        example ``cityflow.Archive``) that cannot be pickled or deep-copied.
        External adapters may therefore provide ``_copy_cloned_state`` to copy
        only the Python-owned parts while preserving the reusable native handle.
        Fall back to ``copy.deepcopy`` for ordinary pure-Python environments.
        """
        copier = getattr(env, "_copy_cloned_state", None)
        if callable(copier):
            return copier(snapshot)
        return copy.deepcopy(snapshot)

    #: The two execution semantics this oracle can be asked for.  They are NOT
    #: interchangeable and are never silently mixed: ``full_joint`` is the
    #: ceteris-paribus contract, ``source_only`` merely records that the
    #: intervention itself was honoured and must be declared by the caller.
    EXECUTION_SEMANTICS = ("full_joint", "source_only")

    def __init__(self, env, *, snapshot, outcome_agent: int, baseline_actions: Sequence[int],
                 execution_semantics: str = "full_joint",
                 horizon: int = 1, discount: float = 1.0, continuation_policy=None):
        if str(execution_semantics) not in self.EXECUTION_SEMANTICS:
            raise ValueError(
                "execution_semantics must be one of " + ",".join(self.EXECUTION_SEMANTICS))
        if int(horizon) < 1:
            raise ValueError("horizon must be at least 1")
        if int(horizon) > 1 and continuation_policy is None:
            raise ValueError(
                "a continuation return needs an explicit frozen continuation policy; "
                "pass continuation_policy=callable(env) -> joint action")
        if not 0.0 <= float(discount) <= 1.0:
            raise ValueError("discount must lie in [0, 1]")
        self.execution_semantics = str(execution_semantics)
        self.horizon = int(horizon)
        self.discount = float(discount)
        self.continuation_policy = continuation_policy
        self.env = env
        self.snapshot = self._copy_snapshot(env, snapshot)
        self.outcome_agent = int(outcome_agent)
        self.baseline_actions = tuple(int(x) for x in baseline_actions)
        if len(self.baseline_actions) != int(env.n_agents):
            raise ValueError("baseline_actions must contain one action per environment agent")
        if self.outcome_agent < 0 or self.outcome_agent >= int(env.n_agents):
            raise ValueError("invalid outcome_agent")

    @staticmethod
    def _normalize_executed_actions(raw_actions, *, n_agents: int) -> Tuple[int, ...]:
        """Return actions in canonical agent-index order.

        ``OmniArena.last_actions`` is a dict. Iterating a dict yields its keys,
        so ``tuple(last_actions)`` silently returns ``(0,1,2,...)`` rather than
        the executed commands.  Normalize mappings and sequences separately and
        fail closed on incomplete/ill-shaped execution telemetry.
        """
        if raw_actions is None:
            raise RuntimeError(
                "environment does not expose executed-action telemetry; "
                "requested actions cannot be treated as executed actions"
            )
        if isinstance(raw_actions, Mapping):
            missing = [agent for agent in range(int(n_agents)) if agent not in raw_actions]
            if missing:
                raise RuntimeError(
                    "executed-action mapping is missing agent ids: "
                    + ",".join(str(x) for x in missing[:10])
                )
            return tuple(int(raw_actions[agent]) for agent in range(int(n_agents)))
        try:
            values = tuple(int(x) for x in raw_actions)
        except TypeError as exc:
            raise RuntimeError("executed-action telemetry is neither a mapping nor a sequence") from exc
        if len(values) != int(n_agents):
            raise RuntimeError(
                f"executed-action sequence has length {len(values)}, expected {int(n_agents)}"
            )
        return values

    def evaluate(self, source_agents: Sequence[int], assignment: Sequence[int]) -> JointOracleRecord:
        source_agents = tuple(int(x) for x in source_agents)
        assignment = tuple(int(x) for x in assignment)
        if len(source_agents) != len(assignment) or len(set(source_agents)) != len(source_agents):
            raise ValueError("source_agents/assignment mismatch or duplicate source")
        actions = list(self.baseline_actions)
        for source, action in zip(source_agents, assignment):
            if source < 0 or source >= int(self.env.n_agents):
                raise ValueError("invalid source agent")
            actions[source] = action
        self.env.restore_state(self._copy_snapshot(self.env, self.snapshot))
        _, rewards, _, _ = self.env.step(actions)
        requested = tuple(int(x) for x in actions)
        executed = self._normalize_executed_actions(
            trusted_execution_receipt(self.env), n_agents=int(self.env.n_agents)
        )
        # Source-only agreement is the weaker historical check; it is kept for
        # diagnostics but is NOT what gates the counterfactual.
        verified_sources = all(
            executed[source] == action for source, action in zip(source_agents, assignment))
        verified_full = tuple(executed) == requested
        verified = verified_full if self.execution_semantics == "full_joint" else verified_sources
        reward = float(rewards[self.outcome_agent])
        if self.horizon > 1:
            # Explicit continuation return: intervene only at t, then roll the
            # frozen continuation policy forward for horizon-1 further steps.
            discounted = reward
            factor = 1.0
            for _ in range(self.horizon - 1):
                factor *= self.discount
                follow = self.continuation_policy(self.env)
                _, rewards_t, done, _ = self.env.step(
                    [int(x) for x in follow])
                discounted += factor * float(rewards_t[self.outcome_agent])
                if bool(np.all(done)) if np.ndim(done) else bool(done):
                    break
            reward = float(discounted)
        self.env.restore_state(self._copy_snapshot(self.env, self.snapshot))
        return JointOracleRecord(
            assignment=assignment,
            reward=reward,
            requested_joint_actions=requested,
            executed_joint_actions=executed,
            execution_verified=bool(verified),
            execution_verified_sources=bool(verified_sources),
            estimand=("Q_one_step" if self.horizon == 1
                      else f"Q_continuation_h{self.horizon}_gamma{self.discount}"),
            horizon=int(self.horizon),
            discount=float(self.discount),
        )

    def enumerate(self, source_agents: Sequence[int], action_sets: Sequence[Sequence[int]], *, fail_on_execution_mismatch: bool = False):
        source_agents = tuple(int(x) for x in source_agents)
        if len(source_agents) != len(action_sets):
            raise ValueError("one action set is required per source agent")
        records = []
        for assignment in itertools.product(*(tuple(int(a) for a in row) for row in action_sets)):
            record = self.evaluate(source_agents, assignment)
            if fail_on_execution_mismatch and not record.execution_verified:
                raise RuntimeError(f"requested joint action not executed for assignment={assignment}")
            records.append(record)
        return tuple(records)

    def feasible_support(self, source_agents: Sequence[int], action_sets: Sequence[Sequence[int]]) -> SupportModel:
        records = self.enumerate(source_agents, action_sets, fail_on_execution_mismatch=False)
        omega = tuple(record.assignment for record in records if record.execution_verified)
        if not omega:
            raise RuntimeError("no requested joint assignments executed exactly")
        # Local alphabets are indexed by actual action ids, so require contiguous
        # [0, max] action sets for conversion to SupportModel. A caller with a
        # sparse semantic subset should remap ids explicitly rather than hide it.
        sizes = []
        for row in action_sets:
            row = tuple(sorted(set(int(a) for a in row)))
            if row != tuple(range(max(row) + 1)):
                raise ValueError("SupportModel adapter requires contiguous local action ids; remap sparse action sets")
            sizes.append(max(row) + 1)
        return SupportModel(tuple(sizes), omega, key="clone_state_executed_support")

    def response_table(self, source_agents: Sequence[int], action_sets: Sequence[Sequence[int]], *, require_feasible: bool = True) -> Mapping[Tuple[int, ...], float]:
        records = self.enumerate(source_agents, action_sets, fail_on_execution_mismatch=False)
        table = {}
        for record in records:
            if require_feasible and not record.execution_verified:
                continue
            table[record.assignment] = float(record.reward)
        if not table:
            raise RuntimeError("response table is empty")
        return table
