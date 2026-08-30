"""Fail-closed capability audit for external CIG-AMF environments.

The audit deliberately distinguishes requestable command support from resolved /
honored command support.  A benchmark may accept a Cartesian tuple of requests
and subsequently cancel a conflicting command; that is *not* evidence that the
requestable support itself is non-Cartesian.
"""
from __future__ import annotations

from dataclasses import dataclass, asdict
import itertools
from typing import Any, Callable, Mapping, Sequence

import numpy as np

STATUS_SUPPORTED = "SUPPORTED"
STATUS_RESTRICTED = "SUPPORTED_WITH_RESTRICTIONS"
STATUS_NOT = "NOT_SUPPORTED"
STATUS_UNVERIFIED = "UNVERIFIED"
VALID_STATUSES = {STATUS_SUPPORTED, STATUS_RESTRICTED, STATUS_NOT, STATUS_UNVERIFIED}

CAPABILITY_KEYS = (
    "clone_restore",
    "valid_action_mask",
    "execution_receipt",
    "fixed_continuation",
    "requestable_joint_support",
    "honored_joint_support",
    "joint_feasibility_oracle",
    "coupled_honored_support_observed",
    "full_cartesian_testable",
    "reference_kernel_observable",
    "message_deletion",
    "communication_delay",
    "agent_removal",
    "learned_policy_hook",
    "mixed_difference_testable",
)

@dataclass(frozen=True)
class CapabilityEntry:
    status: str
    reason: str
    evidence: Mapping[str, Any] | None = None

    def __post_init__(self):
        if self.status not in VALID_STATUSES:
            raise ValueError(f"invalid capability status: {self.status}")

    def payload(self) -> dict:
        return asdict(self)


def _entry(status: str, reason: str, **evidence) -> CapabilityEntry:
    return CapabilityEntry(status, reason, evidence or None)


def static_capability_profile(key: str) -> dict[str, CapabilityEntry]:
    """Conservative claims supported by the adapters as implemented.

    These are *not* runtime verification results.  Runtime-only properties such
    as execution receipts and observed coupling remain UNVERIFIED until probed.
    """
    key = str(key).lower()
    if key not in {"omni", "rware", "flatland", "cyborg", "cityflow"}:
        raise KeyError(key)
    common = {
        "clone_restore": _entry(STATUS_SUPPORTED, "adapter implements clone_state/restore_state"),
        "valid_action_mask": _entry(STATUS_SUPPORTED, "adapter exposes an explicit per-agent mask"),
        "fixed_continuation": _entry(STATUS_SUPPORTED, "adapter exposes a fixed continuation policy"),
        "requestable_joint_support": _entry(STATUS_RESTRICTED, "Cartesian product of per-agent request masks; this is not a joint-feasibility oracle"),
        "joint_feasibility_oracle": _entry(STATUS_NOT, "no pre-execution joint admissibility oracle is exposed"),
        "reference_kernel_observable": _entry(STATUS_NOT, "adapter does not expose a conditional co-action kernel estimator by itself"),
        "message_deletion": _entry(STATUS_NOT, "no standardized message-deletion intervention in the current adapter"),
        "communication_delay": _entry(STATUS_NOT, "no standardized delayed-message intervention in the current adapter"),
        "agent_removal": _entry(STATUS_NOT, "no standardized agent-removal intervention in the current adapter"),
        "learned_policy_hook": _entry(STATUS_RESTRICTED, "training can wrap the adapter, but no claim-specific endogenous learner hook is exposed here"),
    }
    if key == "omni":
        common.update({
            "execution_receipt": _entry(STATUS_SUPPORTED, "Omni exposes executed last_actions and was authority-audited"),
            "honored_joint_support": _entry(STATUS_SUPPORTED, "executed command tuples can be enumerated from clone states"),
            "coupled_honored_support_observed": _entry(STATUS_NOT, "Omni command support is intentionally Cartesian"),
            "full_cartesian_testable": _entry(STATUS_SUPPORTED, "full finite command alphabet is enumerable"),
            "mixed_difference_testable": _entry(STATUS_SUPPORTED, "clone-state full product response tables can be built"),
        })
    elif key == "rware":
        common.update({
            "execution_receipt": _entry(STATUS_UNVERIFIED, "runtime probe must confirm post-resolution req_action telemetry"),
            "honored_joint_support": _entry(STATUS_UNVERIFIED, "RWARE can cancel conflicting movement requests; resolved tuples must be probed"),
            "coupled_honored_support_observed": _entry(STATUS_UNVERIFIED, "requires runtime enumeration of resolved joint actions"),
            "full_cartesian_testable": _entry(STATUS_RESTRICTED, "requestable tuples are enumerable, but resolved support may be coupled"),
            "mixed_difference_testable": _entry(STATUS_RESTRICTED, "only on a verified full-product request/receipt panel; canceled cells must not be silently treated as executed"),
        })
    elif key == "flatland":
        common.update({
            "execution_receipt": _entry(STATUS_UNVERIFIED, "current adapter records requests; Flatland movement_allowed/resolution needs explicit runtime instrumentation"),
            "honored_joint_support": _entry(STATUS_UNVERIFIED, "movement conflict resolution is not yet surfaced as a stable receipt"),
            "coupled_honored_support_observed": _entry(STATUS_UNVERIFIED, "requires explicit movement-resolution probe"),
            "full_cartesian_testable": _entry(STATUS_RESTRICTED, "state-valid per-agent actions are topology-dependent"),
            "mixed_difference_testable": _entry(STATUS_UNVERIFIED, "requires trusted joint execution receipts"),
        })
    elif key == "cyborg":
        common.update({
            "execution_receipt": _entry(STATUS_RESTRICTED, "adapter records submitted actions after per-agent validation, not environment-side causal execution semantics"),
            "honored_joint_support": _entry(STATUS_RESTRICTED, "submitted action tuples can be recorded; no coupled feasibility contract"),
            "coupled_honored_support_observed": _entry(STATUS_NOT, "no coupled command feasibility exposed"),
            "full_cartesian_testable": _entry(STATUS_RESTRICTED, "heterogeneous finite action spaces are enumerable per agent"),
            "mixed_difference_testable": _entry(STATUS_UNVERIFIED, "needs claim-specific outcome/receipt validation"),
            "reference_kernel_observable": _entry(STATUS_RESTRICTED, "policy/co-action trajectories can estimate a kernel, but the current adapter does not provide the estimator"),
            "agent_removal": _entry(STATUS_RESTRICTED, "counterfactual noop/randomization can be defined, but literal removal semantics require a scenario contract"),
        })
    else:  # cityflow
        common.update({
            "execution_receipt": _entry(STATUS_SUPPORTED, "set_tl_phase commands are applied explicitly before next_step"),
            "honored_joint_support": _entry(STATUS_SUPPORTED, "submitted valid phase tuple is the applied command tuple"),
            "coupled_honored_support_observed": _entry(STATUS_NOT, "intersections are commanded independently in the current scenario"),
            "full_cartesian_testable": _entry(STATUS_SUPPORTED, "finite phase products are enumerable for selected intersections"),
            "mixed_difference_testable": _entry(STATUS_SUPPORTED, "clone/restore plus applied phase receipts permit finite response tables"),
            "reference_kernel_observable": _entry(STATUS_RESTRICTED, "trajectory co-action frequencies can estimate a kernel; estimator is external to adapter"),
        })
    return common


def _mask_actions(env, agent: int) -> tuple[int, ...]:
    mask = np.asarray(env.valid_action_mask(int(agent)), dtype=bool).reshape(-1)
    if mask.size == 0 or not np.any(mask):
        raise RuntimeError(f"agent {agent} has no valid action")
    return tuple(int(a) for a in np.flatnonzero(mask))


def probe_execution_and_support(env, *, agents: Sequence[int] | None = None, max_cells: int = 256) -> dict:
    """Enumerate a bounded request panel and compare requested vs receipt tuples.

    The function restores the same snapshot before every request.  It never
    infers execution from state change; a receipt must be exposed by the adapter.
    """
    if agents is None:
        agents = tuple(range(min(2, int(env.n_agents))))
    agents = tuple(int(a) for a in agents)
    if not agents:
        raise ValueError("at least one audited agent is required")
    snapshot = env.clone_state()
    baseline = [int(env.fixed_continuation_policy(i)) for i in range(int(env.n_agents))]
    action_sets = [_mask_actions(env, a) for a in agents]
    requested_cells = list(itertools.product(*action_sets))
    if len(requested_cells) > int(max_cells):
        requested_cells = requested_cells[: int(max_cells)]
    rows = []
    try:
        for cell in requested_cells:
            env.restore_state(snapshot)
            joint = list(baseline)
            for agent, action in zip(agents, cell):
                joint[agent] = int(action)
            env.step(joint)
            receipt = getattr(env, "last_executed_actions", None)
            if receipt is None:
                receipt = getattr(env, "last_actions", None)
            if receipt is None or len(receipt) < int(env.n_agents):
                rows.append({"requested": list(cell), "receipt": None, "verified": False, "fully_honored": None})
                continue
            observed = tuple(int(receipt[a]) for a in agents)
            rows.append({"requested": list(cell), "receipt": list(observed), "verified": True, "fully_honored": bool(observed == tuple(cell))})
    finally:
        env.restore_state(snapshot)
    verified = [r for r in rows if r["verified"]]
    honored = [r for r in verified if r["fully_honored"]]
    request_count = len(rows)
    request_product = int(np.prod([len(x) for x in action_sets]))
    honored_tuples = {tuple(r["requested"]) for r in honored}
    return {
        "agents": list(agents),
        "action_sets": [list(x) for x in action_sets],
        "request_product_size": request_product,
        "cells_probed": request_count,
        "receipts_verified": len(verified),
        "fully_honored_cells": len(honored),
        "authority_rate": float(len(honored) / len(verified)) if verified else None,
        "all_receipts_verified": bool(len(verified) == request_count),
        "all_probed_honored": bool(len(honored) == request_count) if request_count else False,
        "coupled_honored_support_observed": bool(len(honored_tuples) < request_count and len(verified) == request_count),
        "rows": rows,
    }


def claim_readiness(capabilities: Mapping[str, CapabilityEntry], runtime: Mapping[str, Any] | None = None) -> dict:
    def at_least(key: str, allowed=(STATUS_SUPPORTED, STATUS_RESTRICTED)) -> bool:
        return capabilities[key].status in allowed
    runtime = runtime or {}
    receipt_ok = bool(runtime.get("all_receipts_verified", False)) or capabilities["execution_receipt"].status == STATUS_SUPPORTED
    coupled = bool(runtime.get("coupled_honored_support_observed", False))
    return {
        "MASTER_support": {
            "ready": bool(receipt_ok and coupled),
            "reason": "requires a verified non-Cartesian honored/executable support; request support alone is insufficient",
        },
        "MASTER_reference": {
            "ready": bool(capabilities["reference_kernel_observable"].status == STATUS_SUPPORTED and capabilities["clone_restore"].status == STATUS_SUPPORTED),
            "reason": "requires trajectory/co-action kernel estimation plus intervention response",
        },
        "FUNCTIONAL": {
            "ready": bool(at_least("clone_restore") and at_least("valid_action_mask")),
            "reason": "finite intervention panels and explicit masks available",
        },
        "D6": {
            "ready": bool(at_least("full_cartesian_testable") and at_least("mixed_difference_testable") and receipt_ok),
            "reason": "requires verified full-product response table and execution authority",
        },
        "QUERY": {
            "ready": bool(at_least("clone_restore")),
            "reason": "core response/removal primitives possible; unsupported query types remain NA",
        },
        "DYNAMIC": {
            "ready": bool(capabilities["learned_policy_hook"].status == STATUS_SUPPORTED and capabilities["clone_restore"].status == STATUS_SUPPORTED),
            "reason": "only restricted until a claim-specific learned-policy update hook is exercised",
        },
    }


def audit_environment(key: str, env=None, *, agents: Sequence[int] | None = None, max_cells: int = 256) -> dict:
    profile = static_capability_profile(key)
    runtime = None
    if env is not None:
        try:
            runtime = probe_execution_and_support(env, agents=agents, max_cells=max_cells)
        except Exception as exc:  # audit output is explicit, never silently promoted
            runtime = {"error": f"{type(exc).__name__}: {exc}", "all_receipts_verified": False, "coupled_honored_support_observed": False}
    return {
        "adapter": str(key).lower(),
        "capabilities": {k: profile[k].payload() for k in CAPABILITY_KEYS},
        "runtime_probe": runtime,
        "claim_readiness": claim_readiness(profile, runtime),
        "semantic_warning": "requestable command support and resolved/honored support are different objects; never relabel post-conflict cancellation as pre-execution infeasibility",
    }
