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

from research_chains.oracle import trusted_execution_receipt

STATUS_SUPPORTED = "SUPPORTED"
STATUS_RESTRICTED = "SUPPORTED_WITH_RESTRICTIONS"
STATUS_NOT = "NOT_SUPPORTED"
STATUS_UNVERIFIED = "UNVERIFIED"
VALID_STATUSES = {STATUS_SUPPORTED, STATUS_RESTRICTED, STATUS_NOT, STATUS_UNVERIFIED}

CAPABILITY_KEYS = (
    "clone_restore",
    "valid_action_mask",
    "per_agent_valid_mask",
    "execution_receipt",
    "executed_action_receipt",
    "intervention_authority",
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
        "per_agent_valid_mask": _entry(STATUS_SUPPORTED, "alias of the explicit per-agent valid-action mask contract"),
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
            "executed_action_receipt": _entry(STATUS_SUPPORTED, "trusted receipt exposes the action actually applied"),
            "intervention_authority": _entry(STATUS_SUPPORTED, "requested Omni actions are checked against a trusted executed-action receipt"),
            "honored_joint_support": _entry(STATUS_SUPPORTED, "executed command tuples can be enumerated from clone states"),
            "coupled_honored_support_observed": _entry(STATUS_NOT, "Omni command support is intentionally Cartesian"),
            "full_cartesian_testable": _entry(STATUS_SUPPORTED, "full finite command alphabet is enumerable"),
            "mixed_difference_testable": _entry(STATUS_SUPPORTED, "clone-state full product response tables can be built"),
        })
    elif key == "rware":
        common.update({
            "execution_receipt": _entry(STATUS_UNVERIFIED, "runtime probe must confirm post-resolution req_action telemetry"),
            "executed_action_receipt": _entry(STATUS_UNVERIFIED, "runtime must verify post-resolution actions against requests"),
            "intervention_authority": _entry(STATUS_UNVERIFIED, "requires a runtime match between requested and post-resolution executed actions"),
            "honored_joint_support": _entry(STATUS_UNVERIFIED, "RWARE can cancel conflicting movement requests; resolved tuples must be probed"),
            "coupled_honored_support_observed": _entry(STATUS_UNVERIFIED, "requires runtime enumeration of resolved joint actions"),
            "full_cartesian_testable": _entry(STATUS_RESTRICTED, "requestable tuples are enumerable, but resolved support may be coupled"),
            "mixed_difference_testable": _entry(STATUS_RESTRICTED, "only on a verified full-product request/receipt panel; canceled cells must not be silently treated as executed"),
        })
    elif key == "flatland":
        common.update({
            "execution_receipt": _entry(STATUS_UNVERIFIED, "current adapter records requests; Flatland movement_allowed/resolution needs explicit runtime instrumentation"),
            "executed_action_receipt": _entry(STATUS_UNVERIFIED, "no trusted post-motion action receipt is exposed"),
            "intervention_authority": _entry(STATUS_UNVERIFIED, "submitted train actions are not yet a trusted post-resolution receipt"),
            "honored_joint_support": _entry(STATUS_UNVERIFIED, "movement conflict resolution is not yet surfaced as a stable receipt"),
            "coupled_honored_support_observed": _entry(STATUS_UNVERIFIED, "requires explicit movement-resolution probe"),
            "full_cartesian_testable": _entry(STATUS_RESTRICTED, "state-valid per-agent actions are topology-dependent"),
            "mixed_difference_testable": _entry(STATUS_UNVERIFIED, "requires trusted joint execution receipts"),
        })
    elif key == "cyborg":
        common.update({
            "execution_receipt": _entry(STATUS_RESTRICTED, "adapter records submitted actions after per-agent validation, not environment-side causal execution semantics"),
            "executed_action_receipt": _entry(STATUS_UNVERIFIED, "submitted actions are not an executed-action receipt"),
            "intervention_authority": _entry(STATUS_UNVERIFIED, "submitted-action telemetry is insufficient to certify environment-side execution"),
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
            "executed_action_receipt": _entry(STATUS_SUPPORTED, "trusted receipt exposes applied traffic-light phases"),
            "intervention_authority": _entry(STATUS_SUPPORTED, "valid phase commands are applied explicitly and exposed through the trusted receipt"),
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
            try:
                receipt = trusted_execution_receipt(env)
            except RuntimeError:
                rows.append({"requested": list(cell), "receipt": None, "verified": False, "fully_honored": None})
                continue
            if isinstance(receipt, Mapping):
                if any(a not in receipt for a in range(int(env.n_agents))):
                    rows.append({"requested": list(cell), "receipt": None, "verified": False, "fully_honored": None})
                    continue
                observed = tuple(int(receipt[a]) for a in agents)
            else:
                if len(receipt) < int(env.n_agents):
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
    projections = [
        {cell[j] for cell in honored_tuples} for j in range(len(agents))
    ] if honored_tuples else [set() for _ in agents]
    rejected_inside_honored_product = [
        tuple(r["requested"])
        for r in verified
        if not r["fully_honored"]
        and all(int(r["requested"][j]) in projections[j] for j in range(len(agents)))
    ]
    panel_complete = bool(request_count == request_product)
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
        "panel_complete": panel_complete,
        "panel_truncated": bool(not panel_complete),
        "coupling_witnesses": [list(cell) for cell in rejected_inside_honored_product],
        "coupled_honored_support_observed": bool(rejected_inside_honored_product),
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
            "ready": bool(capabilities["joint_feasibility_oracle"].status == STATUS_SUPPORTED),
            "reason": "requires a pre-execution joint command-feasibility oracle; post-execution cancellation/honoring is diagnostic only",
        },
        "MASTER_honored_support_diagnostic": {
            "ready": bool(receipt_ok and coupled),
            "reason": "post-resolution honored support may diagnose interaction but is not relabeled as pre-execution feasible support",
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
            "ready": bool(at_least("clone_restore") and receipt_ok and at_least("intervention_authority")),
            "reason": "core response queries require clone/restore plus a trusted executed-action receipt; unsupported query types remain NA",
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
    layered = {
        "EnvironmentCapabilities": {k: profile[k].payload() for k in (
            "clone_restore", "valid_action_mask", "execution_receipt", "intervention_authority",
            "joint_feasibility_oracle", "full_cartesian_testable", "reference_kernel_observable")},
        "PolicyCapabilities": {
            "learned_policy_hook": profile["learned_policy_hook"].payload(),
            "policy_attention_weights": _entry(STATUS_UNVERIFIED,
                "attention is a policy/checkpoint property, not an environment-adapter property").payload(),
        },
        "CommunicationCapabilities": {
            "message_deletion": profile["message_deletion"].payload(),
            "communication_delay": profile["communication_delay"].payload(),
        },
        "CausalContextCapabilities": {
            "information_intervention": _entry(STATUS_UNVERIFIED,
                "requires an explicit information object and available-vs-absent intervention contract").payload(),
            "causal_context": _entry(STATUS_UNVERIFIED,
                "requires graph, identification assumptions, interventions, and context distribution").payload(),
        },
    }
    return {
        "adapter": str(key).lower(),
        "capabilities": {k: profile[k].payload() for k in CAPABILITY_KEYS},
        "runtime_probe": runtime,
        "claim_readiness": claim_readiness(profile, runtime),
        "query_capability_layers": layered,
        "semantic_warning": "requestable command support and resolved/honored support are different objects; never relabel post-conflict cancellation as pre-execution infeasibility",
    }
