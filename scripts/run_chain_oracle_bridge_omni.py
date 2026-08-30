"""OmniArena clone-state intervention/support audit for R/D/B/H.

This runner does not modify OmniArena dynamics.  It audits the intervention
boundary around one cloned state and keeps four support objects distinct:

* Omega_nominal: full action-alphabet product;
* Omega_valid: state-valid commands according to the environment adapter;
* Omega_requestable: valid commands submitted through the clone-state oracle;
* Omega_honored: requests whose source-agent commands are recorded as executed.

For OmniArena, ``last_actions`` records accepted action commands. A command can
be honored even when grid physics blocks its positional effect.  The runner
therefore does not infer support coupling from a no-movement outcome.
"""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import argparse
import hashlib
import json
import pickle
from pathlib import Path

import numpy as np

from envs.omni_arena import OmniArena
from envs.causal_adapter import resolve_env_adapter
from research_chains.oracle import CloneStateJointOracle
from research_chains.provenance import atomic_json

PROTOCOL_VERSION = "chain_oracle_bridge_omni_v3"


def _cells(rows):
    return [list(map(int, row)) for row in sorted(rows)]


def _support_hash(rows):
    payload = json.dumps(_cells(rows), separators=(",", ":"), sort_keys=False).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def run(seed=0):
    env = OmniArena(
        n_agents=8,
        n_zones=1,
        max_steps=64,
        phase_length=1000,
        enable_structural_shift=False,
        seed=int(seed),
    )
    env.reset()
    snapshot = env.clone_state()
    adapter = resolve_env_adapter(env)
    baseline = [int(env.scripted_policy(a)) for a in range(env.n_agents)]
    roles = env.zone_role_agents[0]
    outcome = int(roles[env.ROLE_COLLECTOR])
    candidates = [int(a) for a in roles.values() if int(a) != outcome]
    if len(candidates) < 2:
        candidates = [a for a in range(env.n_agents) if a != outcome]
    sources = tuple(candidates[:2])
    action_dim = int(env.get_action_dim())

    # 1) Nominal support: every syntactically representable action pair.
    omega_nominal = {
        (int(a0), int(a1))
        for a0 in range(action_dim)
        for a1 in range(action_dim)
    }

    # 2) State-valid support: action-mask product.  For OmniArena this is the
    # command-level legality mask, not a promise that movement changes state.
    action_sets = []
    valid_masks = []
    for source in sources:
        mask = np.asarray(adapter.valid_action_mask(source), dtype=bool).reshape(-1)
        if mask.shape != (action_dim,) or not np.any(mask):
            raise RuntimeError(f"invalid/empty valid-action mask for source={source}")
        valid_masks.append(mask)
        action_sets.append([int(a) for a in np.flatnonzero(mask)])
    omega_valid = {
        (int(a0), int(a1))
        for a0 in action_sets[0]
        for a1 in action_sets[1]
    }

    oracle = CloneStateJointOracle(
        env,
        snapshot=snapshot,
        outcome_agent=outcome,
        baseline_actions=baseline,
    )

    # 3) Requestable support: this bridge attempts every state-valid pair.
    # Keep it explicit rather than silently equating it with Omega_valid.
    omega_requestable = set(omega_valid)
    records = oracle.enumerate(sources, action_sets)

    # Single-source checks help distinguish a pair-specific incompatibility
    # candidate from an action that the interface fails to honor even alone.
    individual_honor = []
    individual_records = []
    for source, source_actions in zip(sources, action_sets):
        status = {}
        rows = []
        for action in source_actions:
            rec = oracle.evaluate((source,), (action,))
            status[int(action)] = bool(rec.execution_verified)
            rows.append({
                "action": int(action),
                "honored": bool(rec.execution_verified),
                "requested_action": int(rec.requested_joint_actions[source]),
                "executed_action": int(rec.executed_joint_actions[source]),
            })
        individual_honor.append(status)
        individual_records.append(rows)

    omega_honored = {
        tuple(r.assignment) for r in records if r.execution_verified
    }
    table = {
        tuple(r.assignment): float(r.reward)
        for r in records
        if r.execution_verified
    }

    mismatch_records = []
    jointly_incompatible_candidates = []
    valid_but_not_honored = []
    for record in records:
        if record.execution_verified:
            continue
        assignment = tuple(int(x) for x in record.assignment)
        row = {
            "assignment": list(assignment),
            "requested_source_actions": [
                int(record.requested_joint_actions[s]) for s in sources
            ],
            "executed_source_actions": [
                int(record.executed_joint_actions[s]) for s in sources
            ],
            "individually_honored": [
                bool(individual_honor[idx].get(int(action), False))
                for idx, action in enumerate(assignment)
            ],
        }
        if all(row["individually_honored"]):
            row["classification"] = "jointly_incompatible_candidate"
            jointly_incompatible_candidates.append(assignment)
        else:
            row["classification"] = "valid_but_not_honored"
            valid_but_not_honored.append(assignment)
        mismatch_records.append(row)

    # Nominal-but-invalid requests are never submitted to the environment.
    invalid_request_cells = omega_nominal - omega_valid

    proj0 = {a0 for a0, _ in omega_honored}
    proj1 = {a1 for _, a1 in omega_honored}
    projected_product = {(a0, a1) for a0 in proj0 for a1 in proj1}
    missing_projected_cross_cells = projected_product - omega_honored

    full_valid_alphabet_coverage = bool(omega_honored == omega_valid)
    projected_support_rectangular = bool(
        omega_honored and omega_honored == projected_product
    )
    intervention_authority_rate = (
        float(len(omega_honored)) / float(len(omega_requestable))
        if omega_requestable else 0.0
    )

    individual_authority = []
    for source, source_actions, status in zip(sources, action_sets, individual_honor):
        honored = sum(bool(status[int(a)]) for a in source_actions)
        individual_authority.append({
            "source": int(source),
            "valid_action_count": int(len(source_actions)),
            "honored_action_count": int(honored),
            "authority_rate": float(honored / max(1, len(source_actions))),
        })

    q0 = []
    q1 = []
    for a0 in action_sets[0]:
        vals = [table[(a0, a1)] for a1 in action_sets[1] if (a0, a1) in table]
        q0.append(float(np.mean(vals)) if vals else None)
    for a1 in action_sets[1]:
        vals = [table[(a0, a1)] for a0 in action_sets[0] if (a0, a1) in table]
        q1.append(float(np.mean(vals)) if vals else None)

    surrogate_residual = None
    if full_valid_alphabet_coverage:
        matrix = np.asarray(
            [[table[(a0, a1)] for a1 in action_sets[1]] for a0 in action_sets[0]],
            dtype=float,
        )
        row = matrix.mean(axis=1)
        col = matrix.mean(axis=0)
        grand = float(matrix.mean())
        surrogate = row[:, None] + col[None, :] - grand
        surrogate_residual = float(np.max(np.abs(matrix - surrogate)))

    restored_hash = hashlib.sha256(
        pickle.dumps(env.clone_state(), protocol=4)
    ).hexdigest()
    snapshot_hash = hashlib.sha256(
        pickle.dumps(snapshot, protocol=4)
    ).hexdigest()

    support_objects = {
        "omega_nominal": {
            "semantic": "full_action_alphabet_product",
            "size": int(len(omega_nominal)),
            "sha256": _support_hash(omega_nominal),
            "cells": _cells(omega_nominal),
        },
        "omega_valid": {
            "semantic": "state_valid_command_mask_product",
            "size": int(len(omega_valid)),
            "sha256": _support_hash(omega_valid),
            "cells": _cells(omega_valid),
        },
        "omega_requestable": {
            "semantic": "valid_pairs_submitted_by_clone_state_oracle",
            "size": int(len(omega_requestable)),
            "sha256": _support_hash(omega_requestable),
            "cells": _cells(omega_requestable),
        },
        "omega_honored": {
            "semantic": "requested_source_commands_recorded_as_executed",
            "size": int(len(omega_honored)),
            "sha256": _support_hash(omega_honored),
            "cells": _cells(omega_honored),
        },
    }

    return {
        "protocol_version": PROTOCOL_VERSION,
        "development_only": True,
        "evidence_class": "CLONE_STATE_ORACLE_SUPPORT_AUDIT_ONLY",
        "seed": int(seed),
        "sources": list(sources),
        "outcome_agent": outcome,
        "action_dim": action_dim,
        "action_execution_semantics": (
            "command_honored_via_env.last_actions; an honored movement command may "
            "still have no positional effect because of OmniArena grid physics"
        ),
        "valid_actions_source_0": action_sets[0],
        "valid_actions_source_1": action_sets[1],
        "support_objects": support_objects,
        "nominal_cells": int(len(omega_nominal)),
        "invalid_request_count": int(len(invalid_request_cells)),
        "invalid_request_cells": _cells(invalid_request_cells),
        "requested_valid_cells": int(len(omega_requestable)),
        "requested_cells": int(len(omega_requestable)),  # compatibility alias
        "verified_executed_cells": int(len(omega_honored)),
        "executed_support_cells": int(len(omega_honored)),  # compatibility alias
        "request_mismatch_count": int(len(mismatch_records)),
        "request_mismatches": mismatch_records[:50],
        "valid_but_not_honored_count": int(len(valid_but_not_honored)),
        "jointly_incompatible_candidate_count": int(len(jointly_incompatible_candidates)),
        "jointly_incompatible_candidate_cells": _cells(jointly_incompatible_candidates),
        "individual_action_audit": individual_records,
        "individual_intervention_authority": individual_authority,
        "intervention_authority_rate": float(intervention_authority_rate),
        "full_valid_alphabet_coverage": full_valid_alphabet_coverage,
        "projected_support_rectangular": projected_support_rectangular,
        "rectangular_executed_support": projected_support_rectangular,  # compatibility alias
        "projected_support_size": int(len(projected_product)),
        "missing_projected_cross_cells": _cells(missing_projected_cross_cells),
        "joint_coupling_missing_cell_count": int(len(missing_projected_cross_cells)),
        "pairwise_product_reference_Q0": q0,
        "pairwise_product_reference_Q1": q1,
        "product_surrogate_sup_residual": surrogate_residual,
        "state_restored_after_oracle": bool(restored_hash == snapshot_hash),
        "scientific_scope": {
            "intervention_authority_audit": True,
            "command_level_cartesian_support_audit": True,
            "local_pairwise_product_reference_response": bool(full_valid_alphabet_coverage),
            "coupled_support_MASTER_evidence": False,
            "reference_kernel_identification_evidence": False,
            "learned_policy_F3_evidence": False,
            "reason_not_coupled_support": "OmniArena valid_action_mask is the full command alphabet; collision/no-movement is an outcome, not missing action support",
            "reason_not_reference_identification": "other agents are frozen to scripted baseline and selected source cells are enumerated; no conditional co-action kernel is estimated",
            "reason_not_F3": "one-step frozen scripted-coagent clone-state audit does not measure a learned CIG-AMF policy under endogenous drift",
        },
        "limitation": (
            "One cloned state, frozen scripted co-agents, H=1. Support is defined "
            "at the action-command interface. OmniArena can honor a movement "
            "command even when collision/grid physics prevents displacement. "
            "A non-honored pair is called a jointly-incompatible *candidate* only "
            "when each constituent action is honored in a single-source audit."
        ),
    }


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--seed", type=int, default=0)
    p.add_argument(
        "--out",
        default="research/new_chains_v2/oracle_bridge_omni/summary.json",
    )
    a = p.parse_args(argv)
    payload = run(a.seed)
    atomic_json(Path(a.out), payload)
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
