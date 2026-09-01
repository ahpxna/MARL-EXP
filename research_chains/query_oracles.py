"""Typed construction of current external query utilities."""
from __future__ import annotations

import numpy as np

from .query_contracts import QUERY_SPECS


def primitive_query_utilities(primitive, *, noop_supported, shapley=None):
    queries = {
        "response_sensitivity": np.asarray(primitive["C_response_span"]),
        "signed_policy_effect": np.asarray(primitive["D_signed_policy_projection"]),
        "randomization_effect": np.asarray(primitive["RandomizedActionImportance"]),
    }
    if noop_supported:
        queries["noop_substitution_effect"] = np.asarray(primitive["DifferenceReward_noop"])
        queries["interventional_response_ate_vs_noop"] = np.asarray(primitive["InterventionalResponseATE_vs_noop"])
    if shapley is not None:
        queries["coalition_contribution"] = np.abs(np.asarray(shapley))
    return queries


def query_payload(query_id, utility):
    spec = QUERY_SPECS[query_id]
    return {"utility": np.asarray(utility).tolist(), "semantic_target": spec.semantic_target,
            "reference_semantics": dict(spec.reference_semantics),
            "required_capabilities": list(spec.required_capabilities), "evidence_class": spec.evidence_class}
