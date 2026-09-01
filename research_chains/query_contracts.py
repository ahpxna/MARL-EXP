"""Typed query/method/capability contracts for the external Query benchmark."""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Mapping, Protocol, Sequence


@dataclass(frozen=True)
class QuerySpec:
    query_id: str
    semantic_target: str
    required_capabilities: tuple[str, ...]
    reference_semantics: Mapping[str, str] = field(default_factory=dict)
    evidence_class: str = "EXTERNAL_INTERVENTIONAL_QUERY"


@dataclass(frozen=True)
class MethodSpec:
    method_id: str
    implementation_scope: str
    required_capabilities: tuple[str, ...]
    provenance: Mapping[str, str]
    information_budget_type: str
    tier: int
    derived_from: str | None = None
    transform: str | None = None
    legacy_aliases: tuple[str, ...] = ()


@dataclass(frozen=True)
class ProviderResult:
    values: Sequence[float]
    metadata: Mapping[str, Any]
    cost: Mapping[str, int]


class AttentionProvider(Protocol):
    def relation_attention(self, snapshot, outcome_agent: int, candidate_agents: Sequence[int]) -> ProviderResult: ...


class CommunicationInterventionProvider(Protocol):
    def deletion_effect(self, snapshot, outcome_agent: int, candidate_agents: Sequence[int]) -> ProviderResult: ...
    def delay_effect(self, snapshot, outcome_agent: int, candidate_agents: Sequence[int], lags: Sequence[int]) -> ProviderResult: ...


class InformationInterventionProvider(Protocol):
    def information_value(self, snapshot, outcome_agent: int, candidate_agents: Sequence[int]) -> ProviderResult: ...


class CausalContextProvider(Protocol):
    def causal_contribution(self, snapshot, outcome_agent: int, candidate_agents: Sequence[int]) -> ProviderResult: ...


@dataclass
class ExternalQueryContext:
    attention: AttentionProvider | None = None
    communication: CommunicationInterventionProvider | None = None
    information: InformationInterventionProvider | None = None
    causal: CausalContextProvider | None = None

    def capability_status(self) -> dict[str, bool]:
        return {
            "policy_attention_weights": self.attention is not None,
            "message_deletion_provider": self.communication is not None,
            "communication_delay_provider": self.communication is not None,
            "information_intervention_provider": self.information is not None,
            "causal_context_provider": self.causal is not None,
        }


BLOCKER_REASON = {
    "policy_attention_weights": "NO_ATTENTION_PROVIDER",
    "message_deletion_provider": "NO_MESSAGE_DELETION_PROVIDER",
    "communication_delay_provider": "NO_COMMUNICATION_DELAY_PROVIDER",
    "information_intervention_provider": "NO_INFORMATION_INTERVENTION_PROVIDER",
    "causal_context_provider": "NO_CAUSAL_CONTEXT_PROVIDER",
    "explicit_noop_semantics": "NO_EXPLICIT_NOOP_SEMANTICS",
    "complete_noop_coalition_table": "NO_COMPLETE_NOOP_COALITION_TABLE",
}


QUERY_SPECS = {
    "response_sensitivity": QuerySpec("response_sensitivity", "max_a Q_j(a)-min_a Q_j(a)",
        ("clone_restore", "valid_action_mask", "intervention_authority")),
    "signed_policy_effect": QuerySpec("signed_policy_effect", "E_pi[Q_j]-E_q[Q_j]",
        ("clone_restore", "trusted_execution_receipt", "current_policy_action"),
        {"pi": "deterministic_frozen_policy_at_snapshot", "q": "uniform_over_honored_actions",
         "formula": "Q(a_pi)-mean_a Q(a)"}),
    "randomization_effect": QuerySpec("randomization_effect", "|E_pi[Q_j]-E_q[Q_j]|",
        ("clone_restore", "trusted_execution_receipt", "current_policy_action"),
        {"pi": "deterministic_frozen_policy_at_snapshot", "q": "uniform_over_honored_actions"}),
    "noop_substitution_effect": QuerySpec("noop_substitution_effect", "|Q_j(a_pi)-Q_j(a_noop)|",
        ("explicit_noop_semantics",)),
    "interventional_response_ate_vs_noop": QuerySpec("interventional_response_ate_vs_noop",
        "|E_uniform Q_j-Q_j(a_noop)|", ("explicit_noop_semantics",),
        {"warning": "response-panel contrast; not a generic causal ATE"}),
    "coalition_contribution": QuerySpec("coalition_contribution", "absolute exact Shapley value of noop coalition table",
        ("complete_noop_coalition_table",)),
    "communication_deletion": QuerySpec("communication_deletion", "J_base-J_delete(sender->receiver)",
        ("message_deletion_provider",)),
    "communication_delay": QuerySpec("communication_delay", "f_lag(J_base-J_delay_lag)",
        ("communication_delay_provider",)),
    "information_value": QuerySpec("information_value", "J_information_available-J_information_absent",
        ("information_intervention_provider",)),
    "causal_contribution": QuerySpec("causal_contribution", "identified causal contribution under declared graph/context",
        ("causal_context_provider",), evidence_class="IDENTIFIED_CAUSAL_QUERY"),
}


METHOD_SPECS = {
    "C_response_span": MethodSpec("C_response_span", "native_cig", ("response_panel",),
        {"definition": "osc(Q)"}, "single_agent_intervention_cells", 0),
    "D_signed_policy_projection": MethodSpec("D_signed_policy_projection", "native_cig", ("response_panel",),
        {"definition": "Q(a_pi)-mean_honored(Q)"}, "single_agent_intervention_cells", 0),
    "DifferenceReward_noop": MethodSpec("DifferenceReward_noop", "faithful_intervention_primitive",
        ("explicit_noop_semantics",), {"definition": "absolute policy-vs-noop response contrast"}, "single_agent_intervention_cells", 1),
    "RandomizedActionImportance": MethodSpec("RandomizedActionImportance", "faithful_intervention_primitive",
        ("response_panel",), {"definition": "absolute deterministic-policy-vs-uniform contrast"},
        "single_agent_intervention_cells", 1, "D_signed_policy_projection", "absolute_value"),
    "InterventionalResponseATE_vs_noop": MethodSpec("InterventionalResponseATE_vs_noop", "faithful_intervention_primitive",
        ("explicit_noop_semantics",), {"definition": "uniform response mean versus noop; not generic causal ATE"},
        "single_agent_intervention_cells", 1, legacy_aliases=("InterventionalATE_vs_noop",)),
    "CoalitionShapley_noop": MethodSpec("CoalitionShapley_noop", "faithful_intervention_primitive",
        ("complete_noop_coalition_table",), {"definition": "exact Shapley on noop coalition value table"},
        "coalition_interventions", 1),
    "RelationFeatureNorm": MethodSpec("RelationFeatureNorm", "noncausal_model_baseline", ("relation_features",),
        {"definition": "L2 norm of adapter relation features"}, "model_forward_passes", 2),
    "AttentionWeights": MethodSpec("AttentionWeights", "model_explanation", ("policy_attention_weights",),
        {"required_metadata": "checkpoint_sha,layer,head_reduction,relation_mapping,normalization"}, "model_forward_passes", 2),
    "MessageDeletion": MethodSpec("MessageDeletion", "communication_intervention", ("message_deletion_provider",),
        {"definition": "provider-declared same-state message deletion"}, "message_interventions", 3),
    "CommunicationDelay": MethodSpec("CommunicationDelay", "communication_intervention", ("communication_delay_provider",),
        {"definition": "provider-declared lag intervention"}, "message_interventions", 3),
    "VoI": MethodSpec("VoI", "information_intervention", ("information_intervention_provider",),
        {"definition": "provider-declared information available-vs-absent target"}, "oracle_calls", 3),
    "CausalContextAttribution": MethodSpec("CausalContextAttribution", "causal_context_attribution", ("causal_context_provider",),
        {"definition": "faithful provider with graph/intervention/context distribution"}, "oracle_calls", 4),
}

LEGACY_METHOD_ALIASES = {alias: method_id for method_id, spec in METHOD_SPECS.items() for alias in spec.legacy_aliases}


def missing_capabilities(required, available):
    return tuple(x for x in required if not available.get(x, False))
