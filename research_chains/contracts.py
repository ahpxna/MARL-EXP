"""Typed semantic contracts shared by all new CIG-AMF research chains."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum
import hashlib
import json


class RelationTargetKind(str, Enum):
    """The scientific object a pairwise intervention is intended to target."""

    PRIMITIVE_ISOLATED = "primitive_isolated"
    FEASIBLE_KAPPA_RESPONSE = "feasible_kappa_response"
    PRODUCT_SURROGATE = "product_surrogate"


class HistoryTargetKind(str, Enum):
    """Which history law is used to standardize a response surface."""

    NATURAL = "natural_history"
    FROZEN_STANDARDIZED = "frozen_standardized"
    TRANSPORTED = "transported"


class CertificateLevel(str, Enum):
    """Do not silently promote oracle/diagnostic quantities to certificates."""

    ORACLE_EXACT = "oracle_exact"
    DETERMINISTIC_BOUND = "deterministic_bound"
    HIGH_PROBABILITY_BOUND = "high_probability_bound"
    ESTIMATED_DIAGNOSTIC = "estimated_diagnostic"
    UNAVAILABLE = "unavailable"


@dataclass(frozen=True)
class TypedEstimandKey:
    """Minimal key that prevents semantic reuse across incompatible targets."""

    ego_id: str
    source_id: str
    horizon: int
    continuation_key: str
    history_target: HistoryTargetKind
    relation_target: RelationTargetKind
    reference_key: str
    support_key: str
    policy_version: str
    response_version: str = "response_v1"
    schema_version: int = 1

    def __post_init__(self) -> None:
        if type(self.horizon) is not int or self.horizon <= 0:
            raise ValueError("horizon must be a positive exact integer")
        for name in (
            "ego_id", "source_id", "continuation_key", "reference_key",
            "support_key", "policy_version", "response_version",
        ):
            if not str(getattr(self, name)).strip():
                raise ValueError(f"{name} must be non-empty")
        if not isinstance(self.history_target, HistoryTargetKind):
            raise TypeError("history_target must be HistoryTargetKind")
        if not isinstance(self.relation_target, RelationTargetKind):
            raise TypeError("relation_target must be RelationTargetKind")
        if self.schema_version != 1:
            raise ValueError("unsupported TypedEstimandKey schema")

    def fingerprint(self) -> str:
        payload = asdict(self)
        payload["history_target"] = self.history_target.value
        payload["relation_target"] = self.relation_target.value
        raw = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        return hashlib.sha256(raw).hexdigest()


def require_natural_aipw_target(history_target: HistoryTargetKind) -> None:
    """Fail closed for the existing conditional AIPW implementation.

    The historical estimator regresses E[phi | X], so it targets the natural
    conditional law P(W|X).  Arbitrary frozen/transported standardization needs
    an explicit standardization/transport stage and must not reuse that code
    path silently.
    """

    if history_target is not HistoryTargetKind.NATURAL:
        raise ValueError(
            "conditional AIPW currently targets the natural history law P(W|X); "
            "frozen/transported nu* requires explicit standardization or transport"
        )
