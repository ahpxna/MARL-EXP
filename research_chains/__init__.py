"""Typed research harness for the post-Round-10 CIG-AMF equation chains.

This package is deliberately independent of the historical Paper-A/Paper-B
validators.  It provides finite-world, falsification, certificate, reference,
functional, support-uncertainty and provenance primitives shared by the new
chains.
"""

from .contracts import (
    CertificateLevel,
    HistoryTargetKind,
    RelationTargetKind,
    TypedEstimandKey,
)
from .support import SupportModel, SupportBracket
from .finite_world import FiniteResponseWorld

__all__ = [
    "CertificateLevel",
    "HistoryTargetKind",
    "RelationTargetKind",
    "TypedEstimandKey",
    "SupportModel",
    "SupportBracket",
    "FiniteResponseWorld",
]
