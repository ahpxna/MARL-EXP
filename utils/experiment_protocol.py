"""Confirmatory experiment summaries and fail-closed protocol validation."""
from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Iterable, Sequence

import numpy as np
from scipy import stats


@dataclass(frozen=True)
class ConfirmatoryProtocol:
    seeds: tuple[int, ...]
    confidence: float = 0.95
    failed_run_policy: str = "FAIL_CLOSED_REPORT_ALL"
    primary_metric: str = ""
    secondary_metrics: tuple[str, ...] = ()
    false_safe_required: bool = False

    def __post_init__(self) -> None:
        if len(self.seeds) == 0:
            raise ValueError("confirmatory protocol must freeze at least one seed")
        if len(set(self.seeds)) != len(self.seeds):
            raise ValueError("confirmatory seeds must be unique")
        if not (0.0 < float(self.confidence) < 1.0):
            raise ValueError("confidence must lie in (0,1)")
        if not str(self.failed_run_policy):
            raise ValueError("failed_run_policy must be explicit")


def summarize_replicates(values: Sequence[float], confidence: float = 0.95) -> dict:
    x = np.asarray(values, dtype=np.float64)
    if x.ndim != 1 or x.size == 0 or not np.all(np.isfinite(x)):
        raise ValueError("replicate values must be a non-empty finite vector")
    n = int(x.size)
    mean = float(np.mean(x))
    median = float(np.median(x))
    if n == 1:
        lo = hi = mean
    else:
        sem = float(stats.sem(x))
        q = float(stats.t.ppf((1.0 + float(confidence)) / 2.0, df=n - 1))
        lo, hi = mean - q * sem, mean + q * sem
    return {
        "n": n,
        "mean": mean,
        "median": median,
        "confidence": float(confidence),
        "ci_low": float(lo),
        "ci_high": float(hi),
        "std": float(np.std(x, ddof=1)) if n > 1 else 0.0,
    }


def false_safe_rate(certified_safe: Iterable[bool], actually_safe: Iterable[bool]) -> dict:
    cert = np.asarray(list(certified_safe), dtype=bool)
    truth = np.asarray(list(actually_safe), dtype=bool)
    if cert.shape != truth.shape or cert.ndim != 1 or cert.size == 0:
        raise ValueError("certificate/truth vectors must be aligned and non-empty")
    false_safe = cert & ~truth
    certified = int(np.sum(cert))
    return {
        "n": int(cert.size),
        "certified_safe": certified,
        "false_safe": int(np.sum(false_safe)),
        "false_safe_rate_all": float(np.mean(false_safe)),
        "false_safe_rate_conditional": float(np.sum(false_safe) / certified) if certified else 0.0,
    }
