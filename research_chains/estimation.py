"""History-standardization helpers that keep nu* semantics explicit."""
from __future__ import annotations
import numpy as np
from .contracts import HistoryTargetKind


def standardize_response_bank(mu_by_history_action, weights):
    """Compute Q^nu(a)=sum_w nu(w) mu(w,a) for a finite frozen bank."""
    mu=np.asarray(mu_by_history_action,dtype=np.float64); w=np.asarray(weights,dtype=np.float64)
    if mu.ndim!=2 or w.shape!=(mu.shape[0],) or np.any(w<0.0) or not np.all(np.isfinite(mu)) or not np.all(np.isfinite(w)):
        raise ValueError("mu must be [history,action] finite and weights a non-negative history vector")
    if not np.isclose(w.sum(),1.0,rtol=1e-8,atol=1e-10):
        raise ValueError("standardization weights must sum to one")
    return np.asarray(w @ mu,dtype=np.float64)


def validate_estimator_target(history_target: HistoryTargetKind, *, transported_weight_available: bool = False):
    if history_target is HistoryTargetKind.NATURAL:
        return "conditional_aipw_or_direct_standardization"
    if history_target is HistoryTargetKind.FROZEN_STANDARDIZED:
        return "direct_history_level_mu_then_frozen_standardization"
    if history_target is HistoryTargetKind.TRANSPORTED:
        if not transported_weight_available:
            raise ValueError("transported target requires an explicit transport/distribution-ratio correction")
        return "transported_estimation"
    raise TypeError("unsupported history target")
