"""CIG-native and response-panel intervention primitives."""
from __future__ import annotations
from typing import Sequence
import numpy as np


def response_primitives(response_rows: Sequence[Sequence[float]], baseline_indices: Sequence[int], noop_indices: Sequence[int] | None=None):
    rows=[np.asarray(r,float) for r in response_rows]; baseline_indices=list(map(int,baseline_indices)); noop_indices=None if noop_indices is None else list(map(int,noop_indices))
    capacity=[];direction=[];noop_effect=[];randomized=[];ate=[]
    for idx,(row,baseline_index) in enumerate(zip(rows,baseline_indices)):
        mean=float(np.mean(row)); base=float(row[baseline_index])
        capacity.append(float(np.ptp(row))); direction.append(base-mean); randomized.append(abs(base-mean))
        if noop_indices is not None:
            noop=float(row[noop_indices[idx]]); noop_effect.append(abs(base-noop)); ate.append(abs(mean-noop))
    result={'C_response_span':np.asarray(capacity),'D_signed_policy_projection':np.asarray(direction),
            'RandomizedActionImportance':np.asarray(randomized)}
    if noop_indices is not None:
        result['DifferenceReward_noop']=np.asarray(noop_effect)
        result['InterventionalResponseATE_vs_noop']=np.asarray(ate)
    return result
