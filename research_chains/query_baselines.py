"""Primitive external-query baselines with explicit implementation scope.

These are not branded reimplementations of entire published algorithms.  Each
method is named by the mathematical/interventional primitive it actually uses.
"""
from __future__ import annotations
import itertools, math
from typing import Mapping, Sequence
import numpy as np

METHOD_SCOPE={
    'C_response_span':'native_cig',
    'D_signed_policy_projection':'native_cig',
    'DifferenceReward_noop':'faithful_primitive',
    'RandomizedActionImportance':'faithful_primitive',
    'InterventionalATE_vs_noop':'faithful_primitive',
    'CoalitionShapley_noop':'faithful_primitive',
    'RelationFeatureNorm':'noncausal_baseline',
    'MessageDeletion':'blocked_without_adapter_capability',
    'CommunicationDelay':'blocked_without_adapter_capability',
    'VoI':'blocked_without_adapter_capability',
}


def response_primitives(response_rows: Sequence[Sequence[float]], baseline_indices: Sequence[int], noop_indices: Sequence[int] | None=None):
    rows=[np.asarray(r,float) for r in response_rows]; baseline_indices=list(map(int,baseline_indices)); noop_indices=baseline_indices if noop_indices is None else list(map(int,noop_indices))
    C=[];D=[];rem=[];rand=[];ate=[]
    for r,b,n in zip(rows,baseline_indices,noop_indices):
        mean=float(np.mean(r)); base=float(r[b]); noop=float(r[n])
        C.append(float(np.ptp(r))); D.append(base-mean); rem.append(abs(base-noop)); rand.append(abs(base-mean)); ate.append(abs(mean-noop))
    return {
        'C_response_span':np.asarray(C),
        'D_signed_policy_projection':np.asarray(D),
        'DifferenceReward_noop':np.asarray(rem),
        'RandomizedActionImportance':np.asarray(rand),
        'InterventionalATE_vs_noop':np.asarray(ate),
    }


def exact_noop_shapley(value_by_active_subset: Mapping[tuple[int,...],float], n_players: int) -> np.ndarray:
    """Exact Shapley values for a coalition value table keyed by active players."""
    n=int(n_players); fact=math.factorial; result=np.zeros(n,float)
    for i in range(n):
        others=[j for j in range(n) if j!=i]
        for r in range(len(others)+1):
            weight=fact(r)*fact(n-r-1)/fact(n)
            for S in itertools.combinations(others,r):
                S=tuple(sorted(S)); Si=tuple(sorted(S+(i,)))
                result[i]+=weight*(float(value_by_active_subset[Si])-float(value_by_active_subset[S]))
    return result


def query_regret(scores: Sequence[float], utility: Sequence[float], k: int) -> dict:
    scores=np.asarray(scores,float); utility=np.asarray(utility,float); k=int(k)
    if scores.shape!=utility.shape: raise ValueError('scores and utility must align')
    chosen=np.argsort(-scores,kind='stable')[:k]; optimal=np.argsort(-utility,kind='stable')[:k]
    regret=float(np.sum(utility[optimal])-np.sum(utility[chosen]))
    return {'regret':regret,'chosen':chosen.tolist(),'optimal':optimal.tolist(),'topk_exact':int(set(chosen)==set(optimal))}
