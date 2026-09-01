"""Primitive external-query baselines with explicit implementation scope.

These are not branded reimplementations of entire published algorithms.  Each
method is named by the mathematical/interventional primitive it actually uses.
"""
from __future__ import annotations
from typing import Sequence
import numpy as np
from .query_contracts import METHOD_SPECS, QUERY_SPECS, LEGACY_METHOD_ALIASES
from .query_methods import response_primitives, exact_noop_shapley

METHOD_SCOPE={name:spec.implementation_scope for name,spec in METHOD_SPECS.items()}
QUERY_SCOPE={name:spec.semantic_target for name,spec in QUERY_SPECS.items()}


def query_regret(scores: Sequence[float], utility: Sequence[float], k: int) -> dict:
    scores=np.asarray(scores,float); utility=np.asarray(utility,float); k=int(k)
    if scores.shape!=utility.shape: raise ValueError('scores and utility must align')
    chosen=np.argsort(-scores,kind='stable')[:k]; optimal=np.argsort(-utility,kind='stable')[:k]
    regret=float(np.sum(utility[optimal])-np.sum(utility[chosen]))
    chosen_set,optimal_set=set(chosen),set(optimal)
    union=chosen_set|optimal_set
    jaccard=float(len(chosen_set&optimal_set)/len(union)) if union else 1.0
    relevance=np.asarray(utility,float)-float(np.min(utility))
    gains=(2.0**relevance)-1.0
    discounts=1.0/np.log2(np.arange(2,k+2,dtype=float))
    dcg=float(np.sum(gains[chosen]*discounts)); ideal=float(np.sum(gains[optimal]*discounts))
    ndcg=float(dcg/ideal) if ideal>0 else 1.0
    return {'regret':regret,'chosen':chosen.tolist(),'optimal':optimal.tolist(),'topk_exact':int(chosen_set==optimal_set),'jaccard':jaccard,'ndcg':ndcg}
