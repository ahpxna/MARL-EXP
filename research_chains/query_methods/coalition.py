"""Exact Shapley primitive for one explicitly declared noop coalition table."""
from __future__ import annotations
import itertools,math
from typing import Mapping
import numpy as np


def exact_noop_shapley(value_by_active_subset: Mapping[tuple[int,...],float], n_players: int) -> np.ndarray:
    n=int(n_players); result=np.zeros(n,float)
    for i in range(n):
        others=[j for j in range(n) if j!=i]
        for r in range(len(others)+1):
            weight=math.factorial(r)*math.factorial(n-r-1)/math.factorial(n)
            for subset in itertools.combinations(others,r):
                subset=tuple(sorted(subset)); with_i=tuple(sorted(subset+(i,)))
                result[i]+=weight*(float(value_by_active_subset[with_i])-float(value_by_active_subset[subset]))
    return result
