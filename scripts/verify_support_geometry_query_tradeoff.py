"""Exact finite support geometry and adaptive membership decision complexity.
The all-positive path is charged; no full-identification endpoint is substituted
for finding any singleton with zero selected radius. Deterministic unit-cost
individual-tip membership queries only.
"""
import hashlib,json
from functools import lru_cache
from itertools import combinations
from pathlib import Path


def solve(m,s):
    full=(1<<m)-1
    worlds=tuple(sum(1<<i for i in c) for c in combinations(range(m),s))
    tips=[[1-(m-1)*(i==w) for i in range(m)] for w in range(m)]
    for W in worlds:
        points=[[0]*m]+[tips[w] for w in range(m) if W>>w&1]
        for j in range(m):
            residual=[sum(p)-p[j] for p in points]
            span=max(residual)-min(residual)
            assert span==(m-1 if W>>j&1 else 0)
    @lru_cache(None)
    def cost(fibre):
        union=0
        for W in fibre:union |= W
        if union != full:return 0
        best=m
        for a in range(m):
            yes=tuple(W for W in fibre if W>>a&1)
            no=tuple(W for W in fibre if not W>>a&1)
            if not yes or not no:continue
            best=min(best,1+max(cost(yes),cost(no)))
        return best
    exact=cost(worlds)
    assert exact==s
    return dict(m=m,present_tips=s,world_count=len(worlds),minimum_worst_case_adaptive_queries=exact,
                states_explored=cost.cache_info().currsize,
                max_radius=(m-1)/2,geometry_checked=True)

rows=[]
for m in range(2,10):
    for s in range(1,m):rows.append(solve(m,s))
out=Path('research/high_risk_20260910/support_geometry_query_tradeoff.json')
out.write_text(json.dumps(dict(evidence_class='EXACT_FINITE_ADAPTIVE_DECISION_TREE_DP',
    query_model='individual physical tip membership',epsilon=0,
    scope='finite worlds have exactly s of m listed non-anchor tips; Gaussian/noisy/randomized costs not claimed',
    script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows),indent=2)+'\n')
print(json.dumps(dict(cases=len(rows),largest_m=9,all_exact_cost_equal_present_tip_count=True)))
