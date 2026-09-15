"""R5: exact finite construction and symmetry-reduced hard-budget Bellman DP.
The full-state DP for d <= 6 independently checks the reduction. Fractions only.
Physical decisions are 0,1; auxiliary membership reads bits. No novelty claim.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json,hashlib

def parity(x):return x.bit_count()%2

def support(d,x):return {1-parity(x)}|{i+2 for i in range(d) if x>>i&1}

def full_dp(d,M):
    @lru_cache(None)
    def risk(worlds,budget,unused):
        n=len(worlds); p=sum(parity(x) for x in worlds)
        best=F(min(p,n-p),n)
        if budget>=M:return F(0) # physical tip 0 or 1
        if budget:
            for i in range(d):
                if unused>>i&1:
                    groups=[tuple(x for x in worlds if x>>i&1==bit) for bit in (0,1)]
                    val=sum((F(len(g),n)*risk(g,budget-1,unused^(1<<i)) for g in groups if g),F(0))
                    best=min(best,val)
        return best
    return [risk(tuple(range(1<<d)),B,(1<<d)-1) for B in range(d+1)]

def collapsed(d,M):
    @lru_cache(None)
    def risk(remaining,B):
        if remaining==0 or B>=M:return F(0)
        best=F(1,2)
        if B>=1:best=min(best,risk(remaining-1,B-1))
        return best
    return [risk(d,B) for B in range(d+1)]

def run():
    checks=0;rows=[]
    for d in range(2,11):
        m=d+2
        for x in range(1<<d):
            W=support(d,x)
            for j in (0,1):
                # Multi-tip indicator kernel: retained singleton j has radius
                # (m-1)/2 exactly when its own tip is present.
                radius=F(m-1,2)*int(j in W)
                assert F(2,m-1)*radius==int(j!=parity(x));checks+=1
            for i in range(d):
                assert (i+2 in W)==bool(x>>i&1)
                assert parity(x^(1<<i))==1-parity(x);checks+=2
        for M in sorted({d,2*d,d*d}):
            vals=collapsed(d,M)
            assert vals==[F(1,2) if B<min(d,M) else F(0) for B in range(d+1)]
            independent=full_dp(d,M) if d<=6 else None
            if independent is not None:assert vals==independent
            rows.append({'d':d,'direct_cost':M,'hard_budget_risk':[str(x) for x in vals],
              'full_state_dp_verified':independent is not None,'optimal_zero_error_cost':min(d,M),
              'one_step_risk_greedy_cost':M,'greedy_cost_ratio':str(F(M,min(d,M))),
              'world_entropy_greedy_cost':d,'parity_entropy_greedy_cost':M,
              'entropy_scope':'world entropy gives gain 1 per bit, direct parity gain 1; parity entropy gives bits gain 0 until last bit'})
    return {'scope':'Exact finite uniform-prior, pathwise-cost family; XOR is a benchmark, not a novelty claim.',
      'dp_reduction':'Conditional completions form a subcube. An unqueried-bit flip pairs opposite parities. Direct query reveals parity; each auxiliary query reduces remaining dimension by one.',
      'physical_bridge_checks':checks,'cases':rows}
if __name__=='__main__':
    out=run();out['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
    print('PASS',len(out['cases']),'design cells;',out['physical_bridge_checks'],'exact bridge/pairing checks')
