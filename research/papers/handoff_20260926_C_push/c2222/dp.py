"""Exact DP (Fractions) for lower bounds: min over paths of sum_k mu_k c_k + band terms."""
import itertools
from fractions import Fraction as Fr
N=(2,2,2,2)
STATES=[u for u in itertools.product(range(3),repeat=4)]
def ssum(a,b,v): return a*(v[0]-v[1])+b*(v[2]-v[3])
def base(a,b,k):
    return min(abs(ssum(a,b,u)) for u in STATES if sum(u)==k)
def dp(a,b,mu,ell=None):
    """mu: dict k->weight (k=1..7). ell: dict (k,t)->mult; node cost adds sum_t ell[k,t]*(v_t/2-k/8).
    returns phi dict and phi(0)."""
    bs={k:base(a,b,k) for k in range(9)}
    phi={}
    for v in sorted(STATES,key=lambda u:-sum(u)):
        k=sum(v)
        if k==8: phi[v]=Fr(0); continue
        node=mu.get(k,0)*(abs(ssum(a,b,v))-bs[k])
        if ell:
            for t in range(4):
                node+=ell.get((k,t),0)*(Fr(v[t],2)-Fr(k,8))
        best=None
        for t in range(4):
            if v[t]<2:
                w=tuple(v[j]+(1 if j==t else 0) for j in range(4))
                if best is None or phi[w]<best: best=phi[w]
        phi[v]=node+best
    return phi,phi[(0,0,0,0)]
