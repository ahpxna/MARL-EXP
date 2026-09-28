"""Exact certificate generator (scaled form) for g=(a,a,-a,-a,b,b,-b,-b).
node'(v) = mu'_k (|s_v| - beta_k) + sum_t ell'_{k t} (v_t/2 - k/8),   k=|v|
phi'(v) = node'(v) + min_w phi'(w);  bound = (phi'(0) - eta/8 * sum|ell'|) / (Z*D)."""
import itertools
from fractions import Fraction as Fr
from sym import P
STATES=[u for u in itertools.product(range(3),repeat=4)]
def sP(v): return P.lin(v[0]-v[1], v[2]-v[3])
def beta(regime):
    b3={'lo':P.lin(-1,2),'mid':P.lin(1,-2),'hi':P.lin(0,1)}[regime]
    return {0:P(),1:P.lin(0,1),2:P(),3:b3,4:P(),5:b3,6:P(),7:P.lin(0,1),8:P()}
def sign_at(p,r0):
    x=p.ev(r0,1)
    return 1 if x>0 else (-1 if x<0 else 0)
def nonneg_on(q,r1,r2):
    """q homogeneous poly in (a,b) deg<=2; check q(r,1)>=0 for r in [r1,r2] (r2 None = inf)."""
    # univariate coefficients
    c=[Fr(0)]*3
    for (i,j),v in q.t.items():
        c[i]+=v
    # q(r)=c0+c1 r+c2 r^2
    f=lambda r: c[0]+c[1]*r+c[2]*r*r
    if f(r1)<0: return False
    if r2 is None:
        if c[2]<0: return False
        if c[2]==0 and c[1]<0: return False
        cands=[]
        if c[2]>0: cands.append(-c[1]/(2*c[2]))
        return all(f(x)>=0 for x in cands if x>=r1)
    if f(r2)<0: return False
    if c[2]>0:
        x=-c[1]/(2*c[2])
        if r1<x<r2 and f(x)<0: return False
    return True
def gen(mu, ell, regime, r1, r2, r0, Z=None):
    """mu: dict k->P (scaled mu'); ell: dict (k,t)->P; returns phi dict, argmin dict, ok flag, bad edges."""
    bs=beta(regime)
    phi={}; arg={}; node={}
    for v in sorted(STATES,key=lambda u:-sum(u)):
        k=sum(v)
        if k==8: phi[v]=P(); continue
        s=sP(v); sg=sign_at(s,r0)
        absS = s*sg
        nd = mu.get(k,P())*(absS - bs[k])
        for t in range(4):
            if (k,t) in ell:
                nd = nd + ell[(k,t)]*(Fr(v[t],2)-Fr(k,8))
        node[v]=nd
        best=None
        for t in range(4):
            if v[t]<2:
                w=tuple(v[j]+(1 if j==t else 0) for j in range(4))
                val=phi[w].ev(r0,1)
                if best is None or val<best[0]: best=(val,w)
        phi[v]=nd+phi[best[1]]; arg[v]=best[1]
    bad=[]
    for v in STATES:
        k=sum(v)
        if k==8: continue
        for t in range(4):
            if v[t]<2:
                w=tuple(v[j]+(1 if j==t else 0) for j in range(4))
                diff=node[v]+phi[w]-phi[v]
                if not nonneg_on(diff,r1,r2): bad.append((v,t,diff))
    # also check abs sign constant on region: sign at r1,r2 not opposite
    for v in STATES:
        s=sP(v)
        for rr in [r1]+([r2] if r2 is not None else []):
            x=s.ev(rr,1)
            if x!=0 and (1 if x>0 else -1)!=sign_at(s,r0) and sign_at(s,r0)!=0:
                bad.append(('sign',v,rr))
        if r2 is None:
            ca=s.t.get((1,0),0)
            if ca!=0 and (1 if ca>0 else -1)!=sign_at(s,r0): bad.append(('signinf',v))
    return phi,node,bad
def ellsum(ell, r0):
    tot=P()
    for key,p in ell.items():
        sg=sign_at(p,r0)
        tot=tot+p*sg
    return tot
