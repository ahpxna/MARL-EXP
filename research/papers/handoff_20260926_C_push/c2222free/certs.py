"""Exact potentials for the free-value certificates, in region bases (s,t).
Polynomials in s,t: dict {(i,j): Fraction}."""
import itertools
from fractions import Fraction as Fr
ST=list(itertools.product(range(3),repeat=4))
def padd(p,q):
    r=dict(p)
    for k,v in q.items(): r[k]=r.get(k,0)+v
    return {k:v for k,v in r.items() if v!=0}
def pneg(p): return {k:-v for k,v in p.items()}
def pmul(p,q):
    r={}
    for k1,v1 in p.items():
        for k2,v2 in q.items():
            k=(k1[0]+k2[0],k1[1]+k2[1]); r[k]=r.get(k,0)+v1*v2
    return {k:v for k,v in r.items() if v!=0}
def lin(cs,ct): return {k:Fr(v) for k,v in {(1,0):cs,(0,1):ct}.items() if v!=0}
def const(c): return {(0,0):Fr(c)} if c else {}
def ev(p,s,t): return sum(v*Fr(s)**i*Fr(t)**j for (i,j),v in p.items())
def nonneg_coeffs(p): return all(v>=0 for v in p.values())
# regions: a,b as linear forms in (s,t); sample interior point (s,t)
REG={
 'R1': dict(a=lin(2,1), b=lin(1,1), pt=(1,1)),   # s=a-b, t=2b-a
 'R2': dict(a=lin(3,2), b=lin(1,1), pt=(1,1)),   # s=a-2b, t=3b-a
 'R3': dict(a=lin(1,3), b=lin(0,1), pt=(1,1)),   # s=a-3b, t=b
}
def scal(c,p): return {k:Fr(c)*v for k,v in p.items() if c*v!=0}
def sumP(ps):
    r={}
    for p in ps: r=padd(r,p)
    return r
def ssum(R,v): return padd(scal(v[0]-v[1],R['a']), scal(v[2]-v[3],R['b']))
def beta(R,name,k):
    a,b=R['a'],R['b']
    if k in (1,7): return b
    if k in (0,2,4,6,8): return {}
    # k=3,5
    if name=='R1': return padd(scal(2,b),pneg(a))
    if name=='R2': return padd(a,scal(-2,b))
    return b
def cost(R,name,v):
    k=sum(v); s=ssum(R,v); x=ev(s,*R['pt'])
    sg=1 if x>0 else (-1 if x<0 else 0)
    # check sign fixed on region: all coeffs of sg*s >= 0
    ab=scal(sg,s)
    assert nonneg_coeffs(ab), (name,v,s)
    return padd(ab,pneg(beta(R,name,k)))
def certs(name):
    R=REG[name]; a,b=R['a'],R['b']
    out={}
    if name=='R1':
        out['A']=({3:const(1),4:const(1),5:const(1)}, scal(2,padd(a,pneg(b))))   # sum r3..r5 >= 2(a-b)
    if name=='R3':
        out['U3']=({k:const(1) for k in range(1,8)}, scal(2,padd(a,pneg(b))))
    if name=='R2':
        t3=padd(scal(3,b),pneg(a))
        out['U']=({k:const(1) for k in range(1,8)}, scal(4,b))
        out['F1']=({3:b,4:t3,5:b}, pmul(scal(2,b),t3))
        out['F2']=({1:t3,2:t3,3:b,4:t3,5:b,6:t3,7:t3}, pmul(scal(2,a),t3))
    return out
def dp(name,mu,W):
    R=REG[name]
    phi={}; node={}
    for v in sorted(ST,key=lambda u:-sum(u)):
        k=sum(v)
        if k==8: phi[v]={}; continue
        node[v]=pmul(mu.get(k,{}),cost(R,name,v)) if k in mu else {}
        best=None
        for tt in range(4):
            if v[tt]<2:
                w=tuple(v[j]+(1 if j==tt else 0) for j in range(4))
                val=ev(phi[w],*R['pt'])
                if best is None or val<best[0]: best=(val,w)
        phi[v]=padd(node[v],phi[best[1]])
    bad=[]
    for v in ST:
        k=sum(v)
        if k==8: continue
        for tt in range(4):
            if v[tt]<2:
                w=tuple(v[j]+(1 if j==tt else 0) for j in range(4))
                d=padd(padd(node[v],phi[w]),pneg(phi[v]))
                if not nonneg_coeffs(d): bad.append((v,tt,d))
    start=padd(phi[(0,0,0,0)],pneg(W))
    return phi,bad,start
if __name__=="__main__":
    for name in ['R1','R2','R3']:
        for cn,(mu,W) in certs(name).items():
            phi,bad,start=dp(name,mu,W)
            print(name,cn,"bad edges:",len(bad),"phi0-W:",start, "ok" if nonneg_coeffs(start) else "START FAIL")
            for x in bad[:5]: print("   ",x)
