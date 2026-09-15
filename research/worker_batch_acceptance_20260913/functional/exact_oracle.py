"""Exact free-table full-extrema oracle for two rows and three actions.

All arithmetic and certificates use Fraction. Every one of the 324 closed
active regions receives either a convex KKT certificate or a Farkas certificate.
This is a finite exact solver, not a claim about coupled physical tables.
"""
from fractions import Fraction as F
from itertools import product, permutations, combinations
import json
from pathlib import Path

def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))
def det(a,b):return a[0]*b[1]-a[1]*b[0]
def mat(H,x):return tuple(dot(r,x) for r in H)
def solve(a,b,c,d):
    z=det(a,c)
    return None if not z else ((b*c[1]-a[1]*d)/z,(a[0]*d-b*c[0])/z)
def evaluate(H,g,c,x):return dot(x,mat(H,x))/2+dot(g,x)+c

def region(pi,pj,ti,tj,states,pair,opening):
    # Objective x'Hx/2+g'x+c, inequalities A_i x >= b_i, x=(ell,z).
    H=[[F(0),F(0)],[F(0),F(0)]];g=[F(0),F(0)];c=F(0)
    cons=[((F(0),F(1)),F(0))]
    def term(weight,v,offset):
        nonlocal c
        for i in range(2):
            g[i]+=weight*offset*v[i]
            for j in range(2):H[i][j]+=weight*v[i]*v[j]
        c+=weight*offset**2/2
    for p,t,s in zip(pi,ti,states):
        if s=='L':
            cons.append(((F(1),F(0)),t));term(p,(F(1),F(0)),-t)
        elif s=='M':cons.extend([((F(-1),F(0)),-t),((F(1),F(1)),t)])
        else:
            cons.append(((F(-1),F(-1)),-t));term(p,(F(1),F(1)),-t)
    a,b=pair;gap=tj[a]-tj[b]
    if opening:
        cons.append(((F(0),F(1)),gap));term(pj[a]*pj[b]/(pj[a]+pj[b]),(F(0),F(1)),-gap)
    else:cons.append(((F(0),F(-1)),-gap))
    return H,g,c,cons

def kkt(H,g,cons,x):
    if any(dot(a,x)<b for a,b in cons):return None
    grad=tuple(u+v for u,v in zip(mat(H,x),g))
    if grad==(0,0):return []
    active=[i for i,(a,b) in enumerate(cons) if dot(a,x)==b]
    for i in active:
        a=cons[i][0];j=0 if a[0] else 1
        if not a[j]:continue
        lam=grad[j]/a[j]
        if lam>=0 and tuple(lam*v for v in a)==grad:return [(i,lam)]
    for i,j in combinations(active,2):
        a,b=cons[i][0],cons[j][0]
        lam=solve((a[0],b[0]),grad[0],(a[1],b[1]),grad[1])
        if lam is not None and min(lam)>=0:return [(i,lam[0]),(j,lam[1])]
    return None

def farkas(cons):
    for count in (1,2,3):
        for ix in combinations(range(len(cons)),count):
            aa=[cons[i][0] for i in ix]
            if count==1:weights=[F(1)] if aa[0]==(0,0) else None
            elif count==2:
                if det(*aa):continue
                coord=0 if aa[0][0] or aa[1][0] else 1
                weights=[aa[1][coord],-aa[0][coord]]
            else:weights=[det(aa[1],aa[2]),det(aa[2],aa[0]),det(aa[0],aa[1])]
            if weights is None:continue
            for sign in (1,-1):
                ww=[sign*w for w in weights]
                if min(ww)<0:continue
                if any(sum((w*a[c] for w,a in zip(ww,aa)),F(0)) for c in range(2)):continue
                if sum((w*cons[i][1] for w,i in zip(ww,ix)),F(0))>0:return list(zip(ix,ww))
    return None

def solve_region(H,g,c,cons):
    candidates=[]
    x=solve(H[0],-g[0],H[1],-g[1])
    if x is not None:candidates.append(x)
    for a,b in cons:
        if a==(0,0):continue
        x0=(b/a[0],F(0)) if a[0] else (F(0),b/a[1]);d=(-a[1],a[0])
        denom=dot(d,mat(H,d));grad=tuple(u+v for u,v in zip(mat(H,x0),g))
        if denom:
            t=-dot(grad,d)/denom;candidates.append(tuple(u+t*v for u,v in zip(x0,d)))
        elif dot(grad,d)==0:candidates.append(x0)
    for (a,b),(v,w) in combinations(cons,2):
        x=solve(a,b,v,w)
        if x is not None:candidates.append(x)
    for x in candidates:
        multipliers=kkt(H,g,cons,x)
        if multipliers is not None:return {'kind':'optimal','point':x,'multipliers':multipliers,'value':evaluate(H,g,c,x)}
    proof=farkas(cons)
    if proof is None:raise AssertionError('Region neither certified optimal nor certified infeasible')
    return {'kind':'infeasible','multipliers':proof}

def full_oracle(pi,pj,ti,tj):
    pi,pj,ti,tj=[tuple(map(F,row)) for row in (pi,pj,ti,tj)]
    assert all(len(row)==3 for row in (pi,pj,ti,tj)) and min(pi+pj)>0
    records=[]
    for states,pair,opening in product(product('LMU',repeat=3),permutations(range(3),2),(False,True)):
        H,g,c,cons=region(pi,pj,ti,tj,states,pair,opening)
        cert=solve_region(H,g,c,cons)
        records.append({'states':''.join(states),'pair':pair,'opening':opening,**cert})
    best=min((r for r in records if r['kind']=='optimal'),key=lambda r:r['value'])
    ell,z=best['point'];a,b=best['pair'];gap=max(F(0),z-(tj[a]-tj[b]))
    vi=[min(ell+z,max(ell,t)) for t in ti];vj=list(tj)
    vj[a]+=gap*pj[b]/(pj[a]+pj[b]);vj[b]-=gap*pj[a]/(pj[a]+pj[b])
    return {'precision_i':pi,'precision_j':pj,'theta_i':ti,'theta_j':tj,'value':best['value'],
            'alternative_i':vi,'alternative_j':vj,'regions':records}

def serial(x):
    if isinstance(x,F):return str(x)
    if isinstance(x,dict):return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)):return [serial(v) for v in x]
    return x

def examples():
    out=[]
    for eta in [F(1),F(1,4),F(1,100),F(1,10000)]:
        for family in ['cheap_middle','cheap_maximum']:
            pi=(1,1,1) if family=='cheap_middle' else (1,eta,1)
            pj=(1,1,eta) if family=='cheap_middle' else (1,1,1)
            ti=(0,1,F(1,2)) if family=='cheap_middle' else (0,1,F(3,4))
            ans=full_oracle(pi,pj,ti,(0,F(1,2),F(1,4)))
            scalar=F(1,32) if family=='cheap_middle' else eta/(8*(1+3*eta))
            ans.update(family=family,eta=eta,scalar=scalar,ratio=ans['value']/scalar)
            out.append(ans)
    # Zero-gap and flat tables are retained as controls.
    out.append(dict(full_oracle((1,2,3),(3,2,1),(0,1,F(1,2)),(0,1,F(1,2))),family='tie'))
    out.append(dict(full_oracle((1,2,3),(3,2,1),(0,0,0),(0,0,0)),family='flat'))
    return out

if __name__=='__main__':
    out=examples();p=Path(__file__).with_name('exact_oracle_certificates.json')
    p.write_text(json.dumps(serial(out),indent=2)+'\n')
    for r in out:print(r['family'],r.get('eta',''),r['value'],r.get('ratio',''))
