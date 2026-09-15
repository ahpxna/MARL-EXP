"""Exact small-cube validation, then numerical large-k orbit games.
All large-k LP values are NUMERICAL, never exact certificates.
"""
import argparse, hashlib, itertools, json, math
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.stats import hypergeom


def slopes(k,t):
    c=(1-t)**(2*k-2);return c*(1+(k-2)*t),(k-2)*t*c

def orbit_loss(k,rho,t,d,u):
    """d=|T\\S|, u=|A intersect (T\\S)|, k>=3, rho>=1, 0<=t<=1/2."""
    a,b=slopes(k,t)
    lmax=rho*d-a*u-b*(d-u)
    lmin=-a*(k-u)-b*(k-1-d+u)
    correction=min(a,2*b) if d==0 else b if (d==1 and u==0) else 0
    upper=1+lmax-correction
    lower=min(lmin+1-a, -b if k-1-d+u>0 else 0)
    return (upper-lower)/2

def validate_cube():
    checked=0
    for k in (3,4):
        m=2*k;A=set(range(k));B=set(range(k,2*k-1));z=m-1
        cube=list(range(1<<m))
        gate=[int(not(x>>z&1) and (any(x>>i&1 for i in A) or sum(x>>i&1 for i in B)>=2)) for x in cube]
        for t in map(F,('0','1/64','1/16','1/4','1/2')):
            a,b=slopes(k,t)
            for j in range(m):
                slope=sum((gate[x|(1<<j)]-gate[x])*t**x.bit_count()*(1-t)**(m-1-x.bit_count()) for x in cube if not(x>>j&1))
                assert slope==(a if j in A else b if j in B else a-1),(k,t,j,slope,a,b)
            for rho in map(F,('1','3/2','15/8','2')):
                for d in range(k+1):
                    for u in range(max(0,d-(k-1)),min(k,d)+1):
                        D=set(list(sorted(A))[:u]+list(sorted(B))[:d-u])
                        raw=[gate[x]+sum((rho*int(i in D)-(a if i in A else b if i in B else a-1))*int(x>>i&1) for i in range(m)) for x in cube]
                        loss=(max(raw)-min(raw))/2
                        assert loss==orbit_loss(k,rho,t,d,u),(k,t,rho,d,u,loss,orbit_loss(k,rho,t,d,u))
                        checked+=1
    return dict(exact_losses_checked=checked,slopes_verified=True,widths=[3,4],
        method='Full cube with Fraction, independent of extremum formula')

def game(k,rho,t):
    # Symmetrizing a randomized decision over permutations of T is minimax valid.
    # h ranges 1..k since A and T are k-subsets of a (2k-1)-set.
    matrix=[]
    for h in range(1,k+1):
        best=min(orbit_loss(k,rho,t,d,u) for d in range(k+1)
                 for u in range(max(0,d-(k-h)),min(h,d)+1))
        row=[]
        for d in range(k+1):
            us=np.arange(max(0,d-(k-h)),min(h,d)+1)
            probs=hypergeom.pmf(us,k,h,d)
            assert abs(float(probs.sum())-1)<1e-10
            row.append(sum(float(p)*(orbit_loss(k,rho,t,d,int(u))-best) for u,p in zip(us,probs)))
        matrix.append(row)
    M=np.array(matrix)
    lp=linprog([0.]*(k+1)+[1.],A_ub=np.c_[M,-np.ones(k)],b_ub=np.zeros(k),
        A_eq=[[1.]*(k+1)+[0.]],b_eq=[1.],bounds=[(0,None)]*(k+1)+[(None,None)],method='highs')
    assert lp.success,lp.message
    return float(lp.fun),[(d,float(p)) for d,p in enumerate(lp.x[:-1]) if p>1e-7]

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',required=True);args=p.parse_args();out=Path(args.out)
    if out.exists():raise SystemExit(f'refusing to overwrite {out}')
    small=validate_cube();print(json.dumps(small),flush=True)
    rows=[]
    for k in (4,8,16,32,64):
        for rho in (1.,1.5,1.875):
            for tau in (0.,.025,.05,.1,.2,.4):
                t=tau/k;value,mix=game(k,rho,t);a,b=slopes(k,t)
                c=math.exp(-2*tau);aa=(1+tau)*c;bb=tau*c
                predicted=max(0.,(rho-2*bb)*(2*aa-rho)/(4*c))
                finite_proxy=max(0.,(rho-2*b)*(2*a-rho)/(4*(a-b)))
                rows.append(dict(k=k,rho=rho,tau=tau,t=t,value_numerical=value,
                    value_over_k=value/k,limit_prediction=predicted,
                    normalized_error=value/k-predicted,finite_coefficient_proxy=finite_proxy,
                    proxy_error_unscaled=value-k*finite_proxy,decision_support=mix))
        print(json.dumps(dict(k=k,completed=True)),flush=True)
    result=dict(evidence_class='EXACT_SMALL_CUBE_VALIDATION_AND_NUMERICAL_LARGE_K_LP',
        exact_validation=small,rows=rows,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        conjecture='V_k(tau/k,rho)/k tends to positive_part((rho-2*tau*exp(-2*tau))*(2*(1+tau)*exp(-2*tau)-rho)/(4*exp(-2*tau))) for 1<=rho<=2 and fixed tau>=0.',
        scope='Reference-aware same-Q family; different t means different compensated worlds. Symmetry reduction and general-k formula are mathematical derivations, not Lean-audited here. Numerical LP values are not exact minimax certificates.')
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
