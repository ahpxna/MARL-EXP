"""Exact physical response checks and a same-mean/different-raw-law control."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib,json

def gate(A,j,x):return F(0) if x[j] else F(any(x[i] for i in A) or sum(x[i] for i in range(len(x)) if i not in A and i!=j)>=2)
def weight(t,x):return t**sum(x)*(1-t)**(len(x)-sum(x))
def params(m,A,j,t):
    b=m-len(A)-1
    a=(1-t)**len(A)*((1-t)**b+b*t*(1-t)**(b-1))
    s=(b-1)*t*(1-t)**(len(A)+b-1)
    return [a-1 if i==j else a if i in A else s for i in range(m)]
def world(m,A,T,j,rho,t0):
    slopes=params(m,A,j,t0);comp=[(rho if i in T else 0)-slopes[i] for i in range(m)]
    a=slopes[next(iter(A))];shift=(1-t0)*(1-a)+t0*sum(comp)
    return {x:gate(A,j,x)+sum(comp[i]*x[i] for i in range(m))-shift for x in product((0,1),repeat=m)}
def response(table,t,i,u):
    return sum((weight(t,x)*table[x[:i]+(u,)+x[i+1:]] for x in table),F(0))
def moment(table,t,p):return sum((weight(t,x)*v**p for x,v in table.items()),F(0))

if __name__=='__main__':
    rows=[];negative=None
    for m in [6,8]:
        k=m//2;A=frozenset(range(k));B=frozenset(range(1,k+1));T=A;j=m-1;i=0;rho=F(3,2)
        for t0 in [F(1,8),F(1,4),F(1,2)]:
            wa,wb=[world(m,W,T,j,rho,t0) for W in [A,B]]
            for coord in range(m):
                for u in (0,1):
                    expected=(rho if coord in T else 0)*(u-t0)
                    assert response(wa,t0,coord,u)==response(wb,t0,coord,u)==expected
            for t in [F(0),F(1,8),F(1,4),F(1,2),F(3,4)]:
                observed=(response(wa,t,i,1)-response(wa,t,i,0))-(response(wb,t,i,1)-response(wb,t,i,0))
                expected=(1-t)**(m-2)-(1-t0)**(m-2)
                assert observed==expected
                rows.append(dict(m=m,t0=str(t0),t=str(t),contrast=str(observed)))
            # Means at t0 agree, but the physical raw mixtures have different third moments.
            ma,mb=moment(wa,t0,1),moment(wb,t0,1);va,vb=moment(wa,t0,3),moment(wb,t0,3)
            assert ma==mb==0
            full_data_information=sum((weight(t0,x)*(wa[x]-wb[x])**2/2 for x in wa),F(0))
            assert full_data_information>0
            if negative is None and va!=vb:
                negative=dict(m=m,t0=str(t0),A=sorted(A),B=sorted(B),T=sorted(T),rho=str(rho),all_first_order_responses_equal=True,
                    mean_A=str(ma),mean_B=str(mb),raw_third_moment_A=str(va),raw_third_moment_B=str(vb),
                    gaussian_noise_variance='1',noisy_Y_third_moment_A=str(va),noisy_Y_third_moment_B=str(vb),
                    full_observed_X_gaussian_KL_formula=str(full_data_information),
                    interpretation='Adding independent unit Gaussian noise preserves the unequal third moments because both raw means are zero; equal first-order responses do not imply equal raw observation laws. KL expression is a finite arithmetic check, not a new Lean KL-chain theorem.')
    assert negative is not None
    p=Path(__file__);out=dict(scope='Exact rational finite construction checks; response-instrument law distinguished from raw samples',source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),contrast_checks=len(rows),rows=rows,raw_law_negative_control=negative)
    p.with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(dict(contrast_checks=len(rows),negative_control=negative),indent=2))
