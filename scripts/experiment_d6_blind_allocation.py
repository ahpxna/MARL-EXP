#!/usr/bin/env python3
"""Full unknown-A common allocation: no supplied A/B core, j remains known.
All legal query orbits are kept under permutations of the 2q+1 non-j coordinates.
Numerical static maximin evidence, not an adaptive-discovery lower bound.
"""
import argparse,json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.optimize import linprog
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information
from experiment_d6_unresolved_label_family import arrays as core_arrays,hypervar


def arrays(q,known_a,known_b,mu):
    C=known_a;D=known_b;na=q+1-C;nb=q-D;U=na+nb;lam=1-mu;ptrue=nb/U
    alts=[(c,d,a,b) for c in range(C+1) for d in range(D+1)
          for a in range(na+1) for b in range(nb+1)
          if c+d+a+b==q+1 and (c,d,a,b)!=(C,0,na,0)]
    groups=[('s',g) for g,size in enumerate([C,D,U,1]) if size]
    groups += [('g',s,t,u,h) for s in range(C+1) for t in range(D+1)
               for u in range(U+1) for h in [0,1] if s+t+u<=q and (h or s+t+u>=2)]
    aa=[];bb=[];cc=[]
    for c,d,a,b in alts:
        pc=1-c/C if C else 0.;pd=1-d/D if D else 0.;pu=1-(a+b)/U;cross=(nb-b)/U
        ar=[];br=[];cr=[]
        for g in groups:
            if g[0]=='s':
                k=g[1]
                if k==0:A,B,E=pc,0.,0.
                elif k==1:A,B,E=pd,-2*mu*pd,mu*mu
                elif k==2:A,B,E=pu,-2*mu*cross,mu*mu*ptrue
                else:A,B,E=1.,-2*mu,mu*mu
            else:
                _,s,t,u,h=g;ex=t+u*ptrue;ey=s*pc+t*pd+u*pu
                vx=hypervar(U,u,ptrue)
                vy=hypervar(C,s,pc)+hypervar(D,t,pd)+hypervar(U,u,pu)
                cov=u*(U-u)/(U-1)*(cross-ptrue*pu) if U>1 else 0.
                alpha=lam*ex-ey+mu*h;beta=ey-h
                A=beta*beta+vy;B=2*alpha*beta-2*vy+2*lam*cov
                E=alpha*alpha+lam*lam*vx+vy-2*lam*cov
            ar.append(A);br.append(B);cr.append(E)
        aa.append(ar);bb.append(br);cc.append(cr)
    return np.array(aa),np.array(bb),np.array(cc),groups


def solve(q,mu,gamma,tol=2e-10):
    aa,bb,cc,groups=arrays(q,0,0,mu);Q=len(groups)
    cuts=[*(cc/2),*((aa*mu*mu+bb*mu+cc)/2),*((aa+bb+cc)/2)]
    for it in range(100):
        mat=np.asarray(cuts)
        lp=linprog([0.]*Q+[-1.],A_ub=np.column_stack([-mat,np.ones(len(mat))]),b_ub=np.zeros(len(mat)),
            A_eq=np.array([[1.]*Q+[0.]]),b_eq=[1.],bounds=[(0,None)]*Q+[(0,gamma)],
            method='highs',options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        if not lp.success:raise RuntimeError(lp.message)
        w=lp.x[:-1];a=aa@w;b=bb@w;c=cc@w
        nu=np.clip(np.divide(-b,2*a,out=np.zeros_like(b),where=a>0),0,1)
        vals=(a*nu*nu+b*nu+c)/2;lo=float(vals.min());hi=float(lp.x[-1])
        if hi-lo<=tol:break
        bad=np.flatnonzero(vals<hi-tol)
        cuts.extend((aa[bad]*nu[bad,None]**2+bb[bad]*nu[bad,None]+cc[bad])/2)
    return dict(value_lower=lo,value_upper=hi,regret_lower=gamma-hi,regret_upper=gamma-lo,
        converged=hi-lo<=tol,iterations=it+1,query_orbits=Q,alternative_orbits=len(aa),
        active_queries=[dict(orbit=g,weight=float(z)) for g,z in zip(groups,w) if z>1e-6])


def verify_blind_worlds(q=3,mu=.63):
    # Independent direct sum over every literal query and alternative world.
    from itertools import combinations
    from fractions import Fraction
    from verify_d6_information_limit_bridge import family_world
    m=2*q+2;j=q+1;ground=[i for i in range(m) if i!=j]
    A=sum(1<<i for i in ground[:q+1]);truth=family_world(m,Fraction(str(mu)),A)
    truth=np.asarray(truth,float)/Fraction(str(mu)).denominator
    alternatives=[sum(1<<i for i in c) for c in combinations(ground,q+1)]
    aa,bb,cc,groups=arrays(q,0,0,mu);worst=0.;pairs=0
    # Rows are ordered by (a,b); recover their alternative distance.
    ds=[q+1-a for a in range(q+2) for b in range(q+1)
        if a+b==q+1 and (a,b)!=(q+1,0)]
    for B in alternatives:
        if A==B:continue
        row=ds.index((A&~B).bit_count())
        for nu in [Fraction(0),Fraction(2,5),Fraction(1)]:
            alt=np.asarray(family_world(m,nu,B),float)/nu.denominator
            for k,g in enumerate(groups):
                if g[0]=='s':corners=[1<<i for i in ground] if g[1]==2 else [1<<j]
                else:
                    _,s,t,u,h=g
                    corners=[sum(1<<i for i in c)|(1<<j if h else 0) for c in combinations(ground,u)]
                actual=float(np.mean([(truth[z]-alt[z])**2 for z in corners]));pairs+=len(corners)
                predicted=aa[row,k]*float(nu)**2+bb[row,k]*float(nu)+cc[row,k]
                worst=max(worst,abs(actual-predicted))
    assert worst<1e-11,worst
    return dict(q=q,query_world_evaluations=pairs,max_abs_error=worst)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--q',type=int,nargs='+',default=[4,8,16,32,64,128])
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/blind_allocation.json'))
    args=ap.parse_args();checks=[];rows=[]
    for q,r in [(3,1),(3,2),(4,4)]:
        original=core_arrays(q,r,.64);general=arrays(q,q+1-r,q-r,.64)
        assert original[3]==general[3]
        err=max(float(np.max(np.abs(a-b))) for a,b in zip(original[:3],general[:3]))
        assert err<1e-12;checks.append(dict(q=q,r=r,known_core_coefficient_crosscheck=err))
    checks.append(verify_blind_worlds())
    for q in args.q:
        p=phase_parameters(q)
        for side in [-1,0,1]:
            mu=p['mu_U']+side*.1*(p['mu_H']-p['mu_U']);gamma=information(q,mu,oracle(q,mu,p))[0]
            row=dict(q=q,side=side,mu=mu,oracle=gamma,**solve(q,mu,gamma))
            row['q_squared_regret_lower']=q*q*row['regret_lower'];row['q_squared_regret_upper']=q*q*row['regret_upper']
            rows.append(row);print({k:row[k] for k in ['q','side','q_squared_regret_lower','q_squared_regret_upper','converged']},flush=True)
            args.out.write_text(json.dumps(dict(evidence_class='FULL_UNKNOWN_LABEL_STATIC_ALLOCATION',
                script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),checks=checks,rows=rows,
                scope=['Known interaction coordinate j; no known A or B core.',
                       'All legal query orbits and alternative distances, continuous nuisance.',
                       'Floating-point LP separation, not a formal certificate.',
                       'No adaptive label learning; does not prove unavoidable adaptive regret.']),indent=2)+'\n')
if __name__=='__main__':main()
