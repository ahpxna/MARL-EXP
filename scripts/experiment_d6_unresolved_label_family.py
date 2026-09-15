#!/usr/bin/env python3
"""Common allocation across C(2r,r) possible labels, with all legal query orbits.
Known A-core has q+1-r coordinates, known B-core q-r; 2r coordinates are
unresolved. Symmetrization over these three coordinate groups is lossless for
this common-allocation minimax problem. This is not an adaptive-discovery bound.
"""
import argparse, json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.optimize import linprog
from experiment_d6_phase_boundary_cost import phase_parameters, oracle, information
from verify_d6_local_decoder_full_orbits import solve as pair_solve

def hypervar(size,draw,p):
    return 0. if size<=1 else draw*(size-draw)/(size-1)*p*(1-p)

def arrays(q,r,mu):
    C=q+1-r;D=q-r;U=2*r;lam=1-mu
    alts=[(c,d,a,b) for c in range(C+1) for d in range(D+1)
          for a in range(r+1) for b in range(r+1) if c+d+a+b==q+1 and (c,d,a,b)!=(C,0,r,0)]
    groups=[('s',g) for g,size in enumerate([C,D,U,1]) if size]
    groups += [('g',s,t,u,h) for s in range(C+1) for t in range(D+1) for u in range(U+1)
               for h in [0,1] if s+t+u<=q and (h or s+t+u>=2)]
    aa=[];bb=[];cc=[]
    for c,d,a,b in alts:
        pc=1-c/C if C else 0.;pd=1-d/D if D else 0.;pu=1-(a+b)/U;cross=(r-b)/U
        ar=[];br=[];cr=[]
        for g in groups:
            if g[0]=='s':
                k=g[1]
                if k==0:A,B,E=pc,0.,0.
                elif k==1:A,B,E=pd,-2*mu*pd,mu*mu
                elif k==2:A,B,E=pu,-2*mu*cross,mu*mu/2
                else:A,B,E=1.,-2*mu,mu*mu
            else:
                _,s,t,u,h=g;ex=t+u/2;ey=s*pc+t*pd+u*pu
                vx=hypervar(U,u,.5)
                vy=hypervar(C,s,pc)+hypervar(D,t,pd)+hypervar(U,u,pu)
                cov=u*(U-u)/(U-1)*(cross-.5*pu)
                alpha=lam*ex-ey+mu*h;beta=ey-h
                A=beta*beta+vy;B=2*alpha*beta-2*vy+2*lam*cov
                E=alpha*alpha+lam*lam*vx+vy-2*lam*cov
            ar.append(A);br.append(B);cr.append(E)
        aa.append(ar);bb.append(br);cc.append(cr)
    return np.array(aa),np.array(bb),np.array(cc),groups

def solve(q,r,mu,gamma,tol=3e-9):
    aa,bb,cc,groups=arrays(q,r,mu);Q=len(groups)
    cuts=[*(cc/2),*((aa*mu*mu+bb*mu+cc)/2),*((aa+bb+cc)/2)]
    for it in range(80):
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
    return dict(common_lower=lo,common_upper=hi,regret_lower=gamma-hi,regret_upper=gamma-lo,
                converged=hi-lo<=tol,iterations=it+1,query_orbits=Q,alternative_orbits=len(aa),
                active_queries=[dict(orbit=g,weight=float(z)) for g,z in zip(groups,w) if z>1e-6])

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--q',type=int,nargs='+',default=[4,8,16])
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/unresolved_label_family.json'))
    args=ap.parse_args();rows=[];checks=[]
    for q in args.q:
        p=phase_parameters(q)
        for r in sorted({1,max(1,q//4),q//2,q}):
            for side in [-1,0,1]:
                mu=p['mu_U']+side*.1*(p['mu_H']-p['mu_U']);gamma=information(q,mu,oracle(q,mu,p))[0]
                row=dict(q=q,unresolved_per_label=r,unresolved_coordinates=2*r,mu=mu,side=side,
                         known_B_core=q-r,oracle=gamma,**solve(q,r,mu,gamma))
                if q==args.q[0] and r==1:
                    ref=pair_solve(q,mu,gamma)
                    error=abs(row['common_upper']-ref['common_value_upper'])
                    assert error<1e-7,(row,ref)
                    checks.append(dict(q=q,side=side,pair_crosscheck_error=error))
                row['relative_regret_lower']=row['regret_lower']/gamma
                rows.append(row);print({k:row[k] for k in ['q','unresolved_per_label','side','relative_regret_lower','converged']},flush=True)
                args.out.write_text(json.dumps(dict(evidence_class='UNRESOLVED_LABEL_FAMILY_COMMON_ALLOCATION',
                    script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,pair_crosschecks=checks,
                    scope=['All legal query and hidden-alternative orbits retained; continuous nuisance separation.',
                           'Uniformly supplied known cores; discovery of these cores is not charged here.',
                           'Floating-point primal/dual bounds, not exact formal certificates.',
                           'Common allocation only; does not lower-bound an adaptive algorithm that resolves labels.']),indent=2)+'\n')
if __name__=='__main__':main()
