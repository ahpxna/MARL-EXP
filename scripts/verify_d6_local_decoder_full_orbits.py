#!/usr/bin/env python3
"""Check whether the local ambiguity deficit is an eight-orbit artifact.
All legal query orbits for the adjacent-label pair are retained here.
"""
import json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.optimize import linprog
from scipy.special import ndtr
from experiment_d6_decoder_orbits import arrays
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information


def solve(q,mu,gamma,tol=2e-9,maxiter=60):
    aa,bb,cc,groups=arrays(q,mu);Q=len(groups)
    constraints=[*(cc/2),*((aa*mu**2+bb*mu+cc)/2),*((aa+bb+cc)/2)]
    for it in range(maxiter):
        mat=np.asarray(constraints)
        res=linprog([0.]*Q+[-1.],A_ub=np.column_stack([-mat,np.ones(len(mat))]),b_ub=np.zeros(len(mat)),
            A_eq=np.array([[1.]*Q+[0.]]),b_eq=[1.],bounds=[(0,None)]*Q+[(0,gamma)],method='highs',
            options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        if not res.success:raise RuntimeError(res.message)
        w=res.x[:-1];a=aa@w;b=bb@w;c=cc@w
        nu=np.clip(np.divide(-b,2*a,out=np.zeros_like(b),where=a>0),0,1)
        vals=(a*nu**2+b*nu+c)/2;lo=float(vals.min());hi=float(res.x[-1]);bad=np.flatnonzero(vals<hi-tol)
        if hi-lo<=tol:break
        constraints.extend((aa[bad]*nu[bad,None]**2+bb[bad]*nu[bad,None]+cc[bad])/2)
    return dict(common_value_lower=lo,common_value_upper=hi,gap_lower=gamma-hi,gap_upper=gamma-lo,
                converged=hi-lo<=tol,iterations=it+1,query_orbits=Q)


def main():
    rows=[];out=Path('research/d6_phase_boundary_20260908/local_decoder_full_orbits.json')
    for q in [8,16,32]:
        p=phase_parameters(q)
        for ratio in [128,8192]:
            N=q*ratio;eps=1/(q*np.sqrt(N));leading=p['slope_jump']*eps*ndtr(-1.)
            for side in [-1,1]:
                mu=p['mu_U']+side*eps;gamma=information(q,mu,oracle(q,mu,p))[0]
                row=dict(q=q,N=N,budget_per_q=ratio,side=side,epsilon=eps,known_A_leading=leading,
                         **solve(q,mu,gamma))
                row['gap_lower_over_leading']=row['gap_lower']/leading
                row['gap_upper_over_leading']=row['gap_upper']/leading
                rows.append(row);print({k:row[k] for k in ['q','budget_per_q','side','gap_lower_over_leading','gap_upper_over_leading','converged']},flush=True)
                out.write_text(json.dumps(dict(evidence_class='FULL_QUERY_ORBIT_LOCAL_LABEL_AMBIGUITY',
                    script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
                    scope=['Numerical primal/dual sandwich for the common-allocation problem.',
                           'Entire actual legal query orbit library and every hidden-alternative orbit.',
                           'Continuous nuisance separation oracle; no universal-q or global-decoder proof.']),indent=2)+'\n')
if __name__=='__main__':main()
