#!/usr/bin/env python3
"""An explicit eight-orbit allocation tolerating one unresolved label swap.

This restricts the learner, so the attained feasible value gives an UPPER
bound on the regret needed to leave one adjacent pair unresolved. It does not
prove that no unrestricted design does better. All competing hidden-set
orbits and continuous nuisance values are retained. LP values are scaled by q
for conditioning. No extra observations or true-side information are supplied.
"""
import argparse,json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.optimize import linprog
from experiment_d6_phase_boundary_cost import phase_parameters


def coefficients(q,mu):
    groups=[('s',1),('s',2),('s',3),('g',0,q-2,1,1,0),('g',0,q-1,0,1,0),
            ('g',0,q-1,1,0,0),('g',q,0,0,0,0),('g',q,0,0,0,1)]
    alts=[(q+1-d-a-b,d,a,b) for d in range(q) for a in [0,1] for b in [0,1] if 0<=q+1-d-a-b<=q]
    rows=[]
    for trueA in [True,False]:
        true=(q,0,1,0) if trueA else (q,0,0,1)
        for c,d,a,b in alts:
            if (c,d,a,b)==true:continue
            probs=[1-c/q,1-a,1-b,1-d/(q-1)];row=[]
            for group in groups:
                if group[0]=='s':
                    o=group[1]; gap=-mu if [False,not trueA,trueA,True][o] else 0.;p=probs[o]
                    alpha=gap;beta=p;variance=p*(1-p);v0=0.;v1=1.
                else:
                    _,s,t,ga,gb,h=group
                    m=s*probs[0]+t*probs[3]+ga*probs[1]+gb*probs[2]-h
                    var=s*probs[0]*(1-probs[0])*(q-s)/(q-1)+t*probs[3]*(1-probs[3])*(q-1-t)/(q-2)
                    y=(1-mu)*(t+(gb if trueA else ga)-h)
                    alpha=y-m;beta=m;variance=var;v0=1.;v1=-1.
                row.append((alpha,beta,variance,v0,v1))
            rows.append(row)
    arr=np.asarray(rows,dtype=np.longdouble)
    alpha,beta,variance,v0,v1=(arr[:,:,i] for i in range(5))
    aa=(beta*beta+variance*v1*v1)*q/2
    bb=2*(alpha*beta+variance*v0*v1)*q/2
    cc=(alpha*alpha+variance*v0*v0)*q/2
    def stable(nu):
        nu=np.asarray(nu,dtype=np.longdouble)
        if nu.ndim:nu=nu[:,None]
        return ((alpha+beta*nu)**2+variance*(v0+v1*nu)**2)*q/2
    return aa,bb,cc,groups,stable


def solve(q,tol,max_iter):
    p=phase_parameters(q);mu=p['mu_U'];aa,bb,cc,groups,stable=coefficients(q,mu)
    constraints=[*stable(mu)];trace=[]
    for iteration in range(max_iter):
        matrix=np.asarray(constraints)
        res=linprog([0.]*8+[-1.],A_ub=np.column_stack([-matrix,np.ones(len(matrix))]),b_ub=np.zeros(len(matrix)),
            A_eq=np.array([[1.]*8+[0.]]),b_eq=[1.],bounds=[(0,None)]*8+[(0,q*p['gamma_boundary'])],method='highs',
            options={'dual_feasibility_tolerance':1e-10,'primal_feasibility_tolerance':1e-10})
        if not res.success:raise RuntimeError(res.message)
        w=res.x[:-1];a=aa@w;b=bb@w;c=cc@w
        nu=np.clip(np.divide(-b,2*a,out=np.zeros_like(b),where=a>0),0,1)
        cutrows=stable(nu);vals=cutrows@w;lo=float(vals.min());hi=float(res.x[-1]);bad=np.flatnonzero(vals<hi-tol)
        trace.append(dict(value_lower=lo/q,value_upper=hi/q,added=len(bad)))
        if hi-lo<=tol:break
        constraints.extend(cutrows[bad])
    gamma=p['gamma_boundary'];gap=gamma-lo/q
    return dict(q=q,mu=mu,gamma=gamma,feasible_common_value=lo/q,restricted_value_upper=hi/q,
        ambiguity_regret_upper=gap,q2_regret_upper=q*q*gap,q25_regret_upper=q**2.5*gap,q3_regret_upper=q**3*gap,
        converged=hi-lo<=tol,iterations=len(trace),scaled_tolerance=tol,
        phase_jump=p['slope_jump'],weights=[dict(orbit=g,weight=float(x)) for g,x in zip(groups,w)],trace=trace)


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--q',type=int,nargs='+',default=[4,16,64,256,1024])
    ap.add_argument('--tolerance',type=float,default=2e-10);ap.add_argument('--max-iter',type=int,default=60)
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/ambiguous_pair_design.json'))
    args=ap.parse_args();rows=[]
    for q in args.q:
        row=solve(q,args.tolerance,args.max_iter)
        if q==4:assert abs(row['ambiguity_regret_upper']-.003431369)<5e-8
        if q==16:assert abs(row['ambiguity_regret_upper']-8.7243e-5)<5e-8
        rows.append(row);print({k:row[k] for k in ['q','ambiguity_regret_upper','q2_regret_upper','q25_regret_upper','q3_regret_upper','converged','iterations']},flush=True)
        args.out.write_text(json.dumps(dict(evidence_class='EIGHT_ORBIT_DESIGN_WITH_ONE_UNRESOLVED_SWAP',
            script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
            scope=['Feasible design evidence, not a lower bound over unrestricted allocations.',
                   'Common core and ambiguous pair supplied; full unknown-label discovery is not simulated.',
                   'Full hidden-alternative orbits and continuous nuisance retained.',
                   'Positive-square evaluation in extended precision avoids cancellation; LP remains floating point.',
                   'Asymptotic power laws are hypotheses until proved uniformly in q.']),indent=2)+'\n')
if __name__=='__main__':main()
