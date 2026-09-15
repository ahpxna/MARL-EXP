#!/usr/bin/env python3
"""Symmetry reduction of the adjacent-label common-allocation experiment.

Coordinates form C=A intersect A' (q), a=A\A' (1), b=A'\A (1),
D=outside both and j (q-1), and j (1). Hypergeometric second moments
average over actual queries within each orbit. Every hidden alternative orbit
is retained and its nuisance is minimized continuously by cutting planes.
Symmetry reduction is analytic; the LP remains floating-point evidence.
"""
import argparse,itertools,json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.optimize import linprog
from experiment_d6_phase_boundary_cost import phase_parameters


def arrays(q,mu):
    alts=[(c,d,a,b) for c in range(q+1) for d in range(q) for a in [0,1] for b in [0,1] if c+d+a+b==q+1]
    groups=[('s',i) for i in range(5)]
    groups += [('g',s,t,a,b,h) for s in range(q+1) for t in range(q) for a in [0,1] for b in [0,1] for h in [0,1]
        if s+t+a+b<=q and (h or s+t+a+b>=2)]
    truealts=[(q,0,1,0),(q,0,0,1)];rows=[]
    for true in truealts:
        truthisA=(true[2]==1)
        for c,d,a,b in alts:
            if (c,d,a,b)==true:continue
            probs=[1-c/q,1-a,1-b,1-d/(q-1),None]
            ca=[];cb=[];cc=[]
            for group in groups:
                if group[0]=='s':
                    orbit=group[1]
                    if orbit==4: aa=1.;bb=-2*mu;co=mu*mu
                    else:
                        trueB=[False,not truthisA,truthisA,True][orbit]
                        gap=-mu if trueB else 0.;p=probs[orbit]
                        aa=p;bb=2*gap*p;co=gap*gap
                else:
                    _,s,t,ga,gb,h=group
                    expectation=s*probs[0]+t*probs[3]+ga*probs[1]+gb*probs[2]-h
                    variance=s*probs[0]*(1-probs[0])*(q-s)/(q-1)+t*probs[3]*(1-probs[3])*(q-1-t)/(q-2)
                    trueB=t+(gb if truthisA else ga);truemean=(1-mu)*(trueB-h)
                    aa=expectation**2+variance;bb=2*truemean*expectation-2*aa;co=truemean**2-2*truemean*expectation+aa
                ca.append(aa);cb.append(bb);cc.append(co)
            rows.append((ca,cb,cc))
    return np.array([r[0] for r in rows]),np.array([r[1] for r in rows]),np.array([r[2] for r in rows]),groups


def solve(q,tol,max_iter):
    p=phase_parameters(q);mu=p['mu_U'];aa,bb,cc,groups=arrays(q,mu);Q=len(groups)
    constraints=[*(cc/2),*((aa*mu**2+bb*mu+cc)/2),*((aa+bb+cc)/2)]
    objective=np.zeros(Q+1);objective[-1]=-1;trace=[]
    for iteration in range(max_iter):
        matrix=np.asarray(constraints)
        opt=linprog(objective,A_ub=np.column_stack([-matrix,np.ones(len(matrix))]),b_ub=np.zeros(len(matrix)),
            A_eq=np.array([[*np.ones(Q),0.]]),b_eq=[1.],bounds=[(0,None)]*Q+[(None,None)],method='highs',
            options={'dual_feasibility_tolerance':1e-9,'primal_feasibility_tolerance':1e-9})
        if not opt.success:raise RuntimeError(opt.message)
        w=opt.x[:-1];upper=float(opt.x[-1]);a=aa@w;b=bb@w;c=cc@w
        nu=np.clip(np.divide(-b,2*a,out=np.zeros_like(b),where=a>0),0,1)
        val=(a*nu**2+b*nu+c)/2;lower=float(val.min());bad=np.flatnonzero(val<upper-tol)
        trace.append(dict(lower=lower,upper=upper,added=len(bad)))
        if upper-lower<=tol:break
        constraints.extend((aa[bad]*nu[bad,None]**2+bb[bad]*nu[bad,None]+cc[bad])/2)
    gamma=p['gamma_boundary'];gap=gamma-upper
    return dict(q=q,mu=mu,gamma=gamma,query_orbits=Q,alternative_orbits=len(aa),
        common_value_lower=lower,common_value_upper=upper,decoder_gap_lower=gap,decoder_gap_upper=gamma-lower,
        q2_gap=q*q*gap,q25_gap=q**2.5*gap,q3_gap=q**3*gap,converged=upper-lower<=tol,
        iterations=len(trace),trace=trace,active_query_orbits=[dict(orbit=g,weight=float(x)) for g,x in zip(groups,w) if x>1e-7])


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--q',nargs='+',type=int,default=[3,4,5,8,12,16])
    ap.add_argument('--tolerance',type=float,default=2e-9);ap.add_argument('--max-iter',type=int,default=70)
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/decoder_orbits.json'))
    args=ap.parse_args();rows=[]
    for q in args.q:
        row=solve(q,args.tolerance,args.max_iter)
        if q==3: assert abs(row['common_value_upper']-0.0565272872130524)<3e-8
        if q==4: assert abs(row['common_value_upper']-0.04936037264722778)<3e-8
        rows.append(row)
        print({k:row[k] for k in ['q','decoder_gap_lower','q2_gap','q25_gap','q3_gap','converged','iterations']},flush=True)
        args.out.write_text(json.dumps(dict(evidence_class='GROWING_Q_ADJACENT_LABEL_ORBIT_LP',
            script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
            scope=['Analytic hypergeometric orbit averaging; full-query q=3,4 agreement checked.',
                   'Pairwise adjacent-label result only; no entire-family decoder theorem.',
                   'Floating-point bounds, not formal certificates.']),indent=2)+'\n')
if __name__=='__main__':main()
