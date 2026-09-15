#!/usr/bin/env python3
"""Cost of one unresolved swap on BOTH sides of the allocation boundary.

Evaluates a feasible common allocation for each side, and a Gaussian test from
shared D-off (slope q-1). The common core plus the ambiguous pair are supplied;
this does not implement their discovery. Restricted-orbit LP gives attainable
allocation values, not minimax lower bounds. Keeps the exact continuous
nuisance and all alternative orbits, with positive-square evaluation.
"""
import json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.optimize import linprog
from scipy.special import ndtr
from experiment_d6_ambiguous_pair_design import coefficients
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information


def solve_at(q,mu,gamma,tol=2e-10,maxiter=60):
    aa,bb,cc,groups,stable=coefficients(q,mu);constraints=[*stable(mu)]
    for it in range(maxiter):
        mat=np.asarray(constraints)
        res=linprog([0.]*8+[-1.],A_ub=np.column_stack([-mat,np.ones(len(mat))]),b_ub=np.zeros(len(mat)),
            A_eq=np.array([[1.]*8+[0.]]),b_eq=[1.],bounds=[(0,None)]*8+[(0,q*gamma)],method='highs',
            options={'dual_feasibility_tolerance':1e-10,'primal_feasibility_tolerance':1e-10})
        if not res.success:raise RuntimeError(res.message)
        w=res.x[:-1];a=aa@w;b=bb@w
        nu=np.clip(np.divide(-b,2*a,out=np.zeros_like(b),where=a>0),0,1)
        cuts=stable(nu);val=cuts@w;low=float(val.min());high=float(res.x[-1]);bad=np.flatnonzero(val<high-tol)
        if high-low<=tol:break
        constraints.extend(cuts[bad])
    return w,float(low/q),high-low<=tol


def value(q,mu,w):
    aa,bb,cc,groups,stable=coefficients(q,mu);a=aa@w;b=bb@w
    nu=np.clip(np.divide(-b,2*a,out=np.zeros_like(b),where=a>0),0,1)
    return float((stable(nu)@w).min()/q)


def main():
    rows=[];out=Path('research/d6_phase_boundary_20260908/partial_label_local_risk.json')
    for q in [16,64,256,1024]:
        p=phase_parameters(q)
        for ratio in [128,8192,1048576]:
            N=q*ratio;eps=1/(q*np.sqrt(N));mu=[p['mu_U']-eps,p['mu_U']+eps]
            gamma=[information(q,u,oracle(q,u,p))[0] for u in mu]
            results=[solve_at(q,u,g) for u,g in zip(mu,gamma)];weights=[r[0] for r in results]
            regrets=[[gamma[s]-value(q,mu[s],weights[k]) for k in range(2)] for s in range(2)]
            error=float(ndtr(-(q-1)*eps*np.sqrt(N)))
            risks=[(1-error)*regrets[s][s]+error*regrets[s][1-s] for s in range(2)]
            leading=p['slope_jump']*eps*float(ndtr(-q*eps*np.sqrt(N)))
            row=dict(q=q,N=N,budget_per_q=ratio,epsilon=eps,
                correct_phase_ambiguity_regret=[regrets[s][s] for s in range(2)],
                correct_phase_ambiguity_over_leading=[regrets[s][s]/leading for s in range(2)],
                crossed_regrets=regrets,common_core_phase_error=error,
                achievable_worst_risk=max(risks),risk_over_known_A_leading=max(risks)/leading,
                known_A_leading=leading,converged=all(r[2] for r in results))
            rows.append(row);print({k:row[k] for k in ['q','budget_per_q','correct_phase_ambiguity_over_leading','risk_over_known_A_leading','converged']},flush=True)
            out.write_text(json.dumps(dict(evidence_class='LOCAL_PHASE_RISK_WITH_ONE_UNRESOLVED_LABEL_SWAP',
                script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                dependency_sha256=sha256(Path(__file__).with_name('experiment_d6_ambiguous_pair_design.py').read_bytes()).hexdigest(),
                rows=rows,scope=['Common B core D and one ambiguous pair are supplied; their discovery cost is not charged.',
                'Gaussian phase test uses N actual legal D-off queries with sensitivity q-1.',
                'For each tested margin, every alternative label orbit and continuous nuisance is evaluated.',
                'All reported values are numerical feasible-design evidence, not a uniform-q theorem.']),indent=2)+'\n')
if __name__=='__main__':main()
