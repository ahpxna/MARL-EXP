#!/usr/bin/env python3
"""Local D6 allocation-risk bounds and finite-budget evidence, known A.

For mu=mu_U +/- epsilon, estimate the side from N actual B-off Gaussian
samples; recommend the corresponding frozen boundary allocation. Computes
actual all-distance, continuous-nuisance information losses. Gaussian sample
means are sampled directly, exactly equivalent to N independent measurements.
Also evaluates a lower bound against every allocation using the COMMON
adjacent-world dual at the boundary, not an optimizer restricted to 3 orbits.
The phase-III certificate and probabilistic comparison are analytic proposals,
not claimed Lean-proved by this experiment. No end-to-end stopping claim.
"""
import argparse,json
from hashlib import sha256
from pathlib import Path
import numpy as np
from scipy.special import ndtr
from scipy.stats import norm
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information,binomial_interval


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--q',type=int,nargs='+',default=[3,4,5])
    ap.add_argument('--epsilons',type=float,nargs='+',default=[.008,.002,.0005,.000125,1e-5])
    ap.add_argument('--scaled-budgets',type=float,nargs='+',default=[0,.0625,.25,1,4])
    ap.add_argument('--seeds',type=int,default=50000)
    ap.add_argument('--seed',type=int,default=20260909)
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/local_allocation_risk.json'))
    args=ap.parse_args()
    assert args.seeds>=2 and all(q>=3 for q in args.q) and all(e>0 for e in args.epsilons)
    rows=[];raw={};param=[]
    for q in args.q:
        p=phase_parameters(q);param.append(p)
        left=np.array([1-p['left_Bon_weight'],0,p['left_Bon_weight']])
        right=np.array([0,1-p['right_Bon_weight'],p['right_Bon_weight']])
        for ei,eps in enumerate(args.epsilons):
            assert eps<min(p['mu_U']-p['mu_L'],p['mu_H']-p['mu_U'])
            mus=[p['mu_U']-eps,p['mu_U']+eps]
            gammas=np.array([information(q,mu,oracle(q,mu,p))[0] for mu in mus])
            risks=np.array([[gammas[i]-information(q,mu,w)[0] for w in (left,right)] for i,mu in enumerate(mus)])
            assert risks.min()>-1e-12
            # A common valid dual at mu_U has average information <= Gamma0.
            # Its midpoint second difference is epsilon² * average squared slope
            # <= epsilon²*q², for EVERY legal allocation.
            separation=max(0.,float(sum(gammas)-2*p['gamma_boundary']-q*q*eps*eps))
            for bi,scaled in enumerate(args.scaled_budgets):
                N=int(np.ceil(scaled/(q*q*eps*eps))) if scaled else 0
                a=q*eps*np.sqrt(N);error=float(ndtr(-a))
                lower=separation*error
                leading=p['slope_jump']*eps*error
                exact_risks=np.array([(1-error)*risks[0,0]+error*risks[0,1],
                                     error*risks[1,0]+(1-error)*risks[1,1]])
                assert lower<=exact_risks.max()+1e-10
                empirical=[]
                for si,side in enumerate((-1,1)):
                    rng=np.random.default_rng(np.random.SeedSequence([args.seed,q,ei,bi,si]))
                    # Z + side*q*eps*sqrt(N) is the sign statistic for B-off.
                    # At N=0 this is a fair randomized decision with no observation.
                    choices=(rng.standard_normal(args.seeds)+side*a>0).astype(np.int8)
                    losses=risks[si,choices]
                    errors=int(np.sum(choices!=(side==1)))
                    empirical.append(dict(side=side,errors=errors,error_rate=errors/args.seeds,
                        error_interval_95=binomial_interval(errors,args.seeds),
                        mean_regret=float(losses.mean()),se_mean_regret=float(losses.std(ddof=1)/np.sqrt(args.seeds))))
                    raw[f'q{q}_e{ei}_b{bi}_s{si}']=choices
                rows.append(dict(q=q,epsilon=eps,N=N,scaled_budget_actual=q*q*eps*eps*N,
                    gaussian_error_exact=error,global_allocation_risk_lower=lower,
                    exact_achievable_worst_risk=float(exact_risks.max()),local_matching_leading=leading,
                    upper_over_leading=float(exact_risks.max()/leading),
                    lower_over_leading=float(lower/leading),
                    frozen_design_regrets=risks.tolist(),common_dual_regret_separation=separation,
                    empirical=empirical))
        print(f'q={q}: {len(args.epsilons)*len(args.scaled_budgets)*2*args.seeds} Gaussian recommendations checked.',flush=True)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    npz=args.out.with_suffix('.npz');np.savez_compressed(npz,**raw)
    dependency=Path(__file__).with_name('experiment_d6_phase_boundary_cost.py')
    result=dict(evidence_class='LOCAL_KNOWN_LABEL_ALLOCATION_RISK_MATCHING_BOUNDS_NUMERICAL',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        dependency_sha256=sha256(dependency.read_bytes()).hexdigest(),
        configuration=dict(q=args.q,epsilons=args.epsilons,scaled_budgets=args.scaled_budgets,seeds=args.seeds,seed=args.seed),
        parameters=param,rows=rows,raw_trials=str(npz),raw_sha256=sha256(npz.read_bytes()).hexdigest(),
        local_target='J_q*epsilon*Phi(-q*epsilon*sqrt(N)) + O_q(epsilon^2)',
        exact_lower_expression='max(0,Gamma_minus+Gamma_plus-2*Gamma_boundary-q^2*epsilon^2)*Phi(-q*epsilon*sqrt(N))',
        scope=['Known A; full legal query library for lower-bound comparison.',
        'Finite deterministic sample budget N, then one allocation recommendation.',
        'Same fixed-candidate actual-world information functional with full continuous nuisance.',
        'No inference of an unavoidable phase-pretest in geometric identification.',
        'Numerical four-phase oracle formula, not a proof of phase III.',
        'Global bound uses boundary dual and max slope q, not optimization over restricted allocation family.'])
    args.out.write_text(json.dumps(result,indent=2)+'\n');print(args.out,flush=True)

if __name__=='__main__':main()
