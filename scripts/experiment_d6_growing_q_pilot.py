#!/usr/bin/env python3
"""Growing-q diagnostic for a concrete unknown-A pilot, not a minimax discovery theorem.

The pilot observes every non-j scalar r times, ranks sample means, and selects
q+1 coordinates. Exact pairwise Gaussian union bound calibrates r uniformly on
a supplied local margin interval. Every pilot measurement is charged to N.
Conditional on correct A, remaining observations are actual B-off samples.
Reported failure contribution is a rigorous envelope Gamma*P(pilot failure),
not a fabricated exact regret when the returned label is wrong. The oracle
phase formulas remain numerical proposals. No stopping-time claim.
"""
import argparse,json
from pathlib import Path
from hashlib import sha256
import numpy as np
from scipy.special import ndtr,ndtri
from experiment_d6_phase_boundary_cost import phase_parameters,oracle,information,binomial_interval


def pilot_errors(q,mu,r,seeds,seed):
    rng=np.random.default_rng(seed); wrong=0
    for start in range(0,seeds,250):
        size=min(250,seeds-start)
        # Actual scalar means: 1 on A (q+1 coordinates), 1-mu on B (q coordinates).
        amin=1+rng.normal(size=(size,q+1)).min(axis=1)/np.sqrt(r)
        bmax=1-mu+rng.normal(size=(size,q)).max(axis=1)/np.sqrt(r)
        wrong+=int(np.sum(bmax>=amin))
    return wrong


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--q',type=int,nargs='+',default=[4,16,64,256,1024])
    ap.add_argument('--budget-per-q',type=int,nargs='+',default=[128,512,2048,8192,32768])
    ap.add_argument('--seeds',type=int,default=5000)
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/growing_q_pilot.json'))
    args=ap.parse_args(); rows=[]
    for q in args.q:
        p=phase_parameters(q); width=p['mu_H']-p['mu_U']
        for ratio in args.budget_per_q:
            N=q*ratio; eps=1/(q*np.sqrt(N)); eta=1/(q*N)
            assert eps<width and p['mu_U']-eps>.5
            # The subproblem supplies this interval, but not the true A or true side.
            mu_min=p['mu_U']-eps
            pairs=q*(q+1)
            r=int(np.ceil(2*(ndtri(eta/pairs)/mu_min)**2))
            pilot=(2*q+1)*r; remain=max(0,N-pilot)
            err_known=float(ndtr(-q*eps*np.sqrt(N)))
            err_after=float(ndtr(-q*eps*np.sqrt(remain)))
            left=(1-p['left_Bon_weight'],0,p['left_Bon_weight'])
            right=(0,1-p['right_Bon_weight'],p['right_Bon_weight'])
            side_results=[]
            for si,side in enumerate([-1,1]):
                mu=p['mu_U']+side*eps
                gamma=information(q,mu,oracle(q,mu,p))[0]
                regrets=[gamma-information(q,mu,w)[0] for w in [left,right]]
                conditional=(1-err_after)*regrets[si]+err_after*regrets[1-si]
                union=min(1.,pairs*float(ndtr(-mu*np.sqrt(r/2))))
                errors=pilot_errors(q,mu,r,args.seeds,np.random.SeedSequence([20260909,q,ratio,si]))
                # Nonnegative information gives r_mu(w)<=Gamma(mu) for every legal design.
                side_results.append(dict(side=side,pilot_errors=errors,seeds=args.seeds,
                    pilot_error_interval_95=binomial_interval(errors,args.seeds),
                    pilot_error_union_bound=union,
                    conditional_correct_label_risk=conditional if pilot<N else None,
                    achievable_risk_upper=conditional+gamma*union if pilot<N else None))
            known_gammas=[information(q,p['mu_U']+s*eps,oracle(q,p['mu_U']+s*eps,p))[0] for s in [-1,1]]
            separation=max(0.,sum(known_gammas)-2*p['gamma_boundary']-q*q*eps*eps)
            rows.append(dict(q=q,N=N,budget_per_q=ratio,epsilon=eps,phaseIII_width=width,
                epsilon_over_phaseIII_width=eps/width,pilot_repeats=r,pilot_samples=pilot,
                pilot_fraction=pilot/N,pilot_fits=pilot<N,remaining_samples=remain,
                known_label_error=err_known,correct_label_phase_error_after_pilot=err_after,
                leading=p['slope_jump']*eps*err_known,
                coarse_separation_over_Jepsilon=separation/(p['slope_jump']*eps),
                width_times_q32=width*q**1.5,J_times_sqrtq=p['slope_jump']*np.sqrt(q),
                sides=side_results))
        print(f'q={q}: pilot samples and actual Gaussian ranking checked',flush=True)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    result=dict(evidence_class='GROWING_Q_CONCRETE_UNKNOWN_LABEL_PILOT_DIAGNOSTIC',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        dependency_sha256=sha256(Path(__file__).with_name('experiment_d6_phase_boundary_cost.py').read_bytes()).hexdigest(),
        configuration=vars(args)|{'out':str(args.out)},rows=rows,
        scope=['All pilot queries charged to the deterministic budget.',
        'Known local interval and boundary; unknown A and unknown side.',
        'Monte Carlo measures exact-label recovery of the scalar pilot, not final geometric stopping.',
        'Pilot overflow is flagged; no achievement claimed in those cells.',
        'q*log(q*N)=o(N) is sufficient for this pilot overhead to vanish; no matching label-discovery lower bound.',
        'Fixed-q O_q(epsilon^2) does not establish a uniform growing-q matching theorem.',
        'The coarse q^2*epsilon^2 regret correction may become vacuous for large q.'])
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(args.out,flush=True)

if __name__=='__main__':main()
