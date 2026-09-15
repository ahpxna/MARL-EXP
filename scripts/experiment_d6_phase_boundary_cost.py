#!/usr/bin/env python3
"""Evidence for phase learning near the D6 allocation boundary.

Separate tasks:
(1) Full sign classification, unknown gap, known world label A. Observe the
actual legal B-off query. Gaussian increments are aggregated exactly between
geometrically spaced looks; no diffusion approximation or continuous-monitor
shortcut. Bonferroni spending gives uniform sign error <= alpha. The true
boundary is excluded from the required termination set.
(2) Exact continuous-nuisance quadratic minimization of three query-orbit
allocations, cross-checked against actual world tables. This is numerical
algebraic evidence, not a formal proof or an adaptive stopping experiment.
No claim that phase-classification cost is compulsory for finding A.
"""
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import numpy as np
from scipy.special import ndtri
from scipy.stats import beta
from scipy.optimize import minimize_scalar
from verify_d6_information_limit_bridge import family_world, masks


def phase_parameters(q):
    c=np.sqrt(q/(q+1)); z=(1-c)/(q-2+c); T=1+z
    R=np.sqrt((q*q+2*q*q*z+z*z)/(q+1)); mu0=R/(1+R)
    lam=1-mu0; K=q*(q-2)**2-q+1
    D=np.sqrt(q*(q-1)*lam*lam+K*mu0*mu0)
    shift=(q*lam*lam-mu0*mu0)/(q*(q-2)*lam+D)
    left=c/(q-2+c); right=(q-1)*shift/D
    V=c*c*T*T
    slopeL=-lam*V
    sB=-(q-1)*(lam*(q-1)-(q-2)*lam*T)
    sQ=(mu0+(q-1)*lam*z)/q
    slopeR=right*sB+(1-right)*sQ
    return dict(q=q,mu_L=(1-c)/(q-1),mu_U=mu0,mu_H=np.sqrt(q)/(1+np.sqrt(q)),
        c=c,z=z,T=T,left_Bon_weight=left,right_Bon_weight=right,
        gamma_boundary=lam*lam*V/2,slope_left=slopeL,slope_right=slopeR,
        slope_jump=slopeR-slopeL)


def oracle(q,mu,p):
    lam=1-mu
    if mu <= p['mu_L']: return (0.,0.,1.)
    if mu <= p['mu_U']: return (1-p['left_Bon_weight'],0.,p['left_Bon_weight'])
    if mu >= p['mu_H']: return (0.,1.,0.)
    D=np.sqrt(q*(q-1)*lam*lam+(q*(q-2)**2-q+1)*mu*mu)
    shift=(q*lam*lam-mu*mu)/(q*(q-2)*lam+D)
    w=(q-1)*shift/D
    return (0.,1-w,w)


def quadratic_min(a,b,c):
    u=np.clip(-b/(2*a),0,1) if a>0 else (1. if b<0 else 0.)
    return (a*u*u+b*u+c)/2, float(u)


def information(q,mu,weights):
    x,y,w=weights; lam=1-mu; results=[]
    for d in range(1,q+1):
        t=q-d-1
        aa=x*d*(d*(q-1)+1)/(q+1)+y*(q-d)/q+w*t*t
        bb=-2*y*(q-d)*lam/q-2*w*lam*(q-1)*t
        cc=y*(d*mu*mu+(q-d)*lam*lam)/q+w*lam*lam*(q-1)**2
        v,u=quadratic_min(aa,bb,cc); results.append((v,d,u))
    return min(results)


def actual_table_crosscheck(q):
    m=2*(q+1); k=q+1; A=(1<<k)-1; j=1<<k; B=((1<<m)-1)^A^j
    aa=[A^(1<<i) for i in range(k)]
    bb=[1<<i for i in range(m) if (1<<i)&B]
    queries=aa+bb+[B|j]
    # Rational margins and rational weights, independent endpoint tables.
    tested=0; discrepancy=0.
    for mu in (Fraction(3,5),Fraction(13,20),Fraction(2,3)):
        truth=np.array(family_world(m,mu,A),float)/mu.denominator
        for weights in ((Fraction(2,3),0,Fraction(1,3)),(0,Fraction(49,50),Fraction(1,50)),
                        (Fraction(1,3),Fraction(1,2),Fraction(1,6))):
            x,y,w=map(float,weights); mass=np.array([x/k]*k+[y/q]*q+[w])
            worst=float('inf')
            for alt in masks(m,k):
                if alt&j or alt==A: continue
                f0=np.array(family_world(m,Fraction(1),alt),float)[queries]
                f1=np.array(family_world(m,Fraction(0),alt),float)[queries]
                v=f1-f0; diff=f0-truth[queries]
                coeff=(float(mass@(v*v)),float(2*mass@(diff*v)),float(mass@(diff*diff)))
                value,_=quadratic_min(*coeff)
                d=(alt^A).bit_count()//2
                worst=min(worst,value); tested+=1
            expected=information(q,float(mu),(x,y,w))[0]
            discrepancy=max(discrepancy,abs(worst-expected))
            assert abs(worst-expected)<1e-10
    # Sharp phase KL slope: all legal query derivatives bounded by q, attained B-off.
    f0=np.array(family_world(m,Fraction(1),A),float)
    f1=np.array(family_world(m,Fraction(0),A),float)
    groups=[g for g in range(1<<m) if not g&j and g.bit_count()<=q]
    legal=[1<<i for i in range(m)]+[g|j for g in groups]+[g for g in groups if g.bit_count()>=2]
    assert np.max(np.abs((f1-f0)[legal]))==q
    assert f1[B]-f0[B]==q
    return dict(q=q,actual_alternative_quadratics=tested,max_discrepancy=discrepancy,
        maximum_legal_margin_slope=q,attaining_query='B-off')


def binomial_interval(errors,n):
    return [float(beta.ppf(.025,errors,n-errors+1)) if errors else 0.,
            float(beta.ppf(.975,errors+1,n-errors)) if errors<n else 1.]


def phase_trials(q,epsilon,alpha,side,seeds,seed,look_ratio,max_looks):
    # X = [1+q*(1-mu_U)] - Y_Boff. Exact mean = q*(mu-mu_U).
    theta=side*q*epsilon
    rng=np.random.default_rng(seed)
    S=np.zeros(seeds); times=np.zeros(seeds,dtype=np.int64); answers=np.zeros(seeds,dtype=np.int8)
    n=0; looks=0
    for k in range(max_looks):
        nxt=max(n+1,int(np.ceil(look_ratio**k)))
        active=np.flatnonzero(times==0)
        if not len(active): break
        step=nxt-n
        S[active]+=theta*step+np.sqrt(step)*rng.standard_normal(len(active))
        spend=alpha/((k+1)*(k+2))
        boundary=np.sqrt(nxt)*(-ndtri(spend))
        hit=active[np.abs(S[active])>=boundary]
        times[hit]=nxt; answers[hit]=np.sign(S[hit]).astype(np.int8)
        n=nxt; looks=k+1
    censored=times==0
    observed=np.where(censored,n,times)
    errors=int(np.sum((answers!=0)&(answers!=side)))
    kl=(1-2*alpha)*np.log((1-alpha)/alpha)
    lower=2*kl/(q*q*epsilon*epsilon)
    scaled=(q*epsilon)**2*observed
    summary=dict(q=q,epsilon=epsilon,alpha=alpha,side=side,seeds=seeds,
        stopped=int(np.sum(~censored)),censored=int(np.sum(censored)),errors=errors,
        error_rate=errors/seeds,error_interval_95=binomial_interval(errors,seeds),
        mean_samples=float(np.mean(observed)),median_samples=float(np.median(observed)),
        std_samples=float(np.std(observed,ddof=1)),se_mean_samples=float(np.std(observed,ddof=1)/np.sqrt(seeds)),
        p90_samples=float(np.quantile(observed,.9)),max_samples=int(np.max(observed)),
        full_sign_information_lower=lower,mean_over_information_lower=float(np.mean(observed)/lower),
        mean_scaled_q2epsilon2=float(np.mean(scaled)),look_count=looks,
        known_A=True,gap_known_to_policy=False,conditional_on_phase_pair=False)
    return summary, observed, answers


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--q',type=int,default=4)
    parser.add_argument('--epsilons',type=float,nargs='+',default=[.008,.004,.002,.001,.0005,.00025,.000125])
    parser.add_argument('--alphas',type=float,nargs='+',default=[.05,.01,.001])
    parser.add_argument('--seeds',type=int,default=5000)
    parser.add_argument('--seed',type=int,default=20260908)
    parser.add_argument('--look-ratio',type=float,default=1.1)
    parser.add_argument('--max-looks',type=int,default=400)
    parser.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/phase_cost.json'))
    args=parser.parse_args(); q=args.q
    assert q>=3 and 1<args.look_ratio<=2 and args.seeds>=2
    assert args.look_ratio**(args.max_looks-1)<np.iinfo(np.int64).max
    p=phase_parameters(q)
    assert all(0<e<min(p['mu_U']-p['mu_L'],p['mu_H']-p['mu_U']) for e in args.epsilons)
    assert all(0<a<.5 for a in args.alphas)
    params=dict(q=q,epsilons=args.epsilons,alphas=args.alphas,seeds=args.seeds,seed=args.seed,
                look_ratio=args.look_ratio,max_looks=args.max_looks)
    checks=[actual_table_crosscheck(i) for i in (3,4,5)]
    rows=[]; raw={}
    for alpha in args.alphas:
        for eps in args.epsilons:
            for side in (-1,1):
                seq=np.random.SeedSequence([args.seed,q,int(round(alpha*10**9)),int(round(eps*10**12)),int(side+1)])
                row,t,a=phase_trials(q,eps,alpha,side,args.seeds,seq,args.look_ratio,args.max_looks)
                key=f'a{alpha}_e{eps}_s{side}'
                raw[key+'_samples']=t;raw[key+'_answer']=a;rows.append(row)
            print(f'alpha={alpha:g} eps={eps:g}: mean={rows[-1]["mean_samples"]:.1f}, stopped={rows[-1]["stopped"]}/{args.seeds}',flush=True)
    left=np.array([1-p['left_Bon_weight'],0,p['left_Bon_weight']])
    right=np.array([0,1-p['right_Bon_weight'],p['right_Bon_weight']])
    regrets=[]
    for eps in sorted(set(args.epsilons+[1e-5,1e-6])):
        if eps>=p['mu_H']-p['mu_U']: continue
        mus=[p['mu_U']-eps,p['mu_U']+eps]
        gammas=[information(q,mu,oracle(q,mu,p))[0] for mu in mus]
        def worst_regret(eta):
            design=eta*left+(1-eta)*right
            return max(g-information(q,mu,design)[0] for mu,g in zip(mus,gammas))
        optimum=minimize_scalar(worst_regret,bounds=(0,1),method='bounded',options={'xatol':1e-12})
        regrets.append(dict(epsilon=eps,
            wrong_right_on_left=gammas[0]-information(q,mus[0],right)[0],
            wrong_left_on_right=gammas[1]-information(q,mus[1],left)[0],
            half_mixture_worst_regret=worst_regret(.5),
            best_boundary_segment_weight_left=float(optimum.x),
            best_boundary_segment_worst_regret=float(optimum.fun),
            half_mixture_regret_over_epsilon=worst_regret(.5)/eps,
            predicted_limit=p['slope_jump']/2,
            gamma_left=gammas[0],gamma_right=gammas[1]))
    args.out.parent.mkdir(parents=True,exist_ok=True)
    npz=args.out.with_suffix('.npz'); np.savez_compressed(npz,**raw)
    result=dict(evidence_class='EMPIRICAL_UNIFORM_PHASE_SIGN_TEST_AND_NUMERICAL_ALLOCATION_REGRET',
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),configuration=params,
        phase_parameters=p,actual_table_checks=checks,phase_trials=rows,allocation_regret=regrets,
        raw_trials=str(npz),raw_sha256=sha256(npz.read_bytes()).hexdigest(),
        caveats=['Known A for phase-testing experiment; unknown-A pilot is separate.',
        'The procedure is gap-agnostic and uniformly sign-correct; no termination guarantee at exact boundary.',
        'Numerical phase-III oracle formula not yet formalized in Lean.',
        'Worst regret minimized only over the boundary segment, not all legal allocations.',
        'No claim that exact phase identification is necessary for geometric-answer identification.',
        'Information lower bound is for the full sign problem, four times the symmetric-pair bound.',
        'Censored sample totals are lower bounds on full stopping times; inspect censor count.'])
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print(args.out,flush=True)


if __name__=='__main__': main()
