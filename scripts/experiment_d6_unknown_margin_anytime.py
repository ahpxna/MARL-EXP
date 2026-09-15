#!/usr/bin/env python3
"""D6 identification with unknown continuous margin and an anytime-valid stop.

Gaussian noise, known variance one, unit measurement cost. For every hidden
set A, the exact actual-world mean is a_A(e)+lambda*b_A(e), lambda in [0,1].
A proper mixture over all sets and uniform lambda defines Z_t. Under every
fixed true (A,lambda), Z_t/L_t(A,lambda) is a nonnegative mean-one martingale,
even for adaptive measurements. Reject A only if max_lambda L_t(A,lambda)
< delta*Z_t; stop at a unique surviving A. Ville's inequality gives error
probability <=delta for each parameter, uniformly over stopping times.
This validity argument is analytic, not currently formalized in Lean.
The oracle mode uses the true set; learner modes never use it for selection.
The closed-form allocation is optimality-certified only at true mu=1/2 for
q>=3 in the stated query library. Experiments do not prove sample optimality.
"""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import numpy as np
from scipy.special import log_ndtr, logsumexp
from verify_d6_information_limit_bridge import family_world
from fractions import Fraction


def model(m):
    k,q=m//2,m//2-1
    assert m%2==0 and q>=3
    j=1<<k; U=((1<<m)-1)^j
    labels=[sum(1<<i for i in g) for g in combinations([i for i in range(m) if i!=k],k)]
    groups=[g for g in range(1<<m) if not g&j and 1<=g.bit_count()<=q]
    queries=[('Q',i) for i in range(m)]+[('J',g) for g in groups]+[
        ('J0',g) for g in groups if g.bit_count()>=2]
    index={e:i for i,e in enumerate(queries)}
    means0=[]; slopes=[]
    for A in labels:
        f0=family_world(m,Fraction(1),A)
        f1=family_world(m,Fraction(0),A)
        x=[(1<<g) if kind=='Q' else g|j if kind=='J' else g for kind,g in queries]
        a=np.array([f0[g] for g in x],float)
        means0.append(a); slopes.append(np.array([f1[g] for g in x])-a)
    return k,q,j,U,labels,queries,index,np.array(means0),np.array(slopes)


def integrated_log_likelihood(sse,score,energy):
    out=-sse/2
    active=energy>0
    v=energy[active]; r=score[active]; center=r/v
    lo=-center*np.sqrt(v); hi=(1-center)*np.sqrt(v)
    # Reflect intervals in the right tail before subtracting Gaussian CDFs.
    reflect=lo>=0
    lo,hi=np.where(reflect,-hi,lo),np.where(reflect,-lo,hi)
    a=log_ndtr(lo); b=log_ndtr(hi)
    log_mass=b+np.log(-np.expm1(a-b))
    out[active]+=r*r/(2*v)+.5*np.log(2*np.pi/v)+log_mass
    assert np.isfinite(out).all()
    return out


def trial(data,mode,seed,delta,mu,max_steps):
    k,q,j,U,labels,queries,index,a,b=data
    m=2*k
    # Shared true set and shared noise by (seed,step) across allocation modes.
    truth_rng=np.random.default_rng(np.random.SeedSequence([seed,1]))
    policy_rng=np.random.default_rng(np.random.SeedSequence([seed,2]))
    noise_rng=np.random.default_rng(np.random.SeedSequence([seed,3]))
    true_idx=int(truth_rng.integers(len(labels))); true_A=labels[true_idx]
    truth=a[true_idx]+(1-mu)*b[true_idx]
    energy=np.zeros(len(labels)); score=energy.copy(); sse=energy.copy()
    mle=np.zeros(len(labels)); selected=0; forced=0; counts={}
    c=np.sqrt(q/(q+1)); w_expanded=c/(q-2+c)
    z=1/((q+1)*(q-2)+np.sqrt(q*(q+1)*(q-2)**2+1))
    w_anchored=z/((q+1)*(q-2)*(1-(q-2)*z)+z)
    for t in range(1,max_steps+1):
        if mode=='uniform':
            e=int(policy_rng.integers(len(queries)))
        elif forced<int(np.sqrt(t)):
            e=forced%m; forced+=1
        else:
            A=true_A if mode=='oracle_expanded' else labels[selected]
            B=U^A
            w=w_anchored if mode=='adaptive_anchored' else w_expanded
            if policy_rng.random()<w:
                e=index[('J',B)]
            else:
                positions=[i for i in range(m) if (1<<i)&A]
                omit=int(policy_rng.choice(positions))
                e=index[('J' if mode=='adaptive_anchored' else 'J0',A^(1<<omit))]
        query_type=queries[e][0]; counts[query_type]=counts.get(query_type,0)+1
        y=truth[e]+noise_rng.normal()
        residual=y-a[:,e]
        sse+=residual*residual; score+=b[:,e]*residual; energy+=b[:,e]**2
        lam=np.clip(np.divide(score,energy,out=np.zeros_like(score),where=energy>0),0,1)
        mle=-sse/2+lam*score-lam*lam*energy/2
        selected=int(np.argmax(mle))
        logZ=float(logsumexp(integrated_log_likelihood(sse,score,energy))-np.log(len(labels)))
        survivors=mle>=logZ+np.log(delta)
        if int(survivors.sum())==1:
            answer=int(np.flatnonzero(survivors)[0])
            return {'mode':mode,'seed':seed,'steps':t,'stopped':True,
                'correct':answer==true_idx,'estimated_mu':float(1-lam[answer]),
                'true_A':true_A,'answer_A':labels[answer],'query_counts':counts}
    return {'mode':mode,'seed':seed,'steps':max_steps,'stopped':False,
            'correct':None,'estimated_mu':float(1-lam[selected]),
            'true_A':true_A,'answer_A':None,'query_counts':counts}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--m',type=int,default=10)
    p.add_argument('--seeds',type=int,default=100)
    p.add_argument('--seed-start',type=int,default=0)
    p.add_argument('--delta',type=float,default=.001)
    p.add_argument('--mu',type=float,default=.5)
    p.add_argument('--max-steps',type=int,default=20000)
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args()
    assert 0<args.delta<1 and 0<=args.mu<=1
    data=model(args.m)
    modes=['adaptive_expanded','adaptive_anchored','uniform','oracle_expanded']
    rows=[]; summaries=[]
    for mode in modes:
        batch=[trial(data,mode,s,args.delta,args.mu,args.max_steps)
               for s in range(args.seed_start,args.seed_start+args.seeds)]
        rows.extend(batch)
        summary={'mode':mode,'trials':len(batch),'stopped':sum(r['stopped'] for r in batch),
            'errors':sum(r['correct'] is False for r in batch),
            'mean_steps_including_censored':float(np.mean([r['steps'] for r in batch])),
            'median_steps':float(np.median([r['steps'] for r in batch]))}
        summaries.append(summary); print(json.dumps(summary),flush=True)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps({'evidence_class':'EMPIRICAL_CONTINUOUS_MARGIN_ANYTIME_MIXTURE',
        'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'm':args.m,'mu':args.mu,'delta':args.delta,'max_steps':args.max_steps,
        'seeds':args.seeds,'seed_start':args.seed_start,'variance':1,
        'alternative_margin':'continuous [0,1]','stopping_rule':'proper_mixture_confidence_set',
        'sequential_optimality_Lean_proved':False,'summary':summaries,'trials':rows},indent=2)+'\n')


if __name__=='__main__': main()
