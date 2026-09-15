"""Fixed-gap discovery matching LeanD6DiscoveryStoppingV1; A and mu unknown.
The theorem target is discovery overhead, NOT Gamma-optimal adaptive regret.
Every Gaussian draw is charged as a query. Shared means are sampled afresh for
all contrasts, so the elementary variance-4 concentration calculation applies.
"""
import argparse, hashlib, json, math
from pathlib import Path
import numpy as np


def means_from_world(q,mu,b):
    n=2*q+1; a=1-b
    def world(x):return (1-mu)*(x@b)+int((x@a>0) or (x@b>=2))
    def unary(i):
        x=np.zeros(n,int);x[i]=1
        # D6 productResponse, not the value of the off query at that point.
        return 1-mu*b[i]
    contrasts=[]
    for i in range(1,n):
        helper=next(k for k in range(n) if k not in [0,i])
        x=np.zeros(n,int);x[[i,helper]]=1
        y=np.zeros(n,int);y[[0,helper]]=1
        contrasts.append([unary(0),unary(i),world(x),world(y)])
    return np.asarray(contrasts)


def run(seed,trials,delta):
    rng=np.random.default_rng(seed);rows=[]
    for q in [3,4,8,16,32,64,128,256]:
        n=2*q+1
        # Four label patterns per cell, including both possible anchor labels.
        patterns=[]
        for _ in range(2):
            b=np.zeros(n,int);b[rng.choice(n,q,False)]=1;patterns.append(b)
        for mu in [0,.01,.5,.99,1.]:
            for pattern,b in enumerate(patterns):
                means=means_from_world(q,mu,b);sign=np.array([1,-1,1,-1])
                anchor=np.array([means[0,0],means[0,0],means[0,3],means[0,3]])
                means=np.vstack([anchor,means])
                r0=max(512,math.ceil(128*math.log(8*n/(3*delta))))
                eta=2*n*math.exp(-r0/128)
                assert 4*eta/3<=delta
                expected=means@sign
                assert np.allclose(expected,b-b[0],atol=1e-12)
                sums=np.zeros((trials,n));active=np.ones(trials,bool)
                stopped=np.zeros(trials,int);failed=np.zeros(trials,bool);last_r=0
                for stage in range(15):
                    r=r0*2**stage;batch=r-last_r;indices=np.flatnonzero(active)
                    # Sum of batch independent raw unit-noise Gaussians for
                    # each of four actual measurements. Exact sufficient-statistic
                    # simulation, no mean-only noise-free shortcut.
                    raw_sums=rng.normal(batch*means,math.sqrt(batch),size=(len(indices),n,4))
                    sums[indices]+=raw_sums@sign
                    score=sums[indices]/r
                    order=np.argsort(score,axis=1);gap=np.take_along_axis(score,order[:,-q:],1).min(1)-np.take_along_axis(score,order[:,:-q],1).max(1)
                    radius=.25
                    done=gap>2*radius
                    ids=indices[done];guessed=np.zeros((len(ids),n),int)
                    np.put_along_axis(guessed,order[done,-q:],1,axis=1)
                    failed[ids]=np.any(guessed!=b,axis=1)
                    stopped[ids]=4*n*r;active[ids]=False;last_r=r
                    if not active.any():break
                rows.append(dict(q=q,mu=mu,pattern=pattern,anchor_label=int(b[0]),trials=trials,
                  stopped=int((~active).sum()),censored=int(active.sum()),false_label=int(failed.sum()),
                  mean_queries=float(stopped[~active].mean()) if (~active).any() else None,
                  median_queries=float(np.median(stopped[~active])) if (~active).any() else None,
                  max_queries=int(stopped.max()),delta=delta,final_repetitions=last_r,initial_repetitions=r0,eta=eta, theoretical_expected_queries_upper=4*n*r0*(1+2*eta),theoretical_ever_wrong_bound=4*eta/3))
        print(json.dumps(dict(q=q,completed=True)),flush=True)
    return dict(evidence_class='DEVELOPMENT_ACTUAL_QUERY_GAUSSIAN_SUFFICIENT_STATISTICS',
      seed=seed,raw_query_accounting='4 fresh scalar responses per off-j coordinate per repeat, including noisy anchor contrast',
      stopping_rule='top-q empirical gap > 1/2; r=r0*2^s; r0=max(512,ceil(128*log(8*d/(3*delta))))',
      scope='j and q known; A and mu unknown. Independent repeats, unit Gaussian noise. No Gamma or minimax discovery lower bound.',
      rows=rows)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--seed',type=int,default=91041);p.add_argument('--trials',type=int,default=500)
    p.add_argument('--delta',type=float,default=.05);p.add_argument('--out',required=True);a=p.parse_args()
    assert 0<a.delta<1 and a.trials>0
    result=run(a.seed,a.trials,a.delta);result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
