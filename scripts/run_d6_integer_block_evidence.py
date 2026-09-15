"""Actual legal off-query evidence for the proved two-block integer allocation.
Draws independent noise on every executed query, with means computed from
intersections with a hidden B. No discovery or adaptive regret claim.
"""
import argparse, hashlib, json, math
from fractions import Fraction
from pathlib import Path
import numpy as np


def main():
    p=argparse.ArgumentParser();p.add_argument('--trials',type=int,default=2000)
    p.add_argument('--seed',type=int,default=91054);p.add_argument('--out',required=True)
    a=p.parse_args();out=Path(a.out)
    if out.exists(): raise SystemExit(f'refusing to overwrite {out}')
    rng=np.random.default_rng(a.seed);rows=[];failures=[]
    for q in [3,4,8,16,64,256]:
        n=2*q+1;B=np.zeros(n,int);B[rng.choice(n,q,replace=False)]=1
        groups=[np.arange(q),np.arange(q,n-2),np.arange(n-2,n)]
        assert [len(g) for g in groups]==[q,q-1,2]
        hits=np.array([B[(np.arange(q)+i)%n].sum() for i in range(n)])
        three=np.array([B[g].sum() for g in groups])
        assert hits.sum()==q*q and three.sum()==q
        Ic=Fraction(q**4,n);It=Fraction(q*q,3)
        for N in sorted({3,n-1,n,n+3,2*n-1,2*n+3,4*n-1}):
            L=N//n;b=(N%n)//3;info=L*Ic+b*It
            opt=max(l*Ic+((N-l*n)//3)*It for l in range(N//n+1))
            assert info==opt and n*L+3*b<=N
            # Local separation chosen on the N~q phase-estimation scale.
            eps=q**(-1.5);mu0=.75
            for sign in [-1,1]:
                mu=mu0+sign*eps;cyc=np.zeros(a.trials);tri=np.zeros(a.trials)
                for _ in range(L):
                    raw=rng.normal(1+hits*(1-mu),1,size=(a.trials,n))
                    cyc+=(n+q*q-raw.sum(axis=1))/(q*q)
                for _ in range(b):
                    raw=rng.normal(1+three*(1-mu),1,size=(a.trials,3))
                    tri+=(3+q-raw.sum(axis=1))/q
                estimate=(float(Ic)*cyc+float(It)*tri)/float(info)
                error=estimate-mu;var=1/float(info)
                observed=float(np.mean((estimate-mu0)*sign<0))
                exact=.5*math.erfc(eps*math.sqrt(float(info)/2))
                rows.append(dict(q=q,N=N,L=L,b=b,queries_executed=n*L+3*b,wasted=N-n*L-3*b,
                    mu=mu,epsilon=eps,sign=sign,trials=a.trials,information_exact=str(info),
                    exact_variance=var,empirical_mse=float(np.mean(error**2)),
                    empirical_bias=float(error.mean()),bias_standard_error=math.sqrt(var/a.trials),
                    mse_ratio=float(np.mean(error**2)/var),phase_error_observed=observed,
                    phase_error_exact=exact,phase_error_standard_error=math.sqrt(exact*(1-exact)/a.trials),
                    hybrid_variance_over_cyclic=float(L*Ic/info) if L else None))
        print(json.dumps(dict(q=q,completed=True)),flush=True)
    result=dict(evidence_class='DEVELOPMENT_MONTE_CARLO_ACTUAL_LEGAL_QUERY_MEANS_AND_RAW_NOISE',
        scope='Fixed A-free phase estimation using two named block families. No adaptive allocation or stopping-rate claim.',
        seed=a.seed,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows)
    out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
