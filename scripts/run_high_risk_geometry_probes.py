"""Development falsification probes on actual finite geometry; not confirmatory evidence.
D6 uses explicit world evaluation and independent raw query noise. Support uses
shared coordinate projections on varying two-point supports. Structural uses
exact subset enumeration/DP, never a floating point LP certificate.
"""
from __future__ import annotations
import argparse, hashlib, itertools, json, math
from fractions import Fraction
from pathlib import Path
import numpy as np
from scipy.stats import norm


def save(path, payload):
    payload['script_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix('.tmp'); tmp.write_text(json.dumps(payload, indent=2)+'\n'); tmp.replace(path)


def d6(seed, trials):
    rng = np.random.default_rng(seed); rows=[]; finite=[]
    for q in [3,4,8,16,32,64]:
        n=2*q+1; cyc=np.zeros((n,n),int)
        for t in range(n):cyc[t,(np.arange(q)+t)%n]=1
        three=np.zeros((3,n),int); three[0,:q]=1;three[1,q:2*q-1]=1;three[2,2*q-1:]=1
        assert np.all(cyc.sum(0)==q) and np.all(cyc.sum(1)==q)
        assert np.all(three.sum(0)==1) and sorted(three.sum(1))==sorted([q,q-1,2])
        mu0=.8; eps=q**(-1.5); mu=mu0+eps
        b=np.zeros(n,int);b[rng.choice(n,q,replace=False)]=1;a=1-b
        def actual_world(x):
            # j is held false by off queries; gate is the exact construction's OR.
            return (1-mu)*(x@b)+((x@a>0)|(x@b>=2)).astype(int)
        for design,M,coef in [('cyclic',cyc,q*q),('three_group',three,q)]:
            means=actual_world(M)
            assert abs(means.sum()-(len(M)+coef*(1-mu)))<1e-9
            for L in [1,4,16]:
                N=L*len(M); out=[]
                for start in range(0,trials,2000):
                    size=min(2000,trials-start)
                    raw=rng.normal(loc=means,scale=1,size=(size,L,len(M)))
                    out.extend((1-(raw.sum((1,2))-N)/(L*coef)).tolist())
                estimates=np.asarray(out);v=len(M)/(L*coef**2)
                rows.append(dict(q=q,design=design,blocks=L,raw_queries=N,epsilon=eps,
                    predicted_variance=v,empirical_variance=float(estimates.var(ddof=1)),
                    standardized_bias=float((estimates.mean()-mu)/math.sqrt(v/trials)),
                    predicted_error=float(norm.cdf(-eps/math.sqrt(v))),
                    empirical_error=float(np.mean(estimates<mu0)),trials=trials,
                    q2N_variance=q*q*N*v))
        # Complete-block spending only; unused budget is charged, not silently ignored.
        for N in sorted(set([3,q,2*q,2*q+1,3*q,4*q,8*q,16*q])):
            if N<3:continue
            L3=N//3;Lc=N//n
            v3=3/(L3*q*q);vc=n/(Lc*q**4) if Lc else None
            finite.append(dict(q=q,budget=N,three_used=3*L3,cyclic_used=n*Lc,
                three_variance=v3,cyclic_variance=vc,
                better=('cyclic' if vc is not None and vc<v3 else 'three_group')))
    return dict(evidence_class='DEVELOPMENT_RAW_GAUSSIAN_SIMULATION',seed=seed,
        scope='Fixed nonadaptive independent unit-noise off-query designs; whole blocks. No adaptive allocation-regret or termination claim.',
        rows=rows,finite_budget=finite)


def support(seed,trials):
    rng=np.random.default_rng(seed);rows=[]
    for m in [3,4,8,16,32,64,128]:
        tips=np.ones((m,m),int);np.fill_diagonal(tips,2-m)
        assert np.all(tips.sum(1)==1)
        radii=np.abs(tips.sum(1)[:,None]-tips)/2
        scale=(2*m-3)/2
        assert np.allclose(radii,np.eye(m)*(m-1)/2)
        assert np.allclose(np.abs(tips).sum(1)/2,scale)
        for omitted in range(m):
            assert np.all(np.delete(radii[:,omitted],omitted)==0)
        # A single membership test of tip_0 returns true iff the world is 0.
        decisions=np.where(np.arange(m)==0,1,0)
        assert np.all(radii[np.arange(m),decisions]==0)
        for noise in [.1,.25,.4]:
            delta=.05
            draws=math.ceil(math.log(1/delta)/(2*(.5-noise)**2))
            if draws%2==0:draws+=1
            for w in [0,1,m-1]:
                p=1-noise if w==0 else noise
                positive=rng.binomial(draws,p,size=trials)>draws/2
                chosen=positive.astype(int)
                failures=(chosen==w)
                rows.append(dict(m=m,world=w,membership_flip_probability=noise,queries=draws,
                    delta=delta,empirical_false_safe=float(failures.mean()),
                    worst_case_hoeffding_bound=math.exp(-2*draws*(.5-noise)**2),
                    obstruction_order=m,normalized_bad_radius=str(Fraction(m-1,2*m-3)),
                    exact_decision_queries=1,exact_full_identification_worst_queries=m-1,
                    trials=trials))
    return dict(evidence_class='EXACT_FINITE_GEOMETRY_AND_DEVELOPMENT_NOISY_SIMULATION',seed=seed,
        scope='Promised finite world family: exactly one of the listed non-anchor support points is present. Does not cover arbitrary unknown support.',
        conclusion='Unbounded minimal obstruction order coexists with one-test safe decision. Order alone cannot determine acquisition cost.',rows=rows)


def scalar_one_menu(weights):
    m=len(weights);size=1<<m;total=sum(weights);scale=sum(map(abs,weights))
    sums=[0]*size;cost=[0]*size;opt=[10**12]*(m+1)
    for mask in range(size):
        if mask:
            bit=mask&-mask;sums[mask]=sums[mask^bit]+weights[bit.bit_length()-1]
        cost[mask]=abs(total-sums[mask]);k=mask.bit_count();opt[k]=min(opt[k],cost[mask])
    best=[10**12]*size;parent=[0]*size;best[0]=0
    for mask in range(1,size):
        remaining=mask;v=10**12;prev=0
        while remaining:
            bit=remaining&-remaining;remaining^=bit;p=mask^bit
            if best[p]<v:v=best[p];prev=p
        best[mask]=max(v,cost[mask]-opt[mask.bit_count()]);parent[mask]=prev
    path=[];mask=size-1
    while mask:
        p=parent[mask];path.append((mask^p).bit_length()-1);mask=p
    return Fraction(best[-1],scale),list(reversed(path))


def structural(seed,searches):
    rng=np.random.default_rng(seed);stairs=[];best={}
    for r in range(2,9):
        m=2*r;F=np.zeros((m,r+1),int)
        for i in range(r): F[2*i,i+1]=1;F[2*i+1,1:i+2]=-1
        values=np.zeros((1<<m,r+1),int);opt=np.full(m+1,np.inf)
        for mask in range(1<<m):
            if mask:
                bit=mask&-mask;values[mask]=values[mask^bit]+F[bit.bit_length()-1]
            k=m-mask.bit_count();rad=int(np.ptp(values[mask]))/2;opt[k]=min(opt[k],rad)
        ranking=list(range(1,m,2))+list(range(0,m,2));selected=0;excess=[]
        for k in range(m+1):
            if k:selected|=1<<ranking[k-1]
            omitted=((1<<m)-1)^selected
            excess.append(float(np.ptp(values[omitted])/2-opt[k]))
        assert max(excess)<=.5
        stairs.append(dict(r=r,components=m,subsets=1<<m,ranking=ranking,
            max_excess=max(excess),normalized_max_excess=max(excess)/r,
            proposed_upper=1/(2*r),all_budget_excess=excess))
    # Search actual two-point scalar geometry for robust one-ranking difficulty.
    # Search-selected witnesses are exploratory; every reported objective is exact DP.
    for m in [6,8,10,12]:
        record=None
        for _ in range(searches):
            weights=rng.integers(-40,41,size=m).tolist()
            if not sum(map(abs,weights)):continue
            eps,ranking=scalar_one_menu(weights)
            if record is None or eps>record[0]:record=(eps,weights,ranking)
        eps,weights,ranking=record
        best[str(m)]=dict(maximum_found_minimum_one_ranking_epsilon=str(eps),weights=weights,
            optimal_ranking=ranking,instances_searched=searches,
            evidence='Exact DP for each random instance; no universal upper/lower bound inferred')
    return dict(evidence_class='EXACT_FINITE_DP_WITH_RANDOM_WITNESS_SEARCH',seed=seed,
        staircase=stairs,scalar_robust_search=best)


def main():
    p=argparse.ArgumentParser();p.add_argument('lane',choices=['d6','support','structural']);p.add_argument('--seed',type=int,default=91001)
    p.add_argument('--trials',type=int,default=20000);p.add_argument('--searches',type=int,default=100)
    p.add_argument('--out',required=True);a=p.parse_args()
    result=globals()[a.lane](a.seed,a.searches if a.lane=='structural' else a.trials)
    save(Path(a.out),result);print(json.dumps({'lane':a.lane,'out':a.out,'evidence_class':result['evidence_class']}))
if __name__=='__main__':main()
