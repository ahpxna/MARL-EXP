"""Matched-budget functional acquisition lab covering every proposed C/D allocation option.

Development-only synthetic Gaussian oracle.  Each strategy receives exactly the
same per-relation intervention budget and consumes prefixes of the same pre-
generated cell observations (common random numbers).  This tests downstream C/D
endpoints, not merely allocation coverage.
"""
from __future__ import annotations
import argparse,json,sys,math
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from scipy.stats import spearmanr
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='functional_matched_budget_allocation_v2'
STRATEGIES=(
 'uniform','behavior_freq','uncertainty_only','D_neyman_pilot','D_oracle',
 'C_extremal_confidence','C_successive_elimination','C_successive_known_sigma',
 'C_split_eval','C_oracle',
)
DIAGNOSTIC_STRATEGIES=('D_oracle','C_oracle','C_successive_known_sigma')
DEPLOYABLE_STRATEGIES=tuple(s for s in STRATEGIES if s not in DIAGNOSTIC_STRATEGIES)

def _allocate_remaining(counts,weights,remaining):
    counts=np.asarray(counts,int).copy(); w=np.asarray(weights,float); w=np.maximum(w,0)
    if remaining<=0: return counts
    if not np.any(w>0): w=np.ones_like(w)
    p=w/w.sum(); add=np.floor(remaining*p).astype(int); counts+=add; left=int(remaining-add.sum())
    if left:
        frac=remaining*p-add; order=np.argsort(-frac,kind='stable'); counts[order[:left]]+=1
    return counts

def _mean(obs,n):
    n=int(n); return float(np.mean(obs[:n])) if n>0 else 0.0

def _pilot_sigma(obs,n):
    n=int(n)
    if n<2: return 1.0
    v=float(np.std(obs[:n],ddof=1)); return max(v,1e-3)

def _counts_fixed(strategy,B,truth,sigma,behavior,obs):
    K=len(truth); base=np.ones(K,dtype=int); remain=int(B-K)
    if remain<0: raise ValueError('budget must be >= K')
    if strategy=='uniform': return _allocate_remaining(base,np.ones(K),remain),None
    if strategy=='behavior_freq': return _allocate_remaining(base,behavior,remain),None
    if strategy=='D_oracle':
        w=np.linspace(-1,1,K); w-=w.mean(); w/=np.sum(np.abs(w)); return _allocate_remaining(base,np.abs(w)*sigma,remain),None
    if strategy=='C_oracle':
        weights=np.zeros(K); weights[int(np.argmax(truth))]=sigma[int(np.argmax(truth))]; weights[int(np.argmin(truth))]=sigma[int(np.argmin(truth))]
        return _allocate_remaining(base,weights,remain),{'selected_hi':int(np.argmax(truth)),'selected_lo':int(np.argmin(truth)),'oracle_selection':True}
    # Pilot-based fixed allocations use two samples/cell where budget permits.
    pilot=min(2,max(1,B//K)); base=np.full(K,pilot,dtype=int); used=int(base.sum())
    if used>B: base=np.ones(K,dtype=int); used=K
    sig_hat=np.asarray([_pilot_sigma(obs[a],base[a]) for a in range(K)])
    means=np.asarray([_mean(obs[a],base[a]) for a in range(K)])
    remain=B-used
    if strategy=='uncertainty_only': return _allocate_remaining(base,sig_hat,remain),None
    if strategy=='D_neyman_pilot':
        w=np.linspace(-1,1,K); w-=w.mean(); w/=np.sum(np.abs(w)); return _allocate_remaining(base,np.abs(w)*sig_hat,remain),None
    if strategy=='C_extremal_confidence':
        weights=np.zeros(K); hi=int(np.argmax(means)); lo=int(np.argmin(means)); weights[hi]=sig_hat[hi]; weights[lo]=sig_hat[lo]
        return _allocate_remaining(base,weights,remain),{'selected_hi':hi,'selected_lo':lo,'oracle_selection':False}
    raise ValueError(strategy)

def _successive_counts(B,obs,known_sigma=None):
    """Successive extremal allocation without hidden oracle leakage.

    The deployable branch estimates per-cell noise from accumulated samples.
    ``known_sigma`` is retained only as an explicitly diagnostic known-noise
    ceiling, never as the deployable strategy used for endpoint winners.
    """
    K=len(obs); pilot=2 if B>=2*K else 1; counts=np.full(K,pilot,dtype=int); z=2.0
    while int(counts.sum())<B:
        means=np.asarray([_mean(obs[a],counts[a]) for a in range(K)])
        if known_sigma is None:
            sig=np.asarray([_pilot_sigma(obs[a],counts[a]) for a in range(K)])
        else:
            sig=np.asarray(known_sigma,float)
        rad=z*sig/np.sqrt(np.maximum(counts,1))
        L=means-rad; U=means+rad
        maxcand=np.flatnonzero(U>=np.max(L)-1e-12); mincand=np.flatnonzero(L<=np.min(U)+1e-12)
        cand=np.unique(np.concatenate([maxcand,mincand]));
        a=int(cand[np.argmax(rad[cand])]); counts[a]+=1
    return counts,{'known_sigma_diagnostic':bool(known_sigma is not None)}

def _split_estimate(B,truth,sigma,obs):
    K=len(truth); pilot=max(K,B//2); pilot=min(pilot,B-2) if B>=K+2 else K
    counts=np.ones(K,dtype=int); counts=_allocate_remaining(counts,np.ones(K),pilot-K)
    means=np.asarray([_mean(obs[a],counts[a]) for a in range(K)])
    hi=int(np.argmax(means)); lo=int(np.argmin(means)); remain=B-int(counts.sum()); eval_counts=np.zeros(K,dtype=int)
    if remain>0:
        eval_counts[hi]=remain//2; eval_counts[lo]=remain-eval_counts[hi]
    # Independent evaluation uses observations after the pilot prefix.
    def eval_mean(a,n):
        n=int(n); start=int(counts[a]); return float(np.mean(obs[a][start:start+n])) if n>0 else means[a]
    c_hat=eval_mean(hi,eval_counts[hi])-eval_mean(lo,eval_counts[lo])
    return counts+eval_counts,{'C_override':float(c_hat),'selected_hi':hi,'selected_lo':lo}

def _metrics(rows):
    def rho(x,y):
        x=np.asarray(x,float); y=np.asarray(y,float)
        if len(x)<2 or np.allclose(x,x[0]) or np.allclose(y,y[0]): return 0.0
        v=spearmanr(x,y).statistic; return 0.0 if not np.isfinite(v) else float(v)
    out={}
    for key in ('C_mae','D_mae','C_topk_exact','D_sign_accuracy','extrema_match','Q_rmse'):
        out[key]=float(np.mean([r[key] for r in rows]))
    out['C_spearman']=rho([r['C_hat'] for r in rows],[r['C_true'] for r in rows])
    out['D_spearman']=rho([r['D_hat'] for r in rows],[r['D_true'] for r in rows])
    out['mean_total_samples']=float(np.mean([r['samples'] for r in rows]))
    return out

def run(instances=200,seeds=(0,),budgets=(16,32,64,128,256),R=5,K=6,topk=2):
    if min(budgets)<K: raise ValueError('all per-relation budgets must be >= K')
    all_rows={str(B):{s:[] for s in STRATEGIES} for B in budgets}
    for seed in seeds:
        rng=np.random.default_rng(int(seed))
        for idx in range(int(instances)):
            truths=[]; sigmas=[]; behaviors=[]
            for r in range(R):
                cap=float(rng.uniform(.6,2.0)); center=float(rng.normal(scale=.3)); q=rng.uniform(center-cap/2,center+cap/2,size=K); q[0]=center-cap/2; q[-1]=center+cap/2
                truths.append(q); sigmas.append(rng.uniform(.2,.7,size=K)); behaviors.append(rng.dirichlet(np.geomspace(2.5,.3,K)))
            truths=np.asarray(truths); sigmas=np.asarray(sigmas); behaviors=np.asarray(behaviors)
            w=np.linspace(-1,1,K); w-=w.mean(); w/=np.sum(np.abs(w)); C_true=np.ptp(truths,axis=1); D_true=truths@w; top_true=set(np.argsort(-C_true,kind='stable')[:topk])
            Bmax=max(budgets); obs=[[rng.normal(loc=truths[r,a],scale=sigmas[r,a],size=Bmax+4) for a in range(K)] for r in range(R)]
            for B in budgets:
                for strategy in STRATEGIES:
                    qhat=np.zeros_like(truths); C_hat=np.zeros(R); D_hat=np.zeros(R); ext=[]; total=0
                    for r in range(R):
                        if strategy=='C_successive_elimination': counts,meta=_successive_counts(B,obs[r],known_sigma=None)
                        elif strategy=='C_successive_known_sigma': counts,meta=_successive_counts(B,obs[r],known_sigma=sigmas[r])
                        elif strategy=='C_split_eval': counts,meta=_split_estimate(B,truths[r],sigmas[r],obs[r])
                        else: counts,meta=_counts_fixed(strategy,B,truths[r],sigmas[r],behaviors[r],obs[r])
                        means=np.asarray([_mean(obs[r][a],counts[a]) for a in range(K)]); qhat[r]=means; total+=int(counts.sum())
                        if meta and 'C_override' in meta:
                            C_hat[r]=float(meta['C_override'])
                        elif meta and 'selected_hi' in meta:
                            C_hat[r]=float(means[int(meta['selected_hi'])]-means[int(meta['selected_lo'])])
                        else:
                            C_hat[r]=float(np.ptp(means))
                        D_hat[r]=float(means@w); ext.append(int(np.argmax(means)==np.argmax(truths[r]) and np.argmin(means)==np.argmin(truths[r])))
                    top_hat=set(np.argsort(-C_hat,kind='stable')[:topk]); nonzero=np.abs(D_true)>1e-10
                    all_rows[str(B)][strategy].append({'C_mae':float(np.mean(np.abs(C_hat-C_true))),'D_mae':float(np.mean(np.abs(D_hat-D_true))),'C_topk_exact':int(top_hat==top_true),'D_sign_accuracy':float(np.mean(np.sign(D_hat[nonzero])==np.sign(D_true[nonzero]))) if np.any(nonzero) else 1.0,'extrema_match':float(np.mean(ext)),'Q_rmse':float(np.sqrt(np.mean((qhat-truths)**2))),'C_hat':float(np.mean(C_hat)),'C_true':float(np.mean(C_true)),'D_hat':float(np.mean(D_hat)),'D_true':float(np.mean(D_true)),'samples':total})
    summary={B:{s:_metrics(rows) for s,rows in by.items()} for B,by in all_rows.items()}
    # Report deployable and diagnostic winners separately.  Previous output
    # accidentally allowed oracle strategies to win the headline table.
    winners={}; winners_all={}
    for B,by in summary.items():
        deploy={name:by[name] for name in DEPLOYABLE_STRATEGIES}
        winners[B]={'C_mae':min(deploy,key=lambda x:deploy[x]['C_mae']),'C_topk_exact':max(deploy,key=lambda x:deploy[x]['C_topk_exact']),'D_mae':min(deploy,key=lambda x:deploy[x]['D_mae']),'D_sign_accuracy':max(deploy,key=lambda x:deploy[x]['D_sign_accuracy'])}
        winners_all[B]={'C_mae':min(by,key=lambda x:by[x]['C_mae']),'C_topk_exact':max(by,key=lambda x:by[x]['C_topk_exact']),'D_mae':min(by,key=lambda x:by[x]['D_mae']),'D_sign_accuracy':max(by,key=lambda x:by[x]['D_sign_accuracy'])}
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances_per_seed':int(instances),'seeds':list(map(int,seeds)),'budgets_per_relation':list(map(int,budgets)),'relations':int(R),'actions':int(K),'strategies':STRATEGIES,'deployable_strategies':DEPLOYABLE_STRATEGIES,'diagnostic_strategies':DIAGNOSTIC_STRATEGIES,'matched_budget_contract':'every strategy uses exactly B samples per relation; common-random-number cell streams shared within instance','by_budget':summary,'endpoint_winners':winners,'endpoint_winners_all':winners_all}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=200); p.add_argument('--seeds',nargs='+',type=int,default=[0,1,2,3,4]); p.add_argument('--budgets',nargs='+',type=int,default=[16,32,64,128,256]); p.add_argument('--relations',type=int,default=5); p.add_argument('--actions',type=int,default=6); p.add_argument('--topk',type=int,default=2); p.add_argument('--out',default='research/high_value_extensions/functional/allocation_summary.json'); a=p.parse_args(argv)
    payload=run(a.instances,tuple(a.seeds),tuple(a.budgets),a.relations,a.actions,a.topk); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
