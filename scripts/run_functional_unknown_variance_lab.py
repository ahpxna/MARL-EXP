"""Unknown-variance redesign for Functional C/D acquisition.

Known sigma is a diagnostic oracle ceiling only.  Deployable strategies learn
variance from the same finite budget and report the cost of doing so.
"""
from __future__ import annotations
import argparse, json, math
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from scipy.stats import t as student_t
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='functional_unknown_variance_v1'
DEPLOYABLE=('uniform','variance_plugin','variance_shrinkage','time_uniform_t_proxy')
DIAGNOSTIC=('known_sigma_oracle',)


def _alloc(base, weights, remaining):
    out=np.asarray(base,int).copy(); remaining=int(remaining)
    if remaining<=0: return out
    w=np.asarray(weights,float); w=np.maximum(w,0)
    if not np.any(w>0): w=np.ones_like(w)
    p=w/w.sum(); raw=remaining*p; add=np.floor(raw).astype(int); out+=add
    left=remaining-int(add.sum())
    if left:
        order=np.argsort(-(raw-add),kind='stable'); out[order[:left]]+=1
    return out


def _stats(streams, counts):
    means=[]; sig=[]
    for x,n in zip(streams,counts):
        n=int(n); sample=np.asarray(x[:n],float)
        means.append(float(sample.mean()))
        sig.append(float(sample.std(ddof=1)) if n>=2 else 1.0)
    return np.asarray(means),np.maximum(np.asarray(sig),1e-3)


def _candidate_weights(means,sig):
    hi=int(np.argmax(means)); lo=int(np.argmin(means)); w=np.zeros_like(sig); w[hi]=sig[hi]; w[lo]=sig[lo]
    return w,hi,lo


def _strategy_counts(name,B,streams,true_q,true_sigma,alpha=0.05):
    K=len(true_q)
    if B<K: raise ValueError('budget must be >= number of actions')
    if name=='uniform': return _alloc(np.ones(K,int),np.ones(K),B-K),{'oracle':False}
    if name=='known_sigma_oracle':
        w=np.zeros(K); hi=int(np.argmax(true_q)); lo=int(np.argmin(true_q)); w[hi]=true_sigma[hi]; w[lo]=true_sigma[lo]
        return _alloc(np.ones(K,int),w,B-K),{'oracle':True,'hi':hi,'lo':lo}
    pilot=min(max(2, int(math.ceil(math.sqrt(B)/2))), max(2,B//K))
    counts=np.full(K,pilot,int)
    if counts.sum()>B: counts=np.ones(K,int)
    means,sig=_stats(streams,counts)
    if name=='variance_plugin':
        w,hi,lo=_candidate_weights(means,sig)
        return _alloc(counts,w,B-int(counts.sum())),{'oracle':False,'hi':hi,'lo':lo,'pilot':int(pilot)}
    if name=='variance_shrinkage':
        pooled=float(np.sqrt(np.mean(sig**2)))
        shrunk=np.sqrt(0.5*sig**2+0.5*pooled**2)
        w,hi,lo=_candidate_weights(means,shrunk)
        return _alloc(counts,w,B-int(counts.sum())),{'oracle':False,'hi':hi,'lo':lo,'pilot':int(pilot),'pooled_sigma':pooled}
    if name=='time_uniform_t_proxy':
        # Repeated-look finite-grid Bonferroni t radii.  This is an experimental
        # proxy, not a claim of an asymptotically optimal BAI algorithm.
        looks=max(1,B-int(counts.sum())); per_tail=max(1e-12,float(alpha)/(2*K*max(1,looks)))
        while int(counts.sum())<B:
            means,sig=_stats(streams,counts)
            df=np.maximum(counts-1,1); crit=np.asarray([float(student_t.ppf(1-per_tail,int(d))) for d in df])
            rad=crit*sig/np.sqrt(np.maximum(counts,1))
            L=means-rad; U=means+rad
            maxcand=np.flatnonzero(U>=np.max(L)-1e-12); mincand=np.flatnonzero(L<=np.min(U)+1e-12)
            cand=np.unique(np.concatenate([maxcand,mincand]))
            a=int(cand[np.argmax(rad[cand])]); counts[a]+=1
        return counts,{'oracle':False,'look_adjusted':True,'alpha':float(alpha)}
    raise ValueError(name)


def _variance_objective(counts,sigma,contrast):
    counts=np.maximum(np.asarray(counts,float),1.0); sigma=np.asarray(sigma,float); c=np.asarray(contrast,float)
    return float(np.sum((c*sigma)**2/counts))


def _fixed_contrast_plugin_counts(B,streams,true_contrast):
    """Allocation used only to test the deterministic variance lemma.

    The contrast is fixed externally; this deliberately removes extrema
    selection error so the variance-estimation premise is actually satisfied.
    """
    K=len(streams); pilot=min(max(2,int(math.ceil(math.sqrt(B)/2))),max(2,B//K)); counts=np.full(K,pilot,int)
    if counts.sum()>B: counts=np.ones(K,int)
    _,sig=_stats(streams,counts); weights=np.abs(np.asarray(true_contrast,float))*sig
    return _alloc(counts,weights,B-int(counts.sum())),sig

def run(instances=1000,seeds=(100,101,102,103,104),budgets=(32,64,128,256),K=6,alpha=0.05):
    strategies=DEPLOYABLE+DIAGNOSTIC; rows={str(B):{s:[] for s in strategies} for B in budgets}
    for seed in seeds:
        rng=np.random.default_rng(int(seed))
        for _ in range(int(instances)):
            cap=float(rng.uniform(.5,2)); center=float(rng.normal(scale=.25)); q=rng.uniform(center-cap/2,center+cap/2,size=K); q[0]=center-cap/2; q[-1]=center+cap/2
            sigma=rng.uniform(.15,.8,size=K); Bmax=max(map(int,budgets)); streams=[rng.normal(q[a],sigma[a],size=Bmax+8) for a in range(K)]
            hi=int(np.argmax(q)); lo=int(np.argmin(q)); c=np.zeros(K); c[hi]=1;c[lo]=-1; C=float(q[hi]-q[lo])
            for B in budgets:
                oracle_counts,_=_strategy_counts('known_sigma_oracle',int(B),streams,q,sigma,alpha)
                oracle_var=_variance_objective(oracle_counts,sigma,c)
                for strategy in strategies:
                    counts,meta=_strategy_counts(strategy,int(B),streams,q,sigma,alpha)
                    means,sighat=_stats(streams,counts); est_hi=int(np.argmax(means)); est_lo=int(np.argmin(means))
                    if strategy=='known_sigma_oracle':
                        # Diagnostic ceiling knows both the extrema identity and sigma.
                        Chat=float(means[hi]-means[lo])
                    elif meta.get('hi') is not None and meta.get('lo') is not None:
                        Chat=float(means[int(meta['hi'])]-means[int(meta['lo'])])
                    else:
                        Chat=float(np.ptp(means))
                    rel=np.max(np.abs(sighat-sigma)/np.maximum(sigma,1e-12)); var_obj=_variance_objective(counts,sigma,c)
                    fixed_counts,fixed_sighat=_fixed_contrast_plugin_counts(int(B),streams,c)
                    fixed_rel=float(np.max(np.abs(fixed_sighat-sigma)/np.maximum(sigma,1e-12))); rho=min(fixed_rel,0.999999)
                    fixed_var=_variance_objective(fixed_counts,sigma,c); robust_factor=((1+rho)/(1-rho))**2
                    rows[str(B)][strategy].append({
                        'C_abs_error':abs(Chat-C),'extrema_correct':int(est_hi==hi and est_lo==lo),
                        'variance_rel_error_max':float(rel),'true_contrast_variance':var_obj,
                        'variance_ratio_to_known_sigma_oracle':float(var_obj/max(oracle_var,1e-12)),
                        'selection_error_present':bool(meta.get('hi') is not None and (int(meta['hi'])!=hi or int(meta['lo'])!=lo)),
                        'fixed_contrast_variance_rel_error':fixed_rel,'fixed_contrast_true_variance':fixed_var,
                        'deterministic_relative_error_factor':float(robust_factor),
                        'relative_error_bound_holds':bool(fixed_var <= robust_factor*max(oracle_var,1e-12)+1e-10),
                        'counts':counts.tolist(),'meta':meta,
                    })
    summary={}
    for B,by in rows.items():
        summary[B]={}
        for s,rr in by.items():
            summary[B][s]={
                'C_mae':float(np.mean([r['C_abs_error'] for r in rr])),
                'extrema_accuracy':float(np.mean([r['extrema_correct'] for r in rr])),
                'mean_variance_rel_error_max':float(np.mean([r['variance_rel_error_max'] for r in rr])),
                'median_variance_ratio_to_known_sigma_oracle':float(np.median([r['variance_ratio_to_known_sigma_oracle'] for r in rr])),
                'relative_error_bound_violation_count':int(sum(not r['relative_error_bound_holds'] for r in rr)),
                'selection_error_fraction':float(np.mean([r['selection_error_present'] for r in rr])),
            }
    winners={B:min(DEPLOYABLE,key=lambda s:summary[B][s]['C_mae']) for B in summary}
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'known_sigma_policy':'diagnostic oracle ceiling only; never included in deployable winner','instances_per_seed':int(instances),'seeds':list(map(int,seeds)),'budgets':list(map(int,budgets)),'actions':int(K),'alpha':float(alpha),'deployable':list(DEPLOYABLE),'diagnostic':list(DIAGNOSTIC),'by_budget':summary,'deployable_C_mae_winner':winners}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=1000); p.add_argument('--seeds',nargs='+',type=int,default=[100,101,102,103,104]); p.add_argument('--budgets',nargs='+',type=int,default=[32,64,128,256]); p.add_argument('--actions',type=int,default=6); p.add_argument('--alpha',type=float,default=.05); p.add_argument('--out',default='research/high_value_extensions/functional/unknown_variance.json'); a=p.parse_args(argv)
    payload=run(a.instances,tuple(a.seeds),tuple(a.budgets),a.actions,a.alpha); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
