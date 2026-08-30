"""Functional extension lab: covariance-aware C/D design and geometry-stratified gains."""
from __future__ import annotations
import sys
from pathlib import Path as _Path
_ROOT=_Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path: sys.path.insert(0,str(_ROOT))
import argparse,json
from pathlib import Path
import numpy as np
from research_chains.experimental_extensions import capacity_contrast,covariance_design_misranking_search,lean_covariance_reversal_witness_diagnostics,quadratic_variance,random_psd
from research_chains.functionals import capacity,direction,extrema_gaps
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='functional_covariance_design_lab_v1'

def _truth(regime,K,rng):
    if regime=='unique': return np.linspace(-1,1,K)
    if regime=='near_tie':
        q=np.linspace(-1,1,K); q[-2]=q[-1]-0.03; q[1]=q[0]+0.03; return q
    if regime=='null': return np.zeros(K)
    if regime=='random':
        q=rng.normal(size=K); return q
    raise ValueError(regime)

def _designs(rng,K,n=8):
    out=[]
    for _ in range(n):
        s=random_psd(rng,K,jitter=.02); s*=K/np.trace(s) # same average marginal variance / budget proxy
        out.append(s)
    out.append(np.eye(K))
    return out

def run(instances=250,replicates=300,seed=0,K=6):
    rng=np.random.default_rng(seed); rows=[]; reversal=covariance_design_misranking_search(max(2000,instances*20),seed=seed+17,n=min(3,K))
    regimes=('unique','near_tie','null','random')
    for idx in range(int(instances)):
        regime=regimes[idx%len(regimes)]; q=_truth(regime,K,rng); weights=np.linspace(-1,1,K); weights-=weights.mean(); weights/=np.sum(np.abs(weights))
        designs=_designs(rng,K); gaps=extrema_gaps(q); aplus=int(np.argmax(q)); aminus=int(np.argmin(q)); vc=capacity_contrast(K,aplus,aminus)
        full_c=np.asarray([quadratic_variance(s,vc) for s in designs]); full_d=np.asarray([quadratic_variance(s,weights) for s in designs])
        diag_c=np.asarray([quadratic_variance(np.diag(np.diag(s)),vc) for s in designs]); diag_d=np.asarray([quadratic_variance(np.diag(np.diag(s)),weights) for s in designs])
        choices={'C_full':int(np.argmin(full_c)),'C_diag':int(np.argmin(diag_c)),'D_full':int(np.argmin(full_d)),'D_diag':int(np.argmin(diag_d)),'uniform':len(designs)-1}
        truth_c=capacity(q); truth_d=direction(q,weights)
        metrics={}
        for name,didx in choices.items():
            sigma=designs[didx]
            errors=rng.multivariate_normal(np.zeros(K),sigma,size=int(replicates))
            qh=q[None,:]+errors
            c=np.ptp(qh,axis=1); d=qh@weights
            metrics[name]={'C_mse':float(np.mean((c-truth_c)**2)),'D_mse':float(np.mean((d-truth_d)**2)),'extrema_match':float(np.mean((np.argmax(qh,axis=1)==aplus)&(np.argmin(qh,axis=1)==aminus))),'full_C_var':float(full_c[didx]),'full_D_var':float(full_d[didx])}
        rows.append({'regime':regime,'gap':float(gaps['g']),'choices':choices,'metrics':metrics,'C_diag_misrank':int(choices['C_full']!=choices['C_diag']),'D_diag_misrank':int(choices['D_full']!=choices['D_diag'])})
    summary={}
    for regime in regimes:
        rr=[r for r in rows if r['regime']==regime]
        if not rr:
            summary[regime]={'n':0}
            continue
        summary[regime]={
            'n':len(rr),'mean_gap':float(np.mean([r['gap'] for r in rr])),
            'C_diag_design_misrank_rate':float(np.mean([r['C_diag_misrank'] for r in rr])),
            'D_diag_design_misrank_rate':float(np.mean([r['D_diag_misrank'] for r in rr])),
            'C_full_vs_diag_mse_ratio':float(np.mean([r['metrics']['C_full']['C_mse']/max(r['metrics']['C_diag']['C_mse'],1e-12) for r in rr])),
            'D_full_vs_diag_mse_ratio':float(np.mean([r['metrics']['D_full']['D_mse']/max(r['metrics']['D_diag']['D_mse'],1e-12) for r in rr])),
            'C_native_vs_D_native_on_C_ratio':float(np.mean([r['metrics']['C_full']['C_mse']/max(r['metrics']['D_full']['C_mse'],1e-12) for r in rr])),
            'D_native_vs_C_native_on_D_ratio':float(np.mean([r['metrics']['D_full']['D_mse']/max(r['metrics']['C_full']['D_mse'],1e-12) for r in rr])),
            'C_full_extrema_match':float(np.mean([r['metrics']['C_full']['extrema_match'] for r in rr])),
        }
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'replicates':int(replicates),'seed':int(seed),'K':int(K),'lean_exact_covariance_reversal':lean_covariance_reversal_witness_diagnostics(),'explicit_covariance_reversal_search':reversal,'by_geometry':summary}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=250); p.add_argument('--replicates',type=int,default=300); p.add_argument('--seed',type=int,default=0); p.add_argument('--K',type=int,default=6); p.add_argument('--out',default='research/high_value_extensions/functional/design_summary.json'); a=p.parse_args(argv)
    payload=run(a.instances,a.replicates,a.seed,a.K); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
