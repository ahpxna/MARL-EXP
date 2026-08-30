"""Controlled C-vs-D regularity and query-design laboratory."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, json
from pathlib import Path
import numpy as np

from research_chains.functionals import (
    capacity, direction, extrema_gaps, neyman_allocation,
    linear_contrast_variance, simultaneous_capacity_interval, split_capacity,
)
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='chain_a_functional_regularity_lab_v2'


def _truth(regime,K):
    if regime=='null': return np.zeros(K)
    if regime=='near_tie':
        q=np.linspace(-0.5,0.5,K); q[-2]=q[-1]-0.02; q[1]=q[0]+0.02; return q
    if regime=='unique': return np.linspace(-1.0,1.0,K)
    raise ValueError(regime)


def run(replicates=2000,seed=0,K=8,n_per_action=40):
    rng=np.random.default_rng(seed); regimes={}; weights=np.linspace(-1,1,K); weights-=weights.mean(); weights/=np.sum(np.abs(weights)); sigmas=np.linspace(0.7,1.3,K)
    budget=float(K*n_per_action); uniform=np.full(K,budget/K); targeted=neyman_allocation(weights,sigmas,budget,floor=max(1.0,0.1*n_per_action))
    for regime in ('unique','near_tie','null'):
        q=_truth(regime,K); true_c=capacity(q); true_d=direction(q,weights); rows=[]
        for _ in range(int(replicates)):
            se=sigmas/np.sqrt(n_per_action); a=q+rng.normal(scale=se); b=q+rng.normal(scale=se)
            plugin=capacity(a); split=split_capacity(a,b); cross=0.5*(split_capacity(a,b)+split_capacity(b,a)); lo,hi,_,_=simultaneous_capacity_interval(a,se,alpha=0.05); d=direction(a,weights)
            rows.append((plugin,split,cross,lo,hi,d))
        arr=np.asarray(rows)
        regimes[regime]={
            'true_C':true_c,'true_D':true_d,'gap':extrema_gaps(q)['g'],
            'plugin_C_bias':float(np.mean(arr[:,0]-true_c)),
            'split_C_bias':float(np.mean(arr[:,1]-true_c)),
            'crosssplit_C_bias':float(np.mean(arr[:,2]-true_c)),
            'simultaneous_C_coverage':float(np.mean((arr[:,3]-1e-12<=true_c)&(true_c<=arr[:,4]+1e-12))),
            'D_bias':float(np.mean(arr[:,5]-true_d)),
            'C_null_fpr_gt_0':float(np.mean(arr[:,0]>0)) if regime=='null' else None,
        }
    return {
        'protocol_version':PROTOCOL_VERSION,'development_only':True,'replicates':int(replicates),'seed':int(seed),
        'regimes':regimes,
        'design':{
            'uniform_variance':linear_contrast_variance(weights,sigmas,uniform),
            'targeted_variance':linear_contrast_variance(weights,sigmas,targeted),
            'uniform_allocation':uniform.tolist(),'targeted_allocation':targeted.tolist(),
            'same_budget':bool(np.isclose(uniform.sum(),targeted.sum())),
        },
    }


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--replicates',type=int,default=2000); p.add_argument('--seed',type=int,default=0); p.add_argument('--K',type=int,default=8); p.add_argument('--n-per-action',type=int,default=40); p.add_argument('--out',default='research/new_chains_v2/chain_a/summary.json'); a=p.parse_args(argv)
    payload=run(a.replicates,a.seed,a.K,a.n_per_action); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
