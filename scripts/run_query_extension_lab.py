"""Query extension lab: representation necessity and cross-query semantic transfer."""
from __future__ import annotations
import sys, argparse, json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from scipy.stats import spearmanr,kendalltau
from research_chains.experimental_extensions import representation_necessity_diagnostics, two_world_lower_bound_diagnostics
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='query_representation_transfer_lab_v2'
QUERIES=('sensitivity','direction','information','removal','deletion','causal','synergy','staleness')
METHODS=('C','absD','Info','Removal','Deletion','Causal','Synergy','Freshness','Attention','ShapleyLinear','NonlinearAttr','Random')
FAMILIES=('generic','same_response_diff_info','signed_cancel','high_order_synergy','reference_shift','staleness','limited_support','nonlinear_nullspace','dynamic_interaction','overlapping_groups','cross_query_entangled')

def _rank_metrics(pred,true,k):
    pred=np.asarray(pred,float); true=np.asarray(true,float); k=min(int(k),len(true)); pt=set(np.argsort(-pred,kind='stable')[:k]); tt=set(np.argsort(-true,kind='stable')[:k]); denom=float(np.sum(np.sort(true)[-k:])-np.sum(np.sort(true)[:k]))
    regret=float(np.sum(true[list(tt)])-np.sum(true[list(pt)])); norm=regret/denom if denom>1e-12 else 0.0
    rho=spearmanr(pred,true).statistic; tau=kendalltau(pred,true).statistic
    return {'spearman':0.0 if not np.isfinite(rho) else float(rho),'kendall':0.0 if not np.isfinite(tau) else float(tau),'topk_exact':int(pt==tt),'jaccard':float(len(pt&tt)/max(1,len(pt|tt))),'regret':regret,'normalized_regret':norm}

def _instance(rng,n_rel=10,K=4,family='generic'):
    q=rng.normal(size=(n_rel,K)); w=np.linspace(-1,1,K); w-=w.mean(); w/=np.sum(np.abs(w)); info=np.abs(rng.normal(size=n_rel)); removal=np.abs(rng.normal(size=n_rel)); deletion=np.abs(rng.normal(size=n_rel)); causal=np.abs(rng.normal(size=n_rel)); synergy=np.abs(rng.normal(size=n_rel)); freshness=np.abs(rng.normal(size=n_rel))
    if family=='same_response_diff_info':
        q[1]=q[0]; info[0]=0.; info[1]=3.
    elif family=='signed_cancel':
        q[1]=q[0][::-1]; q[2]=-q[0]
    elif family=='high_order_synergy':
        q[0]=0.; q[1]=0.; synergy[0]=4.; synergy[1]=3.
    elif family=='reference_shift':
        causal[:2]+=3.; q[:2]+=rng.normal(loc=.8,scale=.1,size=(2,K))
    elif family=='staleness':
        freshness[0]=5.; freshness[1]=.01
    elif family=='limited_support':
        q[0]=np.asarray([-2.,-1.,1.,2.])[:K] if K<=4 else np.linspace(-2,2,K); info[0]=3.
    elif family=='nonlinear_nullspace':
        causal[0]=causal[1]=1.; synergy[0]=4.; synergy[1]=0.
    elif family=='dynamic_interaction':
        freshness[0]=5.; deletion[0]=4.; sensitivity=np.ptp(q,axis=1) if 'sensitivity' in locals() else None
    elif family=='overlapping_groups':
        synergy[:min(3,n_rel)]=np.asarray([4.,3.,2.])[:min(3,n_rel)]; deletion[:min(3,n_rel)]+=1.5
    elif family=='cross_query_entangled':
        # Harder synthetic regime: queries share latent causes and methods are
        # imperfect mixtures rather than direct noisy copies of native oracles.
        z=rng.normal(size=(3,n_rel))
        sensitivity=np.abs(.85*z[0]+.30*z[1])
        direction=np.abs(.55*z[0]-.70*z[1]+.15*z[2])
        info=np.abs(.75*z[1]+.25*z[2])
        removal=np.abs(.40*z[0]+.65*z[2])
        deletion=np.abs(.15*z[0]+.60*z[1]+.55*z[2])
        causal=np.abs(.70*z[0]+.15*z[1]+.45*z[2])
        synergy=np.abs(.25*z[0]+.20*z[1]+.80*z[2])
        freshness=np.abs(.10*z[0]+.30*z[1]+.85*z[2])
        truth={'sensitivity':sensitivity,'direction':direction,'information':info,'removal':removal,'deletion':deletion,'causal':causal,'synergy':synergy,'staleness':freshness}
        noise=lambda scale:rng.normal(scale=scale,size=n_rel)
        methods={
            'C':.70*sensitivity+.20*causal+.10*info+noise(.18),
            'absD':.70*direction+.20*causal+.10*removal+noise(.18),
            'Info':.65*info+.20*causal+.15*freshness+noise(.18),
            'Removal':.65*removal+.20*causal+.15*synergy+noise(.18),
            'Deletion':.65*deletion+.20*freshness+.15*info+noise(.18),
            'Causal':.65*causal+.20*removal+.15*sensitivity+noise(.18),
            'Synergy':.65*synergy+.20*causal+.15*removal+noise(.18),
            'Freshness':.65*freshness+.20*deletion+.15*info+noise(.18),
            'Attention':.18*sensitivity+.12*direction+.12*info+.12*removal+.12*deletion+.12*causal+.12*synergy+.10*freshness+noise(.30),
            'ShapleyLinear':.50*causal+.35*removal+.15*sensitivity+noise(.15),
            'NonlinearAttr':.45*causal+.40*synergy+.15*removal+noise(.15),
            'Random':rng.normal(size=n_rel),
        }
        return truth,methods
    sensitivity=np.ptp(q,axis=1); signed=q@w; direction=np.abs(signed)
    truth={'sensitivity':sensitivity,'direction':direction,'information':info,'removal':removal,'deletion':deletion,'causal':causal,'synergy':synergy,'staleness':freshness}
    noise=lambda s:rng.normal(scale=s,size=n_rel)
    methods={
        'C':sensitivity+noise(.05),'absD':direction+noise(.05),'Info':info+noise(.05),'Removal':removal+noise(.05),'Deletion':deletion+noise(.05),'Causal':causal+noise(.05),'Synergy':synergy+noise(.05),'Freshness':freshness+noise(.05),
        'Attention':.20*sensitivity+.15*info+.15*causal+.15*synergy+.15*deletion+.20*freshness+noise(.3),
        'ShapleyLinear':.55*causal+.45*removal+noise(.08),'NonlinearAttr':.55*causal+.45*synergy+noise(.08),'Random':rng.normal(size=n_rel),
    }
    if family=='limited_support':
        methods['C'][0]*=.15; methods['Attention'][0]*=.25
    if family=='nonlinear_nullspace':
        methods['ShapleyLinear'][0]=methods['ShapleyLinear'][1]
    if family=='dynamic_interaction':
        methods['C'][0]*=.4; methods['Freshness'][0]=freshness[0]+noise(.02)[0]
    return truth,methods

def _subset_selection_necessity_witness():
    import itertools
    n=4; k=2; decisions=list(itertools.combinations(range(n),k))
    scores=[np.asarray([4.,3.,1.,0.]),np.asarray([0.,1.,3.,4.])]
    loss=[]; opt=[]; second_gap=[]
    for s in scores:
        vals=np.asarray([float(np.sum(s[list(d)])) for d in decisions])
        best=float(np.max(vals)); row=(best-vals).tolist(); loss.append(row)
        order=np.argsort(-vals,kind='stable'); opt.append(list(decisions[int(order[0])]))
        second_gap.append(float(vals[order[0]]-vals[order[1]]))
    eps=0.5*min(second_gap)
    diag=representation_necessity_diagnostics(loss,[0,0],eps)
    return {'decisions':[list(d) for d in decisions],'scores':[x.tolist() for x in scores],'loss_matrix':loss,'summaries':[0,0],'epsilon':float(eps),'unique_optima':opt,'second_best_gaps':second_gap,'good_set_intersection_empty':diag['common_good_failure_count']==1,'diagnostic':diag}


def run(instances=300,seed=0,n_rel=10,k=3):
    rng=np.random.default_rng(seed); cells={(m,q):[] for m in METHODS for q in QUERIES}; by_family={f:{(m,q):[] for m in METHODS for q in QUERIES} for f in FAMILIES}
    for idx in range(int(instances)):
        family=FAMILIES[idx%len(FAMILIES)]; truth,methods=_instance(rng,n_rel=n_rel,family=family)
        for m in METHODS:
            for q in QUERIES:
                r=_rank_metrics(methods[m],truth[q],k); cells[(m,q)].append(r); by_family[family][(m,q)].append(r)
    def agg(rows):
        keys=('spearman','kendall','topk_exact','jaccard','regret','normalized_regret')
        if not rows: return {key:None for key in keys}
        return {key:float(np.mean([r[key] for r in rows])) for key in keys}
    matrix={m:{q:agg(cells[(m,q)]) for q in QUERIES} for m in METHODS}
    family_summary={f:{m:{q:agg(by_family[f][(m,q)]) for q in QUERIES} for m in METHODS} for f in FAMILIES}
    native={'C':'sensitivity','absD':'direction','Info':'information','Removal':'removal','Deletion':'deletion','Causal':'causal','Synergy':'synergy','Freshness':'staleness','ShapleyLinear':'causal','NonlinearAttr':'synergy'}
    native_adv={}
    for m,q in native.items():
        own=matrix[m][q]['normalized_regret']; foreign=[matrix[m][qq]['normalized_regret'] for qq in QUERIES if qq!=q]
        native_adv[m]={'native_query':q,'native_regret':own,'mean_foreign_regret':float(np.mean(foreign)),'native_better_than_mean_foreign':bool(own<float(np.mean(foreign)))}
    native_by_regime={'aligned':{},'cross_query_entangled':{}}
    aligned_families=[f for f in FAMILIES if f!='cross_query_entangled']
    for m,q in native.items():
        aligned_own=[]; aligned_foreign=[]
        for f in aligned_families:
            own=family_summary[f][m][q]['normalized_regret']
            if own is not None: aligned_own.append(own)
            for qq in QUERIES:
                if qq==q: continue
                value=family_summary[f][m][qq]['normalized_regret']
                if value is not None: aligned_foreign.append(value)
        ent=family_summary['cross_query_entangled'][m]
        ent_own=ent[q]['normalized_regret']
        ent_foreign=[ent[qq]['normalized_regret'] for qq in QUERIES if qq!=q and ent[qq]['normalized_regret'] is not None]
        native_by_regime['aligned'][m]={'native_query':q,'native_regret':float(np.mean(aligned_own)) if aligned_own else None,'mean_foreign_regret':float(np.mean(aligned_foreign)) if aligned_foreign else None}
        native_by_regime['cross_query_entangled'][m]={'native_query':q,'native_regret':ent_own,'mean_foreign_regret':float(np.mean(ent_foreign)) if ent_foreign else None,'native_better_than_mean_foreign':bool(ent_own is not None and ent_foreign and ent_own<float(np.mean(ent_foreign)))}
    # Representation-necessity stress: collide summaries for worlds with separated optima.
    necessity={}
    base_loss=np.asarray([[0.,2.,4.],[3.,0.,4.],[3.,4.,0.],[0.1,0.,3.]])
    summaries=np.asarray([0,0,1,1])
    for eps in (0.,.05,.25,1.0,2.5): necessity[str(eps)]=representation_necessity_diagnostics(base_loss,summaries,eps)
    unique_conflict={'loss_matrix':base_loss.tolist(),'summaries':summaries.tolist(),'epsilon_0_common_good_failures':necessity['0.0']['common_good_failure_count']}
    subset_witness=_subset_selection_necessity_witness()
    lower_rows=[]
    for _ in range(max(1000,int(instances)*5)):
        t1=float(rng.normal()); t2=float(rng.normal()); psi=float(rng.normal())
        lower_rows.append(two_world_lower_bound_diagnostics(t1,t2,psi))
    exact_lower=two_world_lower_bound_diagnostics(0.0,2.0,1.0)
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'queries':QUERIES,'methods':METHODS,'families':FAMILIES,'transfer_matrix':matrix,'by_challenge_family':family_summary,'native_query_advantage':native_adv,'native_query_advantage_by_regime':native_by_regime,'benchmark_scope':'synthetic semantic stress test; cross_query_entangled reduces direct native-oracle alignment but does not replace external baselines','representation_necessity':necessity,'unique_optimum_conflict':unique_conflict,'subset_selection_necessity_witness':subset_witness,'two_world_lower_bound':{'exact_midpoint_witness':exact_lower,'worst_violation':float(max(r['violation'] for r in lower_rows)),'mean_slack':float(np.mean([r['worst_error']-r['half_separation'] for r in lower_rows])),'random_cases':len(lower_rows)}}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=300); p.add_argument('--seed',type=int,default=0); p.add_argument('--n-rel',type=int,default=10); p.add_argument('--k',type=int,default=3); p.add_argument('--out',default='research/high_value_extensions/query/summary.json'); a=p.parse_args(argv)
    payload=run(a.instances,a.seed,a.n_rel,a.k); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
