"""D6 extension lab: applicability, sharpness, q-sensitive candidates, and stress families."""
from __future__ import annotations
import sys
from pathlib import Path as _Path
_ROOT=_Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path: sys.path.insert(0,str(_ROOT))
import argparse,json,itertools
from pathlib import Path
import numpy as np
from research_chains.experimental_extensions import d6_diagnostics,d6_sharpness_search,d6_decision_adversarial_search,product_anova_decomposition,arbitrary_full_world
from research_chains.finite_world import FiniteResponseWorld
from research_chains.provenance import atomic_json
from research_chains.support import SupportModel

PROTOCOL_VERSION='d6_extension_lab_v2'

def _interaction_table(rng,m,kind,alpha):
    shape=(2,)*m; arr=np.zeros(shape,dtype=float)
    if kind=='pairwise_sparse':
        pairs=[(0,1)] if m>=2 else []
    elif kind=='pairwise_dense':
        pairs=list(itertools.combinations(range(m),2))
    else: pairs=[]
    for a in np.ndindex(*shape):
        x=np.asarray([2*v-1 for v in a],dtype=float); val=0.0
        if pairs: val+=sum(x[i]*x[j] for i,j in pairs)
        if kind=='third_order' and m>=3: val+=x[0]*x[1]*x[2]
        if kind=='spike': val+=float(all(v==1 for v in a))*max(1,m)
        if kind=='adversarial_cancellation':
            val+=sum(((-1)**(i+j))*x[i]*x[j] for i,j in itertools.combinations(range(m),2))
        arr[a]=alpha*val
    return arr

def _world(rng,m,kind,alpha):
    shape=(2,)*m; full=tuple(np.ndindex(*shape)); primitives=tuple(rng.normal(scale=.5,size=2) for _ in range(m)); residual={}
    interact=_interaction_table(rng,m,kind,alpha)
    for a in full: residual[a]=float(interact[a])
    return FiniteResponseWorld(SupportModel(shape,full,key='full'),primitives,residual=residual)

def run(instances=500,seed=0,sharpness_instances=5000,adversarial_instances=0,adversarial_steps=25):
    rng=np.random.default_rng(seed); kinds=('pairwise_sparse','pairwise_dense','third_order','spike','adversarial_cancellation'); alphas=(0.0,.05,.1,.25,.5,1.0)
    rows=[]; violations={'worst':0.0,'decision':0.0,'decision_half_candidate':0.0,'coord':0.0,'qavg_uniform':0.0,'qsigned_uniform':0.0,'qavg_pointwise_uniform':0.0,'qsigned_pointwise_uniform':0.0,'qavg_distributional':0.0,'qsigned_distributional':0.0,'residual_identity':0.0,'qL1_conditional':0.0}
    for idx in range(int(instances)):
        m=3+(idx%3); kind=kinds[idx%len(kinds)]; alpha=alphas[(idx//len(kinds))%len(alphas)]; world=_world(rng,m,kind,alpha)
        marg={j:rng.dirichlet(np.ones(2)) for j in range(m)}; k=int(rng.integers(1,m+1)); d=d6_diagnostics(world,marg,k)
        if not d.get('applicable'): raise RuntimeError('constructed full-product world unexpectedly inapplicable')
        violations['worst']=max(violations['worst'],d['worst_case_violation']); violations['decision']=max(violations['decision'],d['decision_violation']); violations['decision_half_candidate']=max(violations['decision_half_candidate'],d['decision_candidate_half_violation']); violations['coord']=max(violations['coord'],d['coordinate_sum_violation']); violations['qavg_uniform']=max(violations['qavg_uniform'],d['qavg_uniform_candidate_violation']); violations['qsigned_uniform']=max(violations['qsigned_uniform'],d['qsigned_uniform_candidate_violation']); violations['qavg_pointwise_uniform']=max(violations['qavg_pointwise_uniform'],d['qavg_pointwise_uniform_violation']); violations['qsigned_pointwise_uniform']=max(violations['qsigned_pointwise_uniform'],d['qsigned_pointwise_uniform_violation']); violations['qavg_distributional']=max(violations['qavg_distributional'],d['qavg_distributional_candidate_violation']); violations['qsigned_distributional']=max(violations['qsigned_distributional'],d['qsigned_distributional_candidate_violation']); violations['residual_identity']=max(violations['residual_identity'],d['residual_identity_worst_error']);
        if d['qL1']['conditional_violation'] is not None: violations['qL1_conditional']=max(violations['qL1_conditional'],d['qL1']['conditional_violation'])
        anova=product_anova_decomposition(world,marg)
        rows.append({'kind':kind,'alpha':alpha,'m':m,'k':k,'anova_higher_order_l2_mass':anova['higher_order_l2_mass'],'anova_reconstruction_sup_error':anova['reconstruction_sup_error'], 'qL1_topc_surrogate_optimal':d['qL1']['topc_surrogate_optimal'],'qL1_true_regret':d['qL1']['true_regret'],'qL1_transfer_rhs':d['qL1']['transfer_rhs'],'qL1_conditional_violation':d['qL1']['conditional_violation'], **{x:d[x] for x in ('delta_square','surrogate_sup_error','surrogate_expected_abs_q','worst_case_rhs','coordinate_sum_rhs','qavg_sum_rhs','qsigned_sum_rhs','qavg_pointwise_uniform_rhs','qsigned_pointwise_uniform_rhs','qavg_distributional_rhs','qsigned_distributional_rhs','residual_identity_worst_error','surrogate_tightness','true_decision_regret','decision_rhs','decision_candidate_half_rhs','decision_candidate_half_violation','decision_tightness','decision_ratio_to_worst_rhs','qavg_uniform_candidate_violation','qsigned_uniform_candidate_violation','qavg_pointwise_uniform_violation','qsigned_pointwise_uniform_violation','qavg_distributional_candidate_violation','qsigned_distributional_candidate_violation')}})
    by={}
    for kind in kinds:
        by[kind]={}
        for alpha in alphas:
            rr=[r for r in rows if r['kind']==kind and r['alpha']==alpha]
            if not rr: continue
            sur_vals=[r["surrogate_tightness"] for r in rr if np.isfinite(r["surrogate_tightness"])]
            dec_vals=[r["decision_tightness"] for r in rr if np.isfinite(r["decision_tightness"])]
            by[kind][str(alpha)]={
                "n":len(rr),
                "mean_delta_square":float(np.mean([r["delta_square"] for r in rr])),
                "mean_surrogate_tightness":float(np.mean(sur_vals)) if sur_vals else None,
                "mean_decision_tightness":float(np.mean(dec_vals)) if dec_vals else None,
                "qavg_uniform_safe_fraction":float(np.mean([r["qavg_uniform_candidate_violation"]<=1e-10 for r in rr])),
                "qsigned_uniform_safe_fraction":float(np.mean([r["qsigned_uniform_candidate_violation"]<=1e-10 for r in rr])),
                "qavg_distributional_safe_fraction":float(np.mean([r["qavg_distributional_candidate_violation"]<=1e-10 for r in rr])),
                "qsigned_distributional_safe_fraction":float(np.mean([r["qsigned_distributional_candidate_violation"]<=1e-10 for r in rr])),
                "decision_half_candidate_safe_fraction":float(np.mean([r["decision_candidate_half_violation"]<=1e-10 for r in rr])),
                "qL1_surrogate_optimal_fraction":float(np.mean([r["qL1_topc_surrogate_optimal"] for r in rr])),
                "qL1_conditional_safe_fraction":float(np.mean([True if r["qL1_conditional_violation"] is None else r["qL1_conditional_violation"]<=1e-10 for r in rr])),
            }

    # Explicit assumption rejection checks.
    partial=_world(rng,3,'pairwise_sparse',.2); partial_support=SupportModel(partial.support.action_sizes,tuple(partial.support.omega[:-1]),key='partial'); inapp=FiniteResponseWorld(partial_support,partial.primitives,residual=partial.residual); rejection=d6_diagnostics(inapp,{j:[.5,.5] for j in range(3)},1)
    delta=np.asarray([r['delta_square'] for r in rows]); mass=np.asarray([r['anova_higher_order_l2_mass'] for r in rows]); regret=np.asarray([r['true_decision_regret'] for r in rows])
    from scipy.stats import spearmanr
    def rho(x,y):
        x=np.asarray(x,float); y=np.asarray(y,float)
        if x.size<2 or y.size<2 or np.allclose(x,x[0]) or np.allclose(y,y[0]): return 0.0
        v=spearmanr(x,y).statistic; return 0.0 if not np.isfinite(v) else float(v)
    anova_compare={'delta_vs_higher_order_mass_spearman':rho(delta,mass),'higher_order_mass_vs_decision_regret_spearman':rho(mass,regret),'delta_vs_decision_regret_spearman':rho(delta,regret),'max_reconstruction_error':float(max(r['anova_reconstruction_sup_error'] for r in rows))}
    # Exact experimental reproduction of the formal S1 AND-world witness.
    and_world=arbitrary_full_world(np.asarray([[0.,0.],[0.,1.]],dtype=float))
    s1_exact=d6_diagnostics(and_world,{0:[1.,0.],1:[1.,0.]},1)
    decision_ratio_den=np.asarray([r['worst_case_rhs'] for r in rows],float)
    decision_ratio=np.asarray([r['true_decision_regret'] for r in rows],float)/np.maximum(decision_ratio_den,1e-12)
    ql1_rows=[r for r in rows if r['qL1_topc_surrogate_optimal']]
    adversarial=(d6_decision_adversarial_search(instances=int(adversarial_instances),steps=int(adversarial_steps),seed=seed+313) if int(adversarial_instances)>0 else {'instances':0,'steps':int(adversarial_steps),'seed':seed+313,'candidate_ratio_threshold':0.5,'best_ratio_to_worst_rhs':None,'candidate_killed':False,'best_witness':None})
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'lean_alignment':{'hybrid_telescoping':True,'s1_exact_reproduction':{'surrogate_tightness':s1_exact['surrogate_tightness'],'delta_square':s1_exact['delta_square'],'surrogate_sup_error':s1_exact['surrogate_sup_error'],'residual_identity_worst_error':s1_exact['residual_identity_worst_error']}},'worst_candidate_violations':violations,'stress_by_family':by,'sharpness':d6_sharpness_search(instances=int(sharpness_instances),seed=seed+99),'decision_improvement_candidate':{'candidate_rhs':'(m-1)*delta_square/2','safe_fraction':float(np.mean([r['decision_candidate_half_violation']<=1e-10 for r in rows])),'worst_violation':float(max(r['decision_candidate_half_violation'] for r in rows)),'max_regret_over_original_approx_rhs':float(np.max(decision_ratio)),'adversarial_search':adversarial},'qL1_distributional':{'surrogate_optimal_fraction':float(np.mean([r['qL1_topc_surrogate_optimal'] for r in rows])),'conditional_cases':len(ql1_rows),'conditional_worst_violation':float(max([r['qL1_conditional_violation'] for r in ql1_rows],default=0.0))},'assumption_rejection':rejection,'anova_comparison':anova_compare}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=500); p.add_argument('--sharpness-instances',type=int,default=5000); p.add_argument('--adversarial-instances',type=int,default=500); p.add_argument('--adversarial-steps',type=int,default=25); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/high_value_extensions/d6/summary.json'); a=p.parse_args(argv)
    payload=run(a.instances,a.seed,a.sharpness_instances,a.adversarial_instances,a.adversarial_steps); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0 if payload['worst_candidate_violations']['worst']<=1e-8 and payload['worst_candidate_violations']['decision']<=1e-8 else 2
if __name__=='__main__': raise SystemExit(main())
