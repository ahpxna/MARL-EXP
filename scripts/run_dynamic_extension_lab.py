"""Synthetic drift lab for certificate lifespan under score/reference/support changes."""
from __future__ import annotations
import sys,argparse,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from research_chains.experimental_extensions import kernel_sup_tv,mix_kernel
from research_chains.finite_world import FiniteResponseWorld
from research_chains.pairwise import operational_gamma,pairwise_master_bound
from research_chains.provenance import atomic_json
from research_chains.reference import ConditionalReferenceKernel
from research_chains.certificates import exact_optimum,topk_indices,zeta_def,support_bracket_regret_bound
from research_chains.support import SupportModel,SupportBracket

PROTOCOL_VERSION='dynamic_certificate_lifespan_lab_v1'

def _world(rng,m=5):
    sizes=(2,)*m; full=list(np.ndindex(*sizes)); omega=[a for a in full if rng.random()<.7]
    for j in range(m):
        for x in range(2):
            if not any(a[j]==x for a in omega): omega.append(next(a for a in full if a[j]==x))
    primitives=tuple(rng.normal(size=2) for _ in range(m)); return FiniteResponseWorld(SupportModel(sizes,tuple(sorted(set(omega))),key='t0'),primitives)

def _kernel(world,source,rng):
    full=list(world.support.full_product()); rows={}
    for a in range(2):
        cells=[x for x in full if x[source]==a]; p=rng.dirichlet(np.ones(len(cells))); rows[a]={x:float(v) for x,v in zip(cells,p)}
    return ConditionalReferenceKernel(source,world.support.action_sizes,rows,key='t0')

def run(instances=300,seed=0):
    rng=np.random.default_rng(seed); score_rows=[]; ref_rows=[]; support_rows=[]; query_rows=[]
    for _ in range(int(instances)):
        world=_world(rng); m=world.support.n_relations; k=2; c0=world.component_spans(); noise=rng.normal(scale=.03,size=m); chat=c0+noise; e0=np.abs(noise)+1e-10; drift_bound=float(rng.uniform(0,.25)); drift=rng.uniform(-np.minimum(drift_bound,c0),drift_bound,size=m); ct=c0+drift
        selected=topk_indices(chat,k); gamma0=operational_gamma(chat,e0,k,selected); gamma_inf=operational_gamma(chat,e0+drift_bound,k,selected); z=zeta_def(world,k)
        true_set=set(topk_indices(ct,k)); actual_modular=.5*(float(np.sum(ct[list(true_set)]))-float(np.sum(ct[list(selected)])))
        score_rows.append({'drift_bound':drift_bound,'actual_modular_regret':actual_modular,'old_gamma':gamma0,'inflated_gamma':gamma_inf,'old_violation':actual_modular-gamma0,'inflated_violation':actual_modular-gamma_inf,'selection_changed':int(set(selected)!=true_set)})
        ker=_kernel(world,0,rng); mix=float(rng.uniform(0,.6)); kt=mix_kernel(ker,rng,mix); beta=kernel_sup_tv(ker,kt); comp=[j for j in range(m) if j!=0]; hvals=[sum(float(world.primitives[j][a]) for j,a in zip(comp,vals)) for vals in np.ndindex(*(world.support.action_sizes[j] for j in comp))]; R=float(np.ptp(np.asarray(hvals,float))) if hvals else 0.0; chi0=ker.isolation_deviation(world); chit=kt.isolation_deviation(world); ref_rows.append({'beta':beta,'chi_change':abs(chit-chi0),'rhs':2*R*beta,'violation':abs(chit-chi0)-2*R*beta})
        truth=set(world.support.omega); full=set(world.support.full_product()); lower=[a for a in truth if rng.random()<.6]; lower=lower or [next(iter(truth))]; upper=tuple(sorted(truth|{a for a in full-truth if rng.random()<.3})); bracket=SupportBracket(SupportModel(world.support.action_sizes,tuple(sorted(lower)),key='lower'),SupportModel(world.support.action_sizes,upper,key='upper'))
        candidate=topk_indices(c0,k); bound=support_bracket_regret_bound(world,bracket,candidate,k); opt,_=exact_optimum(world,k); actual=world.additive_radius(candidate)-opt; support_rows.append({'bound':bound,'actual':actual,'violation':actual-bound})
        # Separately typed query-target drift: a previously calibrated target score
        # can be reused with interval inflation e+d; rank stability additionally
        # needs the old pairwise margin to dominate 2d.
        t0=rng.normal(size=m); qnoise=rng.normal(scale=.04,size=m); qhat=t0+qnoise; qe=np.abs(qnoise)+1e-12; qd=float(rng.uniform(0,.25)); shift=rng.uniform(-qd,qd,size=m); tt=t0+shift
        infl=qe+qd; err=np.abs(tt-qhat); qviol=float(np.max(err-infl))
        order=np.argsort(-t0,kind='stable'); gap=float(t0[order[0]]-t0[order[1]]) if m>1 else float('inf'); stable_premise=bool(gap>2*qd); rank_changed=bool(int(np.argmax(tt))!=int(np.argmax(t0)))
        query_rows.append({'drift_bound':qd,'error_inflation_violation':qviol,'old_top_gap':gap,'stable_premise':stable_premise,'rank_changed':rank_changed,'rank_stability_violation':int(stable_premise and rank_changed)})
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'score_drift':{'old_bound_failure_rate':float(np.mean([r['old_violation']>1e-9 for r in score_rows])),'inflated_bound_failure_rate':float(np.mean([r['inflated_violation']>1e-9 for r in score_rows])),'selection_change_rate':float(np.mean([r['selection_changed'] for r in score_rows])),'worst_inflated_violation':float(max(r['inflated_violation'] for r in score_rows))},'reference_drift':{'worst_violation':float(max(r['violation'] for r in ref_rows)),'mean_beta':float(np.mean([r['beta'] for r in ref_rows]))},'support_bracket_lifespan':{'worst_violation':float(max(r['violation'] for r in support_rows)),'mean_bound':float(np.mean([r['bound'] for r in support_rows]))},'query_target_drift':{'worst_error_inflation_violation':float(max(r['error_inflation_violation'] for r in query_rows)),'rank_stability_violation_count':int(sum(r['rank_stability_violation'] for r in query_rows)),'stable_premise_count':int(sum(r['stable_premise'] for r in query_rows)),'rank_change_rate':float(np.mean([r['rank_changed'] for r in query_rows]))}}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=300); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/high_value_extensions/dynamic/summary.json'); a=p.parse_args(argv); payload=run(a.instances,a.seed); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0 if payload['score_drift']['worst_inflated_violation']<=1e-8 and payload['reference_drift']['worst_violation']<=1e-8 and payload['support_bracket_lifespan']['worst_violation']<=1e-8 and payload['query_target_drift']['worst_error_inflation_violation']<=1e-8 and payload['query_target_drift']['rank_stability_violation_count']==0 else 2
if __name__=='__main__': raise SystemExit(main())
