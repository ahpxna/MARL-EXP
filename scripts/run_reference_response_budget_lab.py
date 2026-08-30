"""Joint response/reference budget experiment for the MASTER→Functional bridge.

A total per-relation budget is split between direct response estimation and
conditional reference-kernel estimation.  The experiment reports the six
pre-registered endpoints requested by the research plan: Q error, kernel TV,
chi error, final score interval width, Top-K regret, and certificate coverage.
"""
from __future__ import annotations
import argparse, itertools, json, math
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np

from research_chains.experimental_extensions import empirical_kernel_from_counts, kernel_sup_tv, reference_uncertainty_diagnostics
from research_chains.finite_world import FiniteResponseWorld
from research_chains.reference import ConditionalReferenceKernel
from research_chains.support import SupportModel
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='reference_response_budget_split_v1'


def _random_world(rng,m=4,K=3):
    support=SupportModel((K,)*m,tuple(np.ndindex(*((K,)*m))),key='budget_full')
    primitives=[]
    for j in range(m):
        v=rng.normal(size=K); v-=v.mean(); scale=rng.uniform(.4,1.5); v*=scale/max(np.ptp(v),1e-12); primitives.append(v)
    # modest interaction keeps reference response nontrivial without changing primitive target definition
    residual={a:float(rng.normal(scale=.03)) for a in support.omega}
    return FiniteResponseWorld(support,tuple(primitives),residual=residual)


def _random_kernel(rng,world,source):
    sizes=world.support.action_sizes; other=[j for j in range(len(sizes)) if j!=source]; rows={}
    for a in range(sizes[source]):
        cells=[]
        for vals in itertools.product(*(range(sizes[j]) for j in other)):
            joint=[0]*len(sizes); joint[source]=a
            for j,v in zip(other,vals): joint[j]=v
            cells.append(tuple(joint))
        # action-dependent concentrated rows create a real reference-identification problem
        alpha=rng.uniform(.15,1.5,size=len(cells)); p=rng.dirichlet(alpha)
        rows[a]={cell:float(prob) for cell,prob in zip(cells,p)}
    return ConditionalReferenceKernel(source,sizes,rows,key=f'truth_{source}')


def _draw_kernel_row(rng,kernel,a,n):
    cells=list(kernel.by_source_action[a]); p=np.asarray([kernel.by_source_action[a][x] for x in cells],float); idx=rng.choice(len(cells),size=int(n),p=p)
    return [cells[int(i)] for i in idx]


def _estimate_relation(rng,world,kernel,nQ,nK,alpha,m_rel):
    source=kernel.source; K=world.support.action_sizes[source]
    # Direct Q samples, balanced over source actions, bounded by the finite world's exact range.
    q_true=kernel.response_vector(world,true_response=True); qhat=np.zeros(K); qrad=np.zeros(K)
    full_values=np.asarray([world.true_value(a) for a in world.support.full_product()],float); value_range=max(float(np.ptp(full_values)),1e-12)
    baseQ=max(1,int(nQ)//K); rem=max(0,int(nQ)-baseQ*K); allocQ=np.full(K,baseQ,int); allocQ[:rem]+=1
    delta_piece=max(1e-12,float(alpha)/(4*m_rel*K))
    for a in range(K):
        cells=_draw_kernel_row(rng,kernel,a,int(allocQ[a])); vals=np.asarray([world.true_value(x) for x in cells],float)
        qhat[a]=float(vals.mean()); qrad[a]=value_range*math.sqrt(math.log(2.0/delta_piece)/(2.0*max(1,len(vals))))
    q_error=float(np.max(np.abs((qhat-qhat.mean())-(q_true-q_true.mean()))))

    # Kernel samples, balanced source actions.  A union-Hoeffding TV envelope is intentionally conservative.
    baseK=max(1,int(nK)//K); remK=max(0,int(nK)-baseK*K); allocK=np.full(K,baseK,int); allocK[:remK]+=1
    counts={a:{} for a in range(K)}
    other=[j for j in range(len(world.support.action_sizes)) if j!=source]
    d=int(np.prod([world.support.action_sizes[j] for j in other]))
    tv_row_bounds=[]
    for a in range(K):
        cells=_draw_kernel_row(rng,kernel,a,int(allocK[a]))
        for x in cells: counts[a][x]=counts[a].get(x,0)+1
        eps_cat=math.sqrt(math.log(2.0*d/max(delta_piece,1e-12))/(2.0*max(1,int(allocK[a]))))
        tv_row_bounds.append(min(1.0,0.5*d*eps_cat))
    khat=empirical_kernel_from_counts(source=source,action_sizes=world.support.action_sizes,counts=counts,smoothing=.5,key='budget_hat')
    kernel_tv=kernel_sup_tv(kernel,khat); diag=reference_uncertainty_diagnostics(world,kernel,khat)
    tv_cert=float(max(tv_row_bounds))

    measured=float(np.ptp(qhat)); primitive=float(world.component_span(source)); stat_radius=float(2*np.max(qrad))
    # RU3-style same-target radius: statistical span error + estimated isolation + kernel uncertainty.
    ref_radius=float(diag['chi_hat']+2.0*diag['complement_span']*tv_cert)
    total_radius=stat_radius+ref_radius
    return {
        'primitive_score':primitive,'score_hat':measured,'score_lo':measured-total_radius,'score_hi':measured+total_radius,
        'Q_error':q_error,'kernel_tv':float(kernel_tv),'chi_error':float(diag['chi_abs_error']),
        'final_score_interval_width':float(2*total_radius),'certificate_score_covered':bool(abs(measured-primitive)<=total_radius+1e-12),
        'stat_radius':stat_radius,'reference_radius':ref_radius,'kernel_tv_cert_radius':tv_cert,
    }


def run(instances=500,seeds=(100,101,102,103,104),budgets=(64,128,256,512),splits=(0.1,0.2,0.3,0.5,0.7,0.9),relations=4,actions=3,topk=2,alpha=.05):
    rows={str(B):{str(float(s)):[] for s in splits} for B in budgets}
    for seed in seeds:
        rng=np.random.default_rng(int(seed))
        for _ in range(int(instances)):
            world=_random_world(rng,int(relations),int(actions)); kernels=[_random_kernel(rng,world,j) for j in range(int(relations))]
            true_scores=np.asarray([world.component_span(j) for j in range(int(relations))]); optimal=set(np.argsort(-true_scores,kind='stable')[:int(topk)])
            for B in budgets:
                for split in splits:
                    # split = fraction devoted to reference-kernel estimation
                    nK=max(int(actions),int(round(float(B)*float(split)))); nQ=max(int(actions),int(B)-nK)
                    rel=[_estimate_relation(rng,world,kernels[j],nQ,nK,float(alpha),int(relations)) for j in range(int(relations))]
                    score=np.asarray([r['score_hat'] for r in rel]); chosen=set(np.argsort(-score,kind='stable')[:int(topk)])
                    regret=float(sum(true_scores[list(optimal)])-sum(true_scores[list(chosen)]))
                    lo=np.asarray([r['score_lo'] for r in rel]); hi=np.asarray([r['score_hi'] for r in rel]); chosen_idx=np.argsort(-score,kind='stable')[:int(topk)]; outside=[j for j in range(int(relations)) if j not in set(chosen_idx)]
                    cert=bool(np.min(lo[chosen_idx])>np.max(hi[outside])) if outside else True
                    rows[str(B)][str(float(split))].append({
                        'Q_error':float(np.mean([r['Q_error'] for r in rel])),
                        'kernel_tv':float(np.mean([r['kernel_tv'] for r in rel])),
                        'chi_error':float(np.mean([r['chi_error'] for r in rel])),
                        'final_score_interval_width':float(np.mean([r['final_score_interval_width'] for r in rel])),
                        'topk_regret':regret,'certificate_coverage':float(np.mean([r['certificate_score_covered'] for r in rel])),
                        'topk_certified':int(cert),'false_safe':int(cert and chosen!=optimal),'nQ':int(nQ),'nKappa':int(nK),
                    })
    summary={}
    for B,by in rows.items():
        summary[B]={}
        for s,rr in by.items():
            summary[B][s]={key:float(np.mean([r[key] for r in rr])) for key in ('Q_error','kernel_tv','chi_error','final_score_interval_width','topk_regret','certificate_coverage','topk_certified','false_safe')}
            summary[B][s]['mean_nQ']=float(np.mean([r['nQ'] for r in rr])); summary[B][s]['mean_nKappa']=float(np.mean([r['nKappa'] for r in rr]))
    best={B:{endpoint:min(by,key=lambda s:by[s][endpoint]) for endpoint in ('Q_error','kernel_tv','chi_error','final_score_interval_width','topk_regret')} for B,by in summary.items()}
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'split_semantics':'split is B_kappa / (B_Q+B_kappa)','instances_per_seed':int(instances),'seeds':list(map(int,seeds)),'budgets_per_relation':list(map(int,budgets)),'splits':list(map(float,splits)),'relations':int(relations),'actions':int(actions),'topk':int(topk),'alpha':float(alpha),'required_metrics':['Q_error','kernel_tv','chi_error','final_score_interval_width','topk_regret','certificate_coverage'],'by_budget':summary,'best_split_by_endpoint':best}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=500); p.add_argument('--seeds',nargs='+',type=int,default=[100,101,102,103,104]); p.add_argument('--budgets',nargs='+',type=int,default=[64,128,256,512]); p.add_argument('--splits',nargs='+',type=float,default=[.1,.2,.3,.5,.7,.9]); p.add_argument('--relations',type=int,default=4); p.add_argument('--actions',type=int,default=3); p.add_argument('--topk',type=int,default=2); p.add_argument('--alpha',type=float,default=.05); p.add_argument('--out',default='research/high_value_extensions/master/reference_response_budget.json'); a=p.parse_args(argv)
    payload=run(a.instances,tuple(a.seeds),tuple(a.budgets),tuple(a.splits),a.relations,a.actions,a.topk,a.alpha); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
