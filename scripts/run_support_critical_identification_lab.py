"""Decision-critical joint-support identification.

The learner starts from Omega^- subset Omega subset Omega^+ and queries joint
cells only until the support-regret certificate closes.  Query selection uses
one-step minimax certificate width and never looks at hidden truth before the
chosen cell is queried.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.finite_world import FiniteResponseWorld
from research_chains.support import SupportModel
from research_chains.novelty_completion import support_certificate_state,support_query_update,choose_minimax_support_query,critical_support_cells
from research_chains.provenance import write_artifact_with_provenance
PROTOCOL_VERSION='decision_critical_joint_support_v1'

def _world(rng,m=4):
    sizes=(2,)*int(m); full=list(np.ndindex(*sizes)); p=float(rng.uniform(.35,.8)); omega=[a for a in full if rng.random()<p]
    if not omega: omega=[full[0]]
    # Guarantee every coordinate value appears in truth so relation spans are meaningful.
    for j in range(m):
        for x in range(2):
            if not any(a[j]==x for a in omega): omega.append(next(a for a in full if a[j]==x))
    support=SupportModel(sizes,tuple(sorted(set(omega))),key='truth')
    primitives=tuple(np.asarray([0.,float(rng.choice([-3,-2,-1,1,2,3]))]) for _ in range(m))
    return FiniteResponseWorld(support,primitives)

def _run_strategy(world,k,epsilon,rng,mode):
    full=SupportModel(world.support.action_sizes,world.support.full_product(),key='upper')
    # One known-feasible anchor makes the lower bracket valid/nonempty.
    anchor=world.support.omega[0]; lower=SupportModel(world.support.action_sizes,(anchor,),key='lower'); upper=full
    truth=set(world.support.omega); queries=0
    while True:
        state=support_certificate_state(world,lower,upper,k)
        if state['regret_bound'] <= float(epsilon)+1e-12:
            return queries,state,lower,upper
        unresolved=[a for a in upper.omega if a not in set(lower.omega)]
        if not unresolved: return queries,state,lower,upper
        if mode=='decision_critical': cell=tuple(choose_minimax_support_query(world,lower,upper,k)['cell'])
        elif mode=='random': cell=tuple(unresolved[int(rng.integers(0,len(unresolved)))])
        else: cell=tuple(unresolved[0])
        lower,upper=support_query_update(lower,upper,cell,cell in truth); queries+=1

def run(instances=200,seed=0,m=4,k=2,epsilon=.05):
    rng=np.random.default_rng(seed); rows=[]; false_safe=0
    for idx in range(int(instances)):
        world=_world(rng,int(m)); crit=critical_support_cells(world,world.support,int(k),float(epsilon))
        q,state,lo,hi=_run_strategy(world,int(k),float(epsilon),rng,'decision_critical')
        qr,_,_,_=_run_strategy(world,int(k),float(epsilon),rng,'random')
        candidate=state['candidate']; true_loss=world.additive_radius(candidate,support=world.support)
        true_opt=min(world.additive_radius(S,support=world.support) for S in __import__('itertools').combinations(range(int(m)),int(k)))
        regret=float(true_loss-true_opt); bad=regret>float(epsilon)+1e-10; false_safe+=int(bad)
        rows.append({'queries_decision_critical':q,'queries_random':qr,'full_cells':len(world.support.full_product()),'critical_cells':len(crit),'certified_regret_bound':state['regret_bound'],'true_regret':regret})
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'m':int(m),'k':int(k),'epsilon':float(epsilon),
            'false_safe_count':int(false_safe),'mean_queries_decision_critical':float(np.mean([r['queries_decision_critical'] for r in rows])),
            'mean_queries_random':float(np.mean([r['queries_random'] for r in rows])),
            'mean_query_fraction_of_full_product':float(np.mean([r['queries_decision_critical']/r['full_cells'] for r in rows])),
            'mean_one_cell_critical_witness_count':float(np.mean([r['critical_cells'] for r in rows])),
            'rows':rows[:100]}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=200); p.add_argument('--seed',type=int,default=0); p.add_argument('--m',type=int,default=4); p.add_argument('--k',type=int,default=2); p.add_argument('--epsilon',type=float,default=.05); p.add_argument('--out',default='research/novelty_critical/support_critical_identification.json'); a=p.parse_args(argv)
    out=run(a.instances,a.seed,a.m,a.k,a.epsilon); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'m':a.m,'k':a.k,'epsilon':a.epsilon},seed=a.seed,evidence_class='DEVELOPMENT_EXACT_FINITE_SUPPORT',chain='SUPPORT'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
