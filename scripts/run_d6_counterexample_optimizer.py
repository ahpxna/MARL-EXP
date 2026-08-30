"""Counterexample-directed optimizer for the open D6 half-factor conjecture."""
from __future__ import annotations
import argparse,json,math
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from research_chains.experimental_extensions import arbitrary_full_world,d6_diagnostics
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='d6_counterexample_optimizer_v1'

def _score(values,m,k,q):
    d=d6_diagnostics(arbitrary_full_world(values),q,k); rhs=float(d['worst_case_rhs'])
    return (float(d['true_decision_regret'])/rhs if rhs>1e-12 else 0.0),d

def run(restarts=2000,steps=200,m=3,alphabet=2,k=1,seed=0,value_clip=8.0,temp0=.5):
    rng=np.random.default_rng(int(seed)); shape=(int(alphabet),)*int(m); q={j:np.full(int(alphabet),1.0/int(alphabet)) for j in range(int(m))}; best=(-1.0,None,None); killed=False
    for _ in range(int(restarts)):
        x=rng.integers(-3,4,size=shape).astype(float); current,dc=_score(x,m,k,q); temp=float(temp0)
        if current>best[0]: best=(current,x.copy(),dc)
        for _step in range(int(steps)):
            y=x.copy(); idx=tuple(int(rng.integers(0,s)) for s in shape); y[idx]=np.clip(y[idx]+rng.choice([-2.,-1.,1.,2.]),-float(value_clip),float(value_clip))
            score,dy=_score(y,m,k,q); accept=score>=current or rng.random()<math.exp((score-current)/max(temp,1e-8))
            if accept: x,current,dc=y,score,dy
            if score>best[0]: best=(score,y.copy(),dy)
            if score>0.5+1e-12: killed=True; break
            temp*=.985
        if killed: break
    ratio,values,d=best
    witness=None if values is None else {'values':values.tolist(),'m':int(m),'k':int(k),'ratio_regret_over_approx_rhs':float(ratio),'delta_square':float(d['delta_square']),'decision_regret':float(d['true_decision_regret']),'approximation_rhs':float(d['worst_case_rhs']),'candidate_half_rhs':float(d['decision_candidate_half_rhs']),'candidate_violation':float(d['decision_candidate_half_violation']),'chosen_topc':d['chosen_topc'],'exact_optimal_sets':d['exact_optimal_sets']}
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'DIRECTED_FALSIFICATION_NOT_PROOF','candidate_threshold':0.5,'candidate_killed':bool(killed),'restarts_requested':int(restarts),'steps_per_restart':int(steps),'seed':int(seed),'m':int(m),'alphabet':int(alphabet),'k':int(k),'best_witness':witness}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--restarts',type=int,default=2000); p.add_argument('--steps',type=int,default=200); p.add_argument('--m',type=int,default=3); p.add_argument('--alphabet',type=int,default=2); p.add_argument('--k',type=int,default=1); p.add_argument('--seed',type=int,default=100); p.add_argument('--value-clip',type=float,default=8); p.add_argument('--out',default='research/high_value_extensions/d6/counterexample_optimizer.json'); a=p.parse_args(argv)
    payload=run(a.restarts,a.steps,a.m,a.alphabet,a.k,a.seed,a.value_clip); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 2 if payload['candidate_killed'] else 0
if __name__=='__main__': raise SystemExit(main())
