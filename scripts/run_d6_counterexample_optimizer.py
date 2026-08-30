"""Counterexample-directed optimizer for the open D6 half-factor conjecture."""
from __future__ import annotations
import argparse,json,math
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import itertools
import numpy as np
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='d6_counterexample_optimizer_v1'

def _actions(m, alphabet):
    return tuple(itertools.product(range(alphabet), repeat=m))

def _update(x, i, u):
    y=list(x); y[i]=u; return tuple(y)

def _evaluate(values,m,k,q):
    alphabet=int(values.shape[0]); actions=_actions(m,alphabet)
    def weight(a): return float(np.prod([q[j][a[j]] for j in range(m)]))
    weights={a:weight(a) for a in actions}
    b=sum(weights[a]*float(values[a]) for a in actions)
    rows=[]
    for j in range(m):
        rows.append(tuple(sum(weights[c]*float(values[_update(c,j,u)]) for c in actions)
                          for u in range(alphabet)))
    surrogate={a:sum(rows[j][a[j]] for j in range(m))-(m-1)*b for a in actions}
    sup=max(abs(float(values[a])-surrogate[a]) for a in actions)
    delta=0.0
    for i in range(m):
        for x in actions:
            for c in actions:
                d=(float(values[x])-float(values[_update(x,i,c[i])])-
                   float(values[_update(c,i,x[i])])+float(values[c]))
                delta=max(delta,abs(d))
    score=[max(row)-min(row) for row in rows]
    order=sorted(range(m),key=lambda j:(-score[j],j)); chosen=tuple(sorted(order[:k]))
    components=[tuple(v-b for v in row) for row in rows]
    def loss(S):
        S=set(S)
        residual=[float(values[a])-sum(components[j][a[j]] for j in S) for a in actions]
        return (max(residual)-min(residual))/2
    subset_losses=[(S,loss(S)) for S in itertools.combinations(range(m),k)]
    optimum=min(v for _,v in subset_losses); regret=loss(chosen)-optimum
    rhs=(m-1)*delta
    exact=[list(S) for S,v in subset_losses if abs(v-optimum)<=1e-10]
    return {'delta_square':delta,'product_surrogate_sup_error':sup,
            'worst_case_rhs':rhs,'true_decision_regret':regret,
            'decision_candidate_half_rhs':rhs/2,
            'decision_candidate_half_violation':regret-rhs/2,
            'chosen_topc':list(chosen),'exact_optimal_sets':exact,
            'reference_q':{str(j):q[j].tolist() for j in range(m)}}

def _score(values,m,k,q):
    d=_evaluate(values,m,k,q); rhs=float(d['worst_case_rhs'])
    return (float(d['true_decision_regret'])/rhs if rhs>1e-12 else 0.0),d

def _sample_q(rng,m,alphabet,mode):
    if mode=='uniform': return {j:np.full(alphabet,1/alphabet) for j in range(m)}
    if mode=='boundary':
        return {j:np.eye(alphabet)[int(rng.integers(0,alphabet))] for j in range(m)}
    if mode=='skewed':
        return {j:rng.dirichlet(np.full(alphabet,.12)) for j in range(m)}
    if mode=='random':
        return {j:rng.dirichlet(np.ones(alphabet)) for j in range(m)}
    raise ValueError(f'unknown q mode: {mode}')

def run(restarts=2000,steps=200,m=3,alphabet=2,k=1,seed=0,value_clip=8.0,temp0=.5,q_mode='uniform',optimize_q=False):
    rng=np.random.default_rng(int(seed)); shape=(int(alphabet),)*int(m); best=(-1.0,None,None); killed=False
    for _ in range(int(restarts)):
        q=_sample_q(rng,int(m),int(alphabet),q_mode)
        x=rng.integers(-3,4,size=shape).astype(float); current,dc=_score(x,m,k,q); temp=float(temp0)
        if current>best[0]: best=(current,x.copy(),dc)
        for _step in range(int(steps)):
            y=x.copy(); qy={j:q[j].copy() for j in q}
            if optimize_q and rng.random()<.35:
                j=int(rng.integers(0,int(m)))
                logits=np.log(np.maximum(qy[j],1e-12))
                u=int(rng.integers(0,int(alphabet)))
                logits[u]+=float(rng.normal(0,.8))
                logits-=np.max(logits); qy[j]=np.exp(logits); qy[j]/=qy[j].sum()
            else:
                idx=tuple(int(rng.integers(0,s)) for s in shape); y[idx]=np.clip(y[idx]+rng.choice([-2.,-1.,1.,2.]),-float(value_clip),float(value_clip))
            score,dy=_score(y,m,k,qy); accept=score>=current or rng.random()<math.exp((score-current)/max(temp,1e-8))
            if accept: x,q,current,dc=y,qy,score,dy
            if score>best[0]: best=(score,y.copy(),dy)
            if score>0.5+1e-12: killed=True; break
            temp*=.985
        if killed: break
    ratio,values,d=best
    witness=None if values is None else {'values':values.tolist(),'m':int(m),'k':int(k),'ratio_regret_over_approx_rhs':float(ratio),'delta_square':float(d['delta_square']),'decision_regret':float(d['true_decision_regret']),'approximation_rhs':float(d['worst_case_rhs']),'candidate_half_rhs':float(d['decision_candidate_half_rhs']),'candidate_violation':float(d['decision_candidate_half_violation']),'chosen_topc':d['chosen_topc'],'exact_optimal_sets':d['exact_optimal_sets'],'reference_q':d['reference_q']}
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'DIRECTED_FALSIFICATION_NOT_PROOF','candidate_threshold':0.5,'candidate_killed':bool(killed),'restarts_requested':int(restarts),'steps_per_restart':int(steps),'seed':int(seed),'m':int(m),'alphabet':int(alphabet),'k':int(k),'q_mode':q_mode,'optimize_q':bool(optimize_q),'best_witness':witness}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--restarts',type=int,default=2000); p.add_argument('--steps',type=int,default=200); p.add_argument('--m',type=int,default=3); p.add_argument('--alphabet',type=int,default=2); p.add_argument('--k',type=int,default=1); p.add_argument('--seed',type=int,default=100); p.add_argument('--value-clip',type=float,default=8); p.add_argument('--q-mode',choices=['uniform','random','skewed','boundary'],default='uniform'); p.add_argument('--optimize-q',action='store_true'); p.add_argument('--out',default='research/high_value_extensions/d6/counterexample_optimizer.json'); a=p.parse_args(argv)
    payload=run(a.restarts,a.steps,a.m,a.alphabet,a.k,a.seed,a.value_clip,q_mode=a.q_mode,optimize_q=a.optimize_q); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 2 if payload['candidate_killed'] else 0
if __name__=='__main__': raise SystemExit(main())
