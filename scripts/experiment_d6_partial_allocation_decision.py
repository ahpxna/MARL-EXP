#!/usr/bin/env python3
"""Budget-charged partial-label allocation decisions on actual D6 queries.

Two-point local margin subproblem: q, mu_U and epsilon are supplied, but neither
A nor the side is known to the algorithm. All data-using methods receive the
same scalar pilot and independent three-query phase blocks. The terminal
recommendation is an allocation, not the allocation of the pilot observations.
No sequential stopping or minimax-optimality claim is made.
"""
import argparse, itertools, json
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.special import ndtr
from experiment_d6_blind_allocation import arrays
from experiment_d6_adaptive_geometry import Model
from experiment_d6_phase_boundary_cost import information, oracle
from verify_d6_information_limit_bridge import family_world


def robust_orbits(q,C,D,mus,gammas,tol=2e-8):
    blocks=[arrays(q,C,D,mu) for mu in mus]
    groups=blocks[0][3]; Q=len(groups)
    cuts=[]; targets=[]
    for (aa,bb,cc,_),mu,gamma in zip(blocks,mus,gammas):
        for nu in [0.,mu,1.]:
            cuts.extend((aa*nu*nu+bb*nu+cc)/2)
            targets.extend([gamma]*len(aa))
    for it in range(100):
        mat=np.asarray(cuts)
        lp=linprog([0.]*Q+[1.],A_ub=np.column_stack([-mat,-np.ones(len(mat))]),
            b_ub=-np.asarray(targets),A_eq=np.array([[1.]*Q+[0.]]),b_eq=[1.],
            bounds=[(0,None)]*Q+[(0,None)],method='highs',options={'primal_feasibility_tolerance':1e-9,'dual_feasibility_tolerance':1e-9})
        if not lp.success: raise RuntimeError(lp.message)
        w=lp.x[:-1]; worst=0.
        for (aa,bb,cc,_),gamma in zip(blocks,gammas):
            a,b,c=aa@w,bb@w,cc@w
            nu=np.clip(np.divide(-b,2*a,out=np.zeros_like(b),where=a>0),0,1)
            vals=(a*nu*nu+b*nu+c)/2
            worst=max(worst,float(gamma-vals.min()))
            bad=np.flatnonzero(gamma-vals>lp.x[-1]+tol)
            cuts.extend((aa[bad]*nu[bad,None]**2+bb[bad]*nu[bad,None]+cc[bad])/2)
            targets.extend([gamma]*len(bad))
        if worst-lp.x[-1]<=tol: break
    else: raise RuntimeError(('LP separation failed',q,C,D,worst,float(lp.x[-1])))
    return groups,w,dict(lower=float(lp.x[-1]),upper=worst,iterations=it+1)


def lift(groups,weights,Acore,Bcore,ground,j):
    unresolved=[i for i in ground if i not in Acore and i not in Bcore]
    cells=[Acore,Bcore,unresolved,[j]]; chosen={}
    for orbit,weight in zip(groups,weights):
        if weight<1e-13: continue
        if orbit[0]=='s':
            queries=[('scalar',i,False) for i in cells[orbit[1]]]
        else:
            _,s,t,u,h=orbit
            queries=[('joint',sum(1<<i for i in (*a,*b,*c)),bool(h))
                for a in itertools.combinations(Acore,s)
                for b in itertools.combinations(Bcore,t)
                for c in itertools.combinations(unresolved,u)]
        assert queries
        for e in queries: chosen[e]=chosen.get(e,0.)+float(weight)/len(queries)
    es=list(chosen); ws=np.array([chosen[e] for e in es]); ws/=ws.sum()
    return es,ws


def actual_information(model,truth,mu,design):
    es,ws=design; K=len(model.labels)
    aa=np.zeros(K); bb=np.zeros(K); cc=np.zeros(K)
    for e,w in zip(es,ws):
        off,slope=model.features(e)
        d=off-off[truth]-mu*slope[truth]
        aa+=w*slope*slope; bb+=2*w*d*slope; cc+=w*d*d
    nu=np.clip(np.divide(-bb,2*aa,out=np.zeros_like(bb),where=aa>0),0,1)
    vals=(aa*nu*nu+bb*nu+cc)/2; vals[truth]=np.inf
    return float(vals.min())


def exact_block_check(q):
    m=2*q+2; j=q+1; ids=[i for i in range(m) if i!=j]
    gs=[ids[:q],ids[q:2*q-1],ids[2*q-1:]]
    masks=[sum(1<<i for i in g) for g in gs]; cases=0
    for lab in itertools.combinations(ids,q+1):
        for mu in [Fraction(0),Fraction(2,5),Fraction(7,10),Fraction(1)]:
            world=family_world(m,mu,sum(1<<i for i in lab))
            assert sum(world[g] for g in masks)==3*mu.denominator+q*(mu.denominator-mu.numerator)
            cases+=1
    return dict(q=q,world_margin_cases=cases,query_evaluations=cases*3,max_exact_error=0)


def run(q,repeats,seeds,alpha):
    model=Model(q); p=model.p; j=q+1
    ground=[i for i in range(model.m) if i!=j]; n=len(ground)
    eps=.4*(p['mu_H']-p['mu_U']); mus=[p['mu_U']-eps,p['mu_U']+eps]
    gammas=[information(q,mu,oracle(q,mu,p))[0] for mu in mus]
    cache={}; checks=[]
    def recommend(ac,bc):
        key=(len(ac),len(bc))
        if key not in cache:
            cache[key]=robust_orbits(q,*key,mus,gammas)
        groups,w,cert=cache[key]
        return lift(groups,w,ac,bc,ground,j)
    blind=recommend([],[])
    # Direct evaluation validates the orbit LP against the literal query library.
    groups,w,cert=cache[(0,0)]
    direct=max(g-actual_information(model,0,mu,blind) for g,mu in zip(gammas,mus))
    assert abs(direct-cert['upper'])<1e-8
    checks.append(dict(kind='blind_orbit_vs_all_label_query_evaluation',error=abs(direct-cert['upper'])))
    rows=[]
    for r in repeats:
        blocks=max(1,n*r//3); N=n*r+3*blocks
        radius=np.sqrt(2*np.log(2*n/alpha)/r)
        for side,mu in enumerate(mus):
            rng=np.random.default_rng(np.random.SeedSequence([20260910,q,r,side]))
            for seed in range(seeds):
                truth=int(rng.integers(len(model.labels))); A=int(model.labels[truth])
                scalar_means=np.array([1. if A&(1<<i) else 1-mu for i in ground])
                obs=scalar_means+rng.normal(size=n)/np.sqrt(r)
                order=np.argsort(-obs); plugA=sum(1<<ground[i] for i in order[:q+1])
                plug_ix=int(np.flatnonzero(model.labels==plugA)[0])
                # Sum of actual block observations; group counts from the literal A.
                gs=[ground[:q],ground[q:2*q-1],ground[2*q-1:]]
                totals=0.
                for group in gs:
                    Bcount=sum(not bool(A&(1<<i)) for i in group)
                    mean=1+(1-mu)*Bcount
                    totals+=blocks*mean+np.sqrt(blocks)*rng.normal()
                mhat=1-(totals/blocks-3)/q
                estimated_side=int(mhat>=p['mu_U'])
                ac=[i for i,v in zip(ground,obs) if v-radius>1-mus[0]]
                bc=[i for i,v in zip(ground,obs) if v+radius<1.]
                valid=len(ac)<=q+1 and len(bc)<=q and not(set(ac)&set(bc))
                if not valid: ac=[];bc=[]
                # Cardinality closure uses only the known label sizes.
                if len(ac)==q+1: bc=[i for i in ground if i not in ac]
                if len(bc)==q: ac=[i for i in ground if i not in bc]
                full=len(ac)==q+1
                core_correct=all(A&(1<<i) for i in ac) and all(not(A&(1<<i)) for i in bc)
                plugin=model.design(plug_ix,mus[estimated_side])
                if full:
                    ix=int(np.flatnonzero(model.labels==sum(1<<i for i in ac))[0])
                    partial=model.design(ix,mus[estimated_side])
                else:
                    partial=recommend(ac,bc)
                designs={'blind':blind,'partial':partial,'recover_first':partial if full else blind,'full_plugin':plugin}
                losses={k:max(0.,gammas[side]-actual_information(model,truth,mu,d)) for k,d in designs.items()}
                rows.append(dict(q=q,repeats=r,N=N,side=2*side-1,seed=seed,epsilon=eps,
                    scalar_samples=n*r,phase_samples=3*blocks,phase_wrong=estimated_side!=side,
                    phase_error_exact=float(ndtr(-q*eps*np.sqrt(blocks/3))),
                    known_A=len(ac),known_B=len(bc),fully_resolved=full,core_correct=bool(core_correct),
                    plugin_label_correct=plug_ix==truth,gamma=gammas[side],regret=losses))
        print(f'q={q}, r={r}, N={N}: {2*seeds} paired trials',flush=True)
    summaries=[]
    for r in repeats:
        sub=[x for x in rows if x['repeats']==r]
        losses={k:np.array([x['regret'][k] for x in sub]) for k in sub[0]['regret']}
        delta=losses['partial']-losses['recover_first']
        summaries.append(dict(q=q,repeats=r,N=sub[0]['N'],trials=len(sub),
            mean_regret={k:float(v.mean()) for k,v in losses.items()},
            paired_partial_minus_recover_mean=float(delta.mean()),
            paired_partial_minus_recover_se=float(delta.std(ddof=1)/np.sqrt(len(delta))),
            unresolved_fraction=float(np.mean([not x['fully_resolved'] for x in sub])),
            mean_resolved_coordinates=float(np.mean([x['known_A']+x['known_B'] for x in sub])),
            bad_core_count=sum(not x['core_correct'] for x in sub),
            plugin_label_accuracy=float(np.mean([x['plugin_label_correct'] for x in sub])),
            phase_error_observed=float(np.mean([x['phase_wrong'] for x in sub])),
            phase_error_exact=sub[0]['phase_error_exact']))
    # Check every cache size on canonical cores against the direct evaluator.
    for (C,D),(groups,w,cert) in cache.items():
        ac=ground[:C];bc=ground[q+1:q+1+D]
        design=lift(groups,w,ac,bc,ground,j)
        direct=max(g-actual_information(model,0,mu,design) for g,mu in zip(gammas,mus))
        assert abs(direct-cert['upper'])<1e-7,(C,D,direct,cert)
        checks.append(dict(kind='partial_orbit_vs_actual',C=C,D=D,error=abs(direct-cert['upper'])))
    return rows,summaries,checks


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--q',nargs='+',type=int,default=[3,4])
    ap.add_argument('--repeats',nargs='+',type=int,default=[1,4,12,32,96])
    ap.add_argument('--seeds',type=int,default=100)
    ap.add_argument('--out',type=Path,default=Path('research/d6_phase_boundary_20260908/partial_allocation_decision.json'))
    args=ap.parse_args(); rows=[]; summaries=[]; checks=[]
    for q in args.q:
        checks.append(exact_block_check(q))
        r,s,c=run(q,args.repeats,args.seeds,.1);rows+=r;summaries+=s;checks+=c
    deps=['experiment_d6_blind_allocation.py','experiment_d6_adaptive_geometry.py','experiment_d6_phase_boundary_cost.py','experiment_d6_unresolved_label_family.py','verify_d6_information_limit_bridge.py']
    obj=dict(evidence_class='ACTUAL_QUERY_PAIRED_PARTIAL_LABEL_ALLOCATION',configuration=vars(args)|{'out':str(args.out)},
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        dependencies={f:sha256(Path(__file__).with_name(f).read_bytes()).hexdigest() for f in deps},
        summaries=summaries,checks=checks,rows=rows,
        scope=['Supplied two-point local margin family; no hidden label or true side supplied to recommendation.',
        'Equal actual-query budget for all data-using policies; blind comparator uses no data.',
        'Confidence cores are inferred from noisy scalar data; wrong cores remain in risk evaluation.',
        'Regret is terminal recommended allocation loss, not cumulative loss or empirical pilot allocation.',
        'Every alternative label and continuous nuisance in [0,1] evaluated for realized recommendation.',
        'Small-q Monte Carlo and floating-point LP certificates; no adaptive minimax or growing-q theorem.'])
    args.out.parent.mkdir(parents=True,exist_ok=True); args.out.write_text(json.dumps(obj,indent=2)+'\n')
    print(json.dumps(summaries,indent=2),flush=True)
if __name__=='__main__':main()
