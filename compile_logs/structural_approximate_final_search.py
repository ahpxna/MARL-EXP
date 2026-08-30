#!/usr/bin/env python3
"""One final focused approximate-Structural round.

Tests continuous adjacent nesting defects against exact best all-budget chain
regret.  It intentionally does not reopen exact-iff candidate search.
"""
from __future__ import annotations
import itertools, json, random
from structural_candidate_search import (
    objective_values, optimal_levels, valid_projection, popcount)


def best_chain_regret(m, obj):
    best = {k:min(obj[s] for s in range(1<<m) if popcount(s)==k)
            for k in range(m+1)}
    dp = {0: 0}
    parent = {}
    for k in range(1,m+1):
        ndp={}
        for s in range(1<<m):
            if popcount(s)!=k: continue
            regret=obj[s]-best[k]
            choices=[(max(dp[p],regret),p) for p in dp if p & s == p]
            ndp[s],parent[(k,s)]=min(choices)
        dp=ndp
    return dp[(1<<m)-1], best


def defects(m,obj,opt,best):
    # Pairwise adjacent optimal compatibility relaxed continuously by the
    # next-level objective gap.
    weak=[]; allopt=[]
    for k in range(m):
        ext=lambda s:[t for t in range(1<<m)
                      if popcount(t)==k+1 and s&t==s]
        weak.append(min(obj[t]-best[k+1] for s in opt[k] for t in ext(s)))
        allopt.append(max(min(obj[t]-best[k+1] for t in ext(s)) for s in opt[k]))
    # Worst one-swap local-minimum regret: a direct algorithmic trap metric.
    trap=0; traps=0
    for k in range(1,m):
        fam=[s for s in range(1<<m) if popcount(s)==k]
        for s in fam:
            neigh=[(s^(1<<i))|(1<<j) for i in range(m) for j in range(m)
                   if s&(1<<i) and not s&(1<<j)]
            if all(obj[s] <= obj[t] for t in neigh):
                traps += 1
                trap=max(trap,obj[s]-best[k])
    return max(weak,default=0),max(allopt,default=0),trap,traps


def world_payload(m,support,slopes,obj,target,weak,allopt,trap,corpus):
    return {"m":m,"support":[list(a) for a in support],"slopes":list(slopes),
            "objective_twice_radius":{str(s):obj[s] for s in obj},
            "best_chain_regret_twice_radius":target,
            "weak_adjacent_defect":weak,"all_optima_extension_defect":allopt,
            "local_trap_depth":trap,"corpus":corpus}


def main():
    stats={"worlds":0,"zero_weak_positive_target":0,
           "zero_allopt_positive_target":0,"target_positive":0,
           "local_trap_positive":0,"target_and_trap_positive":0,
           "trap_false_positive":0,"trap_false_negative":0,
           "target_gt_allopt":0,"target_gt_m_times_allopt":0,
           "corpora":{},"counterexamples":{}}
    def add(m,support,slopes,corpus):
        obj=objective_values(m,support,slopes); opt=optimal_levels(m,obj)
        target,best=best_chain_regret(m,obj)
        weak,allopt,trap,traps=defects(m,obj,opt,best)
        stats["worlds"]+=1; stats["corpora"][corpus]=stats["corpora"].get(corpus,0)+1
        stats["target_positive"]+=target>0;stats["local_trap_positive"]+=trap>0
        stats["target_and_trap_positive"]+=(target>0 and trap>0)
        stats["trap_false_positive"]+=(target==0 and trap>0)
        stats["trap_false_negative"]+=(target>0 and trap==0)
        stats["target_gt_allopt"]+=target>allopt
        stats["target_gt_m_times_allopt"]+=target>m*allopt
        if weak==0 and target>0:
            stats["zero_weak_positive_target"]+=1
            stats["counterexamples"].setdefault("weak_adjacent_zero_not_sufficient",
                world_payload(m,support,slopes,obj,target,weak,allopt,trap,corpus))
        if allopt==0 and target>0:
            stats["zero_allopt_positive_target"]+=1
            stats["counterexamples"].setdefault("all_optima_extension_zero_not_sufficient",
                world_payload(m,support,slopes,obj,target,weak,allopt,trap,corpus))

    # Existing 12,352 m=3 corpus.
    m=3; full=tuple(itertools.product((0,1),repeat=m))
    for mask in range(1,1<<len(full)):
        support=tuple(a for bit,a in enumerate(full) if mask&(1<<bit))
        if not valid_projection(support,m):continue
        for slopes in itertools.product((-2,-1,1,2),repeat=m):
            add(m,support,slopes,"existing_exhaustive_m3")
    # Existing exhaustive m4 slice.
    m=4; full=tuple(itertools.product((0,1),repeat=m));slopes=(-3,-1,2,4)
    for mask in range(1,1<<len(full)):
        support=tuple(a for bit,a in enumerate(full) if mask&(1<<bit))
        if valid_projection(support,m):add(m,support,slopes,"existing_exhaustive_m4")
    # Existing-size random plus fresh adversarial sparse/cancellation-biased worlds.
    rng=random.Random(8871)
    for m in (4,5,6):
        full=tuple(itertools.product((0,1),repeat=m))
        for phase,count in (("existing_random",5000),("fresh_adversarial",5000)):
            done=0
            while done<count:
                if phase=="fresh_adversarial":
                    p=rng.choice((0.08,0.12,0.18,0.25,0.75))
                    slopes=tuple(rng.choice((-5,-4,-1,1,4,5)) for _ in range(m))
                else:
                    p=rng.uniform(.12,.9)
                    slopes=tuple(rng.choice((-4,-3,-2,-1,1,2,3,4)) for _ in range(m))
                support=tuple(a for a in full if rng.random()<p)
                if not support or not valid_projection(support,m):continue
                add(m,support,slopes,f"{phase}_m{m}");done+=1
    # frozen actual witnesses
    for m,support,slopes,name in [
      (3,((0,0,0),(0,1,1),(1,0,0)),(-2,1,-3),"W1"),
      (2,((0,0),(1,1)),(-1,1),"W2"),
      (3,((0,0,1),(0,1,0),(1,0,0)),(-3,-3,1),"W3")]:
        add(m,support,slopes,name)
    with open("compile_logs/structural_approximate_final_results.json","w") as f:
        json.dump(stats,f,indent=2,sort_keys=True)
    print(json.dumps({k:v for k,v in stats.items() if k!="counterexamples"},indent=2))

if __name__=="__main__":main()
