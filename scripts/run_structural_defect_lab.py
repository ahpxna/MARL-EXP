"""Final approximate-Structural screen after exact-iff candidates were closed."""
from __future__ import annotations
import sys,argparse,json,itertools,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from scipy.stats import spearmanr
from research_chains.certificates import deficit_terms
from research_chains.experimental_extensions import best_nested_prefix_regret, all_optimal_extension_defect
from research_chains.finite_world import FiniteResponseWorld
from research_chains.provenance import atomic_json
from research_chains.support import SupportModel

PROTOCOL_VERSION='structural_approximate_defect_screen_v1'
CLOSED_EXACT_SEARCH_WORLDS=91130
CLOSED_CANDIDATES=('adjacent_pair','submodular','supermodular','equal_cardinality_M_convex','monotonicity','tested_deficit_iff_variants')

def _world(rng,m):
    sizes=(2,)*m; full=list(np.ndindex(*sizes)); p=float(rng.uniform(.15,.95)); omega=[a for a in full if rng.random()<p]
    for j in range(m):
        for x in range(2):
            if not any(a[j]==x for a in omega): omega.append(next(a for a in full if a[j]==x))
    primitives=tuple(np.asarray([0.,float(rng.choice([-3,-2,-1,1,2,3]))]) for _ in range(m))
    return FiniteResponseWorld(SupportModel(sizes,tuple(sorted(set(omega))),key='structural'),primitives)

def run(instances=3000,seed=0):
    rng=np.random.default_rng(seed); rows=[]
    for idx in range(int(instances)):
        m=3+int(rng.integers(0,4)); world=_world(rng,m); t0=time.perf_counter(); d=best_nested_prefix_regret(world); ao=all_optimal_extension_defect(world,d); d['runtime_seconds']=float(time.perf_counter()-t0); d.update({'all_optimal_extension_defect':ao['all_optimal_extension_defect'],'m_times_all_optimal_extension_defect':ao['m_times_defect'],'all_optimal_candidate_violation':ao['candidate_violation']})
        pair=[]
        for size in (2,):
            if size<=m:
                pair += [deficit_terms(world,T)['d']/2.0 for T in itertools.combinations(range(m),size)]
        span_sum=float(np.sum(world.component_spans()))/2.0
        d.update({'m':m,'max_pair_defect_half':float(max(pair,default=0.0)),'mean_pair_defect_half':float(np.mean(pair)) if pair else 0.0,'missing_scaled_span':float(d['support_missing_fraction']*span_sum)})
        rows.append(d)
    target=np.asarray([r['best_nested_max_regret'] for r in rows]); candidates=('max_zeta_half','E_half','all_optimal_extension_defect','m_times_all_optimal_extension_defect','max_pair_defect_half','mean_pair_defect_half','missing_scaled_span','support_missing_fraction')
    master_baseline=np.asarray([min(r['max_zeta_half'],r['E_half']) for r in rows],float)
    screen={}
    for name in candidates:
        x=np.asarray([r[name] for r in rows],float); violations=target-x
        rho=0.0 if x.size<2 or np.allclose(x,x[0]) or np.allclose(target,target[0]) else spearmanr(x,target).statistic
        screen[name]={
            'spearman_with_best_nested_regret':0.0 if not np.isfinite(rho) else float(rho),
            'max_candidate_bound_violation':float(np.max(violations)),
            'safe_fraction_as_direct_bound':float(np.mean(violations<=1e-10)),
            'nonzero_fraction':float(np.mean(x>1e-12)),
            'tighter_than_existing_MASTER_fraction':float(np.mean(x < master_baseline-1e-10)),
            'mean_width_ratio_to_MASTER':float(np.mean(x/np.maximum(master_baseline,1e-12))),
        }
    # SR0 executable sanity: best_nested_prefix_regret enumerates all rankings;
    # zero regret therefore witnesses a cardinality-optimal nested chain, while a
    # positive minimum excludes one.  Recompute the predicate from per-budget
    # regrets to guard against implementation drift.
    sr0_viol=0
    for r in rows:
        via_best=bool(r['best_nested_max_regret']<=1e-10)
        via_path=bool(r['best_nested_per_budget'] is not None and max(r['best_nested_per_budget'],default=0.0)<=1e-10)
        sr0_viol+=int(via_best!=via_path)
    zeta_safe=screen['max_zeta_half']['max_candidate_bound_violation']<=1e-8
    allopt_safe=float(max(r['all_optimal_candidate_violation'] for r in rows))<=1e-8
    allopt_nontrivial=float(np.mean([r['all_optimal_extension_defect']>1e-12 for r in rows]))
    allopt_tighter=float(np.mean([r['m_times_all_optimal_extension_defect'] < min(r['max_zeta_half'],r['E_half'])-1e-10 for r in rows]))
    if allopt_safe and allopt_nontrivial>0 and allopt_tighter>=0.10:
        decision='CONTINUE_APPROXIMATE_STRUCTURAL'; reason='open all-optimal-extension candidate survived and is tighter than existing MASTER on >=10% of fresh worlds'
    elif allopt_safe:
        decision='MERGE_INTO_MASTER_KEEP_OPEN_CANDIDATE'; reason='all-optimal-extension candidate survived but did not add >=10% practical tightening in this screen; keep theorem candidate open but do not justify standalone paper'
    elif zeta_safe:
        decision='MERGE_INTO_MASTER_STOP_STANDALONE'; reason='open all-optimal-extension candidate was falsified; existing MASTER bounds remain safe'
    else: decision='OPEN'; reason='even expected MASTER zeta diagnostic failed; inspect implementation'
    worst=sorted(rows,key=lambda r:r['best_nested_max_regret'],reverse=True)[:20]
    runtime_by_m={}
    for m in sorted({r['m'] for r in rows}):
        vals=[r['runtime_seconds'] for r in rows if r['m']==m]; runtime_by_m[str(m)]={'n':len(vals),'median_seconds':float(np.median(vals)),'p90_seconds':float(np.quantile(vals,.9)),'max_seconds':float(max(vals))}
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'closed_exact_search':{'worlds':106130,'original_exact_iff_worlds':CLOSED_EXACT_SEARCH_WORLDS,'closed_candidates':CLOSED_CANDIDATES,'retry_exact_iff':False},'sr0_nested_chain_sanity':{'violation_count':int(sr0_viol),'checked_worlds':len(rows)},'open_candidate':{'name':'best_nested_regret <= m * all_optimal_extension_defect','safe':bool(allopt_safe),'worst_violation':float(max(r['all_optimal_candidate_violation'] for r in rows)),'nonzero_defect_fraction':allopt_nontrivial,'tighter_than_MASTER_fraction':allopt_tighter},'candidate_screen':screen,'kill_gate_decision':decision,'kill_gate_reason':reason,'runtime_complexity_by_m':runtime_by_m,'largest_best_nested_regret_examples':worst}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=3000); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/high_value_extensions/structural/summary.json'); a=p.parse_args(argv); payload=run(a.instances,a.seed); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
