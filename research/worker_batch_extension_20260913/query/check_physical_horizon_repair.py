"""Audit scalar repair with the existing physical horizon<=2 query library.

Population is every successful stored snapshot-candidate, including constant
cases. World includes physical AND RNG state. Identifiers are never decoder
features. This reuses stored interventions, not newly generated trajectories.
"""
from pathlib import Path
from fractions import Fraction as F
import importlib.util,json,hashlib,collections
repo=Path('/Users/phanan/cig-amf-main')
source=repo/'scripts/QUERY_restricted_decoder_exact.py'
spec=importlib.util.spec_from_file_location('old_query_decoder',source);lib=importlib.util.module_from_spec(spec);spec.loader.exec_module(lib)
panel=repo/'research/high_risk_20260910/QUERY_natural_panel_v2.json'
payload=json.loads(panel.read_text());units=lib.build_units(payload)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def uid(u):return dict(seed=u['seed'],t=u['t'],candidate=u['cand'],physical_key=u['physical_key'],rng_key=u['rng_key'],c1=u['c1'],c2=u['c2'],target=str(u['ateT']))
def analyze(extras):
    key=lambda u:lib.summary_key(u,extras)
    groups=lib.fibres(units,key);radius=F(0);witness=None;errors=[]
    for members in groups.values():
        lo=min(members,key=lambda u:u['ateT']);hi=max(members,key=lambda u:u['ateT'])
        rad=(hi['ateT']-lo['ateT'])/2;mid=(hi['ateT']+lo['ateT'])/2
        assert all(abs(u['ateT']-mid)<=rad for u in members)
        errors.extend(abs(u['ateT']-mid) for u in members)
        if rad>radius:radius=rad;witness=dict(low=uid(lo),high=uid(hi),distinct_physical_states=lo['physical_key']!=hi['physical_key'])
    assert max(errors)==radius
    nondeg=[u for u in units if any(u['c1'])]
    ng=lib.fibres(nondeg,key)
    nondeg_radius=max(((max(u['ateT'] for u in g)-min(u['ateT'] for u in g))/2 for g in ng.values()),default=F(0))
    ngworst=max(ng.values(),key=lambda g:max(u['ateT'] for u in g)-min(u['ateT'] for u in g)) if ng else []
    nlo=min(ngworst,key=lambda u:u['ateT']) if ngworst else None;nhi=max(ngworst,key=lambda u:u['ateT']) if ngworst else None
    nwitness=dict(low=uid(nlo),high=uid(nhi),distinct_physical_states=nlo['physical_key']!=nhi['physical_key']) if ngworst else None
    train_seeds=set(sorted(payload['seeds'])[:15]);train=[u for u in units if u['seed'] in train_seeds];test=[u for u in units if u['seed'] not in train_seeds]
    holdout=lib.holdout_eval(train,test,key,lambda u:u['ateT'])
    return dict(features=list(extras),incremental_environment_steps=10 if extras else 0,fibres=len(groups),singleton_fibres=sum(len(g)==1 for g in groups.values()),
                repeated_fibre_units=sum(len(g) for g in groups.values() if len(g)>1),exact_minimax_radius=str(radius),worst_pair=witness,holdout=holdout,nondegenerate_c1_units=len(nondeg),nondegenerate_c1_radius=str(nondeg_radius),nondegenerate_worst_pair=nwitness)
rows=[analyze(()),analyze(('response_h2',))]
# Every subset of the permitted catalog is exhausted. No model/privileged keys.
repair=[]
for eps in map(F,['0','1/10','1/4','1/2','1']):
    legal=[r for r in rows if F(r['exact_minimax_radius'])<=eps]
    best=min(legal,key=lambda r:r['incremental_environment_steps']) if legal else None
    repair.append(dict(eps=str(eps),feasible=best is not None,minimum_incremental_environment_steps=best['incremental_environment_steps'] if best else None,features=best['features'] if best else None))
counts=payload['counts'];assert len(units)==counts['panel_built']*len(payload['candidates'])
assert counts['reachable_snapshots']==counts['panel_built']+counts.get('filtered_panel_error',0)
# A fabricated unique ID must trigger singleton leakage diagnostics.
leaked=lib.fibres(units,lambda u:(u['seed'],u['t'],u['cand']))
assert len(leaked)==len(units) and all(len(v)==1 for v in leaked.values())
out=dict(scope='Exact empirical finite-population scalar ATE horizon-6 repair; only extra feature is the actual stored horizon-2 response, costing five two-step rollouts; no distributional generalization claim',
         panel_path=str(panel),panel_sha256=sha(panel),helper_source_sha256=sha(source),source_sha256=sha(Path(__file__)),
         population_units=len(units),constant_horizon6_profiles=sum(len(set(u['RT']))==1 for u in units),collection_counts=counts,feature_results=rows,repair=repair,
         unique_identifier_negative_control=dict(singletons=len(leaked),rejected_as_physical_feature=True))
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['feature_results','collection_counts']},indent=2))
print([(r['features'],r['exact_minimax_radius'],r['fibres'],r['holdout']) for r in rows])
