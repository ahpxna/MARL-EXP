import json, math, statistics
from pathlib import Path
R=Path('/Users/phanan/cig-amf-main/research')
O=Path('/Users/phanan/Documents/Codex/2026-09-07/users-phanan-downloads-cig-amf-evolution/outputs')
load=lambda p:json.loads(p.read_text())
fpath=R/'confirm_20260907_030500/functional_v2.json';f=load(fpath)
summary={'inputs':[str(fpath)],'functional':{},'master':[],'structural':[]}
for v,rows in f['runs_by_variant'].items():
 n=len(rows);emit=sum(r['certificate_emitted'] for r in rows)
 assert n==60 and math.isclose(emit/n,f['by_variant'][v]['certificate_fraction'])
 counts=[sum(r['counts'],[]) for r in rows]
 if v=='uniform': assert all(max(c)-min(c)<=1 for c in counts)
 summary['functional'][v]={'n':n,'emitted':emit,'false_safe':sum(r['false_safe'] is True for r in rows),'median_censored':statistics.median(r['censored_N_certificate'] for r in rows),'min_cell_count':min(min(c) for c in counts),'runs_with_cell_count_2':sum(min(c)==2 for c in counts),'mean_interval_width':f['by_variant'][v]['mean_final_capacity_interval_width']}
summary['functional_pilot_shrink_identical']=all({k:v for k,v in a.items() if k!='variant'}=={k:v for k,v in b.items() if k!='variant'} for a,b in zip(f['runs_by_variant']['C_pilot'],f['runs_by_variant']['C_shrink']))
for seed in [8201,8202,8203]:
 mp=R/f'confirm_20260907_030535/master_s{seed}.json';m=load(mp);summary['inputs'].append(str(mp))
 rows=[r for r in m['rows'] if r['tolerance']==.1]
 assert len(rows)==450 and all(r['regret'] is not None for r in rows)
 for r in rows:
  assert r['certificate_box'] <= r['certificate_operational']+1e-10
  for key in ['box','operational']:
   cert=r['certificate_'+key]
   assert r['fallback_'+key]==(cert>.1)
   assert r['regret']<=cert+1e-10
  assert math.isclose(r['regret'],r['candidate_loss']-r['exact_optimum'],abs_tol=1e-10)
 box=sum(not r['fallback_box'] for r in rows);op=sum(not r['fallback_operational'] for r in rows)
 summary['master'].append({'seed':seed,'n':len(rows),'box':box,'op':op,'gain_pp':100*(box-op)/len(rows),'all_bounds_cover':True,'false_safe':sum(r['false_safe_box'] or r['false_safe_operational'] for r in rows)})
 sp=R/f'confirm_20260907_030529/structural_s{seed}.json';s=load(sp);summary['inputs'].append(str(sp))
 row={'seed':seed,'by_K':{}}
 for k,z in s['by_K'].items():
  d={}
  for meth in ['exact','greedy']:
   raw=z['raw_'+meth];assert len(raw)==12
   vals=[]
   for r in raw:
    budgets=r['metrics']['per_budget'];computed=[p['achieved']-p['optimum'] for p in budgets]
    assert all(math.isclose(a,p['regret'],abs_tol=1e-10) for a,p in zip(computed,budgets))
    assert math.isclose(max(computed),r['metrics']['worst_budget_regret'],abs_tol=1e-10)
    vals.append(max(computed))
   assert math.isclose(statistics.mean(vals),z[meth]['worst_budget_regret']['mean'],abs_tol=1e-10)
   d[meth]={'zero_worlds':sum(abs(x)<1e-10 for x in vals),'mean_worst_regret':statistics.mean(vals)}
  dr=z['deep']['rows'];d['deep_mean_worst_regret']=statistics.mean(r['worst_budget_regret'] for r in dr)
  assert math.isclose(d['deep_mean_worst_regret'],z['deep']['worst_budget_regret_mean'],abs_tol=1e-10)
  row['by_K'][k]=d
 summary['structural'].append(row)
qp=R/'confirm_20260907_030529/query_v4.json';q=load(qp);summary['inputs'].append(str(qp))
qs=[x for s in q['states'] for x in s['queries'].values()]
assert len(qs)==48 and all(x['diagnostics']['utility_oscillation']==0 for x in qs)
summary['query']={'status':q['scientific_transfer_status'],'executable_states':q['executable_states'],'unique_states':len(set(s['state_hash'] for s in q['states'])),'constant_targets':len(qs),'evaluable_cells':q['scientifically_evaluable_matrix_cells'],'full':q['aggregate_denominators_full_information'],'matched':q['aggregate_denominators_matched_budget'],'missing_methods':list(q['blocked_methods'])}
(O/'CONFIRM_RESULTS_20260907.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2))
print(json.dumps({k:v for k,v in summary.items() if k not in ['inputs','structural']},indent=1))
print('All raw-summary consistency checks passed; no simulations or training executed.')
