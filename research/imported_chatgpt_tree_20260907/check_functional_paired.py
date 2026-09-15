import importlib.util,sys,json
from pathlib import Path
sys.path.insert(0,'/Users/phanan/cig-amf-main')
from scripts import run_functional_variance_stopping_lab as old
spec=importlib.util.spec_from_file_location('functional_v3',Path('work/code/run_functional_variance_stopping_lab.py'))
new=importlib.util.module_from_spec(spec);spec.loader.exec_module(new)
results={}
for label,mod in [('v2',old),('v3',new)]:
 p=mod.run(instances=2,seeds=(8301,),relations=5,actions=6,topk=2,max_n=2048,batch=16)
 results[label]=p
summary={}
for label,p in results.items():
 summary[label]={v:{'min_counts':[min(sum(r['counts'],[])) for r in rr],
                     'emitted':sum(r['certificate_emitted'] for r in rr),
                     'mean_width':p['by_variant'][v]['mean_final_capacity_interval_width']}
                 for v,rr in p['runs_by_variant'].items()}
 rr=p['runs_by_variant'];summary[label]['pilot_shrink_counts_identical']=sum(a['counts']==b['counts'] for a,b in zip(rr['C_pilot'],rr['C_shrink']))
Path('work/functional_paired_smoke.json').write_text(json.dumps({'summary':summary,'runs':results},indent=2))
assert summary['v2']['pilot_shrink_counts_identical']==2
assert summary['v3']['pilot_shrink_counts_identical']==0
assert min(summary['v3']['C_anytime']['min_counts'])>2
print(json.dumps(summary,indent=2))
