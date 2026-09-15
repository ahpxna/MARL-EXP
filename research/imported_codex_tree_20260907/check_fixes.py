import importlib.util,sys,json
from pathlib import Path
import numpy as np
ROOT=Path('/Users/phanan/cig-amf-main');sys.path.insert(0,str(ROOT))
def load(name,file):
 spec=importlib.util.spec_from_file_location(name,Path(__file__).parent/file)
 m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
lab=load('fixed_variance','run_functional_variance_stopping_lab.py')
cap=load('fixed_capability','capability_audit.py')
shape=(5,6);z=np.zeros(shape);one=np.ones(shape)
for variant in ['uniform','C_split','C_pilot','C_shrink']:
 counts=np.full(shape,2)
 for _ in range(60):
  draw=lab._allocate_batch(variant,16,z,one,z,one,counts,2,fixed_drivers=[(0,0),(0,1)],fixed_scale=one)
  assert draw.sum()==16 and np.all(draw>=0)
  counts+=draw
 assert counts.min()>2,(variant,counts)
 if variant=='uniform':assert counts.max()-counts.min()<=1
 print(variant,'min/max counts',counts.min(),counts.max())
p=json.load(open(ROOT/'research/next_steps_20260907_014920/query_rware.json'))
profile=cap.static_capability_profile('rware');rt=p['capability_runtime']['runtime_probe']
assert cap.claim_readiness(profile,rt)['QUERY']['ready']
assert not cap.claim_readiness(profile,None)['QUERY']['ready']
assert not cap.claim_readiness(profile,dict(rt,all_receipts_verified=False))['QUERY']['ready']
assert not cap.claim_readiness(profile,dict(rt,cells_probed=0))['QUERY']['ready']
assert not cap.claim_readiness(profile,dict(rt,all_probed_honored=False))['QUERY']['ready']
print('QUERY runtime authority positive/negative checks pass')
p=lab.run(instances=1,seeds=(7101,),relations=3,actions=3,topk=1,max_n=256,batch=4)
assert all(len(v)==1 and v[0]['instance_id']==0 for v in p['runs_by_variant'].values())
print('raw per-instance records pass')
