import pathlib,json,sys,time
import numpy as np
from scipy.optimize import minimize_scalar
p=pathlib.Path('/Users/phanan/cig-amf-main');d=json.loads((p/'research/paper_exp_20260916/functional_proxy.json').read_text()); rows=d['rows']
# Deliberately stress the grid: twenty smallest capacity gaps; forty spread indices.
want=set(sorted(range(len(rows)),key=lambda i:rows[i]['cap_i']-rows[i]['cap_j'])[:20]);want.update(np.linspace(0,len(rows)-1,40,dtype=int).tolist())
rng=np.random.default_rng(20260916);out=[];t0=time.time()
def shrink(t,a,z):
 if z>=np.ptp(t):return 0.
 lo=float(t.min()-z);hi=float(t.max())
 for _ in range(45):
  mid=(lo+hi)/2
  grad=np.dot(a,mid-np.clip(t,mid,mid+z)+np.minimum(t-mid,0)) if False else np.dot(a,np.maximum(mid-t,0)-np.maximum(t-mid-z,0))
  if grad>0:hi=mid
  else:lo=mid
 x=np.clip(t,(lo+hi)/2,(lo+hi)/2+z)
 return .5*float(np.dot(a,(x-t)**2))
for i in range(len(rows)):
 A=int(rng.integers(3,9));ti=rng.uniform(0,1,A);tj=rng.uniform(0,1,A);ai=10**rng.uniform(-2,1,A);aj=10**rng.uniform(-2,1,A)
 if np.ptp(ti)<=np.ptp(tj):ti,tj=tj,ti;ai,aj=aj,ai
 if i not in want:continue
 assert abs(np.ptp(ti)-rows[i]['cap_i'])<1e-14 and abs(np.ptp(tj)-rows[i]['cap_j'])<1e-14
 best=float('inf');arg=None
 for c in range(A):
  for e in range(A):
   if c==e:continue
   gap=tj[c]-tj[e];v=aj[c]*aj[e]/(aj[c]+aj[e]);hi=float(np.ptp(ti))
   def f(z):return shrink(ti,ai,z)+.5*max(z-gap,0)**2*v
   r=minimize_scalar(f,bounds=(0,hi),method='bounded',options={'xatol':1e-14,'maxiter':200})
   val=min(r.fun,f(0),f(hi))
   if val<best:best=val;arg=(c,e)
 old=rows[i]['j_full'];rel=(old-best)/max(best,1e-300)
 out.append({'index':i,'old':old,'allpair_numerical':best,'relative_overestimate':rel,'best_pair':arg})
result={'scope':'Independent bounded numerical diagnostic; evaluates every pair on 60 existing worlds, not a certified solver','count':len(out),'max_relative_overestimate':max(x['relative_overestimate'] for x in out),'over_1e-6':int(sum(x['relative_overestimate']>1e-6 for x in out)),'rows':out,'seconds':time.time()-t0}
f=pathlib.Path('/tmp/cig_functional_allpair_check_20260919.json');f.write_text(json.dumps(result,indent=2));print({k:v for k,v in result.items() if k!='rows'},flush=True)
