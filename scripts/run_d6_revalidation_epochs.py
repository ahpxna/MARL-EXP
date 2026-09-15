"""Finite-horizon evidence for LeanD6RepeatedDiscoveryV1.
A missing certificate uses a blind fallback and is charged as a bad epoch.
The theorem covers infinitely many epochs; this experiment cannot prove that.
"""
import argparse,hashlib,json,math
from pathlib import Path
import numpy as np
from run_d6_nuisance_free_discovery import means_from_world


def main():
 p=argparse.ArgumentParser();p.add_argument('--trials',type=int,default=300);p.add_argument('--epochs',type=int,default=12);p.add_argument('--seed',type=int,default=91042);p.add_argument('--out',required=True);a=p.parse_args()
 rng=np.random.default_rng(a.seed);rows=[]
 for q in [4,64,256,1024]:
  d=2*q+1
  for mu in [0,.5,1.]:
   b=np.zeros(d,int);b[rng.choice(d,q,False)]=1
   other=means_from_world(q,mu,b)
   anchor=np.array([other[0,0],other[0,0],other[0,3],other[0,3]])
   means=np.vstack([anchor,other]);contrast=means@np.array([1,-1,1,-1])
   assert np.allclose(contrast,b-b[0],atol=1e-12)
   for r0 in [512,1024]:
    sums=np.zeros((a.trials,d));bad_work=np.zeros(a.trials);trace=[]
    for s in range(a.epochs):
     # Exact law of the sum of r0 four-query contrasts, with all raw draws charged.
     sums+=rng.normal(r0*contrast,2*math.sqrt(r0),size=(a.trials,d))
     score=sums/(r0*(s+1));order=np.argsort(score,axis=1)
     gap=np.take_along_axis(score,order[:,-q:],axis=1).min(1)-np.take_along_axis(score,order[:,:-q],axis=1).max(1)
     certified=gap>.5;guess=np.zeros((a.trials,d),int)
     np.put_along_axis(guess,order[:,-q:],1,axis=1)
     wrong=np.any(guess!=b,axis=1)&certified
     invalid=~certified|wrong
     bad_work+=2**s*invalid
     trace.append(dict(epoch=s,missing_certificate=int((~certified).sum()),wrong_certificate=int(wrong.sum())))
    eta=2*d*math.exp(-r0/128)
    C=4*d*r0
    rows.append(dict(q=q,d=d,mu=mu,r0=r0,trials=a.trials,epochs=a.epochs,
     mean_normalized_bad_epoch_work=float(bad_work.mean()),theoretical_infinite_expected_bad_epoch_work_upper=2*eta,
     query_cost_per_discovery_epoch=C,total_discovery_queries=C*a.epochs,
     allocation_epoch_lengths=[C*2**s for s in range(a.epochs)],trace=trace))
  print(json.dumps(dict(q=q,completed=True)),flush=True)
 result=dict(evidence_class='DEVELOPMENT_ACTUAL_QUERY_GAUSSIAN_SUFFICIENT_STATISTICS',seed=a.seed,
  scope='Repeated discovery only; missing certificate uses blind fallback. No theorem about regret of good-epoch allocations or Gamma tracking.',rows=rows,
  script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
 out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
