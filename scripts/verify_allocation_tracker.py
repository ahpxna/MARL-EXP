"""Numerical construction check of LeanFiniteAllocationTrackerV1 (not proof)."""
import argparse,hashlib,json
from pathlib import Path
import numpy as np


def main():
 p=argparse.ArgumentParser();p.add_argument('--seed',type=int,default=91043);p.add_argument('--out',required=True);a=p.parse_args()
 rng=np.random.default_rng(a.seed);rows=[]
 for k in [2,4,8,16,32,64]:
  for family in ['switching','spiky','rotating','diffuse']:
   for horizon in [128,1024,4096]:
    target=np.zeros(k);count=np.zeros(k,int);history=[];max_abs=0.;max_upper=0.
    for t in range(horizon):
     if family=='switching':
      w=np.zeros(k);w[(t//17)%k]=1
     elif family=='rotating':
      w=np.zeros(k);w[t%k]=.75;w[(t+1)%k]+=.25
     else:w=rng.dirichlet(np.full(k,.03 if family=='spiky' else 1.))
     target+=w
     # Any below-target coordinate is permitted by the Lean construction.
     below=np.flatnonzero(count<target-1e-12)
     assert len(below)
     i=int(below[0]);count[i]+=1;history.append(i)
     diff=count-target
     assert abs(count.sum()-(t+1))==0
     assert diff.max()<=1+1e-9 and abs(diff).max()<=k+1e-9
     max_abs=max(max_abs,float(abs(diff).max()));max_upper=max(max_upper,float(diff.max()))
    assert np.array_equal(count,np.bincount(history,minlength=k))
    rows.append(dict(k=k,family=family,horizon=horizon,max_abs_discrepancy=max_abs,max_upper_discrepancy=max_upper,
                     final_l1_discrepancy=float(abs(count-target).sum()),formal_bound=k))
 out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True)
 out.write_text(json.dumps(dict(evidence_class='NUMERICAL_CONSTRUCTIVE_TRACKING_CHECK',seed=a.seed,rows=rows,
   script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()),indent=2)+'\n')
 print(json.dumps(dict(cases=len(rows),steps=sum(r['horizon'] for r in rows),violations=0)))
if __name__=='__main__':main()
