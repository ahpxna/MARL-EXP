"""Finite semantic identifiability verifier lab.

Natural-language routing is intentionally out of scope.  The experiment asks
whether a typed evidence summary identifies the requested target on a finite
model class and, when it does not, returns an exact same-summary/different-
target witness plus the two-world minimax floor.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.provenance import write_artifact_with_provenance
PROTOCOL_VERSION='query_identifiability_verifier_lab_v1'

def verify(summary,target):
    groups={}
    for i,s in enumerate(summary): groups.setdefault(tuple(np.atleast_1d(s).tolist()),[]).append(i)
    for key,idxs in groups.items():
        vals=[target[i] for i in idxs]
        if max(vals)-min(vals)>1e-12:
            lo=min(idxs,key=lambda i:target[i]); hi=max(idxs,key=lambda i:target[i])
            return {'status':'INSUFFICIENT','summary':list(key),'witness':[int(lo),int(hi)],'target_values':[float(target[lo]),float(target[hi])],
                    'minimax_floor':0.5*abs(float(target[hi]-target[lo]))}
    return {'status':'IDENTIFIABLE','witness':None,'minimax_floor':0.0}

def run(instances=1000,seed=0):
    rng=np.random.default_rng(seed); insufficient=0; floors=[]; examples=[]
    for _ in range(int(instances)):
        n=int(rng.integers(4,10)); summary=rng.integers(0,max(2,n//2),size=n); target=rng.normal(size=n)
        # Half the time make target a true function of summary, half inject a fibre conflict.
        if rng.random()<.5:
            mapping={s:float(rng.normal()) for s in set(map(int,summary))}; target=np.asarray([mapping[int(s)] for s in summary])
        out=verify(summary,target); insufficient+=int(out['status']=='INSUFFICIENT'); floors.append(out['minimax_floor'])
        if out['status']=='INSUFFICIENT' and len(examples)<20: examples.append(out)
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),
            'frontend_scope':'typed query/evidence only; natural-language method routing is not a novelty claim',
            'insufficient_fraction':float(insufficient/int(instances)),'mean_minimax_floor':float(np.mean(floors)),
            'witness_examples':examples,'status_values':['IDENTIFIABLE','INSUFFICIENT','BLOCKED_NA'],
            'blocked_na_note':'BLOCKED_NA is emitted by external capability contracts and is not simulated by this finite identifiability lab'}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=1000); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/novelty_critical/query_identifiability.json'); a=p.parse_args(argv)
    out=run(a.instances,a.seed); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'instances':a.instances},seed=a.seed,evidence_class='DEVELOPMENT_FINITE_IDENTIFIABILITY',chain='QUERY'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
