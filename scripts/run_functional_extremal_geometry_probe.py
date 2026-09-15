"""Paired development test: fixed outer gap and noise, varying inner extremal gaps.
Action extrema are permuted separately for each relation and instance; the
sampler only sees observations. This is not an optimality or novelty claim.
"""
from __future__ import annotations
import argparse,hashlib,json,sys
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from scripts.run_functional_variance_stopping_lab_v3 import _one_variant


def main():
    p=argparse.ArgumentParser();p.add_argument('--instances',type=int,default=12)
    p.add_argument('--seed',type=int,default=91001);p.add_argument('--max-n',type=int,default=16384)
    p.add_argument('--batch',type=int,default=128);p.add_argument('--out',required=True);a=p.parse_args()
    rng=np.random.default_rng(a.seed);rows=[];out=Path(a.out);out.parent.mkdir(parents=True,exist_ok=True)
    for i in range(a.instances):
        permutations=[rng.permutation(6) for _ in range(3)]
        noise=rng.normal(0,.3,size=(3,6,a.max_n+8))
        for gap in [.01,.2]:
            truth=[]
            for r,cap in enumerate([1.4,1.2,1.]):
                v=np.array([-cap/2,-cap/2+gap,-.05,.05,cap/2-gap,cap/2])
                truth.append(v[permutations[r]])
            truth=np.asarray(truth);streams=truth[:,:,None]+noise
            assert np.allclose(np.ptp(truth,axis=1),[1.4,1.2,1.])
            for mode in ['uniform','C_anytime','C_shrink','C_known_sigma']:
                result=_one_variant(truth,np.full(6,.3),streams,mode,k=1,alpha=.05,
                    max_n=a.max_n,batch=a.batch,pilot_fraction=.15)
                result.update(instance=i,inner_gap=gap,variant=mode);rows.append(result)
        payload=dict(evidence_class='DEVELOPMENT_PAIRED_GEOMETRY_FALSIFICATION',seed=a.seed,
            requested_instances=a.instances,completed_instances=i+1,max_n=a.max_n,batch=a.batch,
            outer_gap=.2,noise_sigma=.3,independent_cell_noise=True,extremal_locations='permuted per relation',
            primary_estimand='Difference in certificate probability / stopping cost at fixed outer gap and noise when inner extremal gap changes',
            censoring='N_certificate is null when not certified; do not report censored median as identified',
            script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            runner_sha256=hashlib.sha256((ROOT/'scripts/run_functional_variance_stopping_lab_v3.py').read_bytes()).hexdigest(),rows=rows)
        tmp=out.with_suffix('.tmp');tmp.write_text(json.dumps(payload,indent=2)+'\n');tmp.replace(out)
        print(f'completed {i+1}/{a.instances}',flush=True)
if __name__=='__main__':main()
