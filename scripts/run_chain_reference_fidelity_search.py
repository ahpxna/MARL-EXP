"""Finite search for universal reference-fidelity characterization."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, json
from pathlib import Path
import numpy as np

from research_chains.reference import ConditionalReferenceKernel, reference_fidelity_characterization
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='chain_reference_fidelity_search_v2'


def _random_kernel(rng, sizes=(2,2,2), source=0):
    full=list(np.ndindex(*sizes)); rows={}
    for a in range(sizes[source]):
        compatibles=[x for x in full if x[source]==a]
        probs=rng.dirichlet(np.ones(len(compatibles)))
        rows[a]={x:float(p) for x,p in zip(compatibles,probs)}
    return ConditionalReferenceKernel(source,sizes,rows,key='random')


def run(instances=2000,seed=0):
    rng=np.random.default_rng(seed); failures=[]; invariant_count=0; witness_count=0
    # Product kernels must always pass.
    for idx in range(int(instances)):
        if idx % 5 == 0:
            marg={0:[.5,.5],1:rng.dirichlet(np.ones(2)),2:rng.dirichlet(np.ones(2))}
            kernel=ConditionalReferenceKernel.product((2,2,2),0,marg,key='product')
        else:
            kernel=_random_kernel(rng)
        result=reference_fidelity_characterization(kernel)
        invariant_count+=int(result['marginal_invariant']); witness_count+=int(result['witness'] is not None)
        if result['marginal_invariant'] and result['witness'] is not None:
            failures.append({'idx':idx,'kind':'invariant_has_witness'})
        if (not result['marginal_invariant']) and result['witness'] is None:
            failures.append({'idx':idx,'kind':'noninvariant_missing_basis_witness'})
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'failure_count':len(failures),'failures':failures[:20],'invariant_count':invariant_count,'noninvariant_basis_witness_count':witness_count}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=2000); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/new_chains_v2/reference_fidelity/summary.json'); a=p.parse_args(argv)
    payload=run(a.instances,a.seed); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0 if payload['failure_count']==0 else 2
if __name__=='__main__': raise SystemExit(main())
