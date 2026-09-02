"""Exact small-m search for Budget-Transversal Prefix-Cover Dimension."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.finite_world import FiniteResponseWorld
from research_chains.support import SupportModel
from research_chains.novelty_completion import prefix_cover_dimension
from research_chains.provenance import write_artifact_with_provenance
PROTOCOL_VERSION='structural_prefix_cover_dimension_v1'

def _world(rng,m):
    sizes=(2,)*m; full=list(np.ndindex(*sizes)); p=float(rng.uniform(.2,.85)); omega=[a for a in full if rng.random()<p]
    if not omega: omega=[full[0]]
    for j in range(m):
        for x in range(2):
            if not any(a[j]==x for a in omega): omega.append(next(a for a in full if a[j]==x))
    primitives=tuple(np.asarray([0.,float(rng.choice([-4,-3,-2,-1,1,2,3,4]))]) for _ in range(m))
    return FiniteResponseWorld(SupportModel(sizes,tuple(sorted(set(omega))),key='prefix'),primitives)

def run(instances=500,seed=0,m_values=(3,4,5,6),epsilon=0.0):
    rng=np.random.default_rng(seed); hist={}; best=None
    for idx in range(int(instances)):
        m=int(m_values[idx%len(m_values)]); w=_world(rng,m); row=prefix_cover_dimension(w,float(epsilon)); d=int(row['dimension']); hist[str(d)]=hist.get(str(d),0)+1
        witness={'m':m,'dimension':d,'support':[list(a) for a in w.support.omega],'primitives':[x.tolist() for x in w.primitives],**row}
        if best is None or (d,m)>(best['dimension'],best['m']): best=witness
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),'m_values':list(map(int,m_values)),'epsilon':float(epsilon),
            'dimension_histogram':hist,'max_dimension_found':int(best['dimension']) if best else None,'chi_ge_3_found':bool(best and best['dimension']>=3),'best_witness':best,
            'scope':'exact finite search; absence of chi>=3 is not a theorem'}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=500); p.add_argument('--seed',type=int,default=0); p.add_argument('--m-values',nargs='+',type=int,default=[3,4,5,6]); p.add_argument('--epsilon',type=float,default=0.0); p.add_argument('--out',default='research/novelty_critical/structural_prefix_cover.json'); a=p.parse_args(argv)
    out=run(a.instances,a.seed,tuple(a.m_values),a.epsilon); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'m_values':a.m_values,'epsilon':a.epsilon},seed=a.seed,evidence_class='DEVELOPMENT_EXACT_SMALL_SEARCH',chain='STRUCTURAL'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
