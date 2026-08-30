"""R_iso + PAIRWISE + near-additive transfer falsification laboratory."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, json, itertools
from pathlib import Path
import numpy as np

from research_chains.certificates import exact_optimum, topk_indices, zeta_def
from research_chains.finite_world import FiniteResponseWorld
from research_chains.pairwise import operational_gamma, pairwise_master_bound, sharp_gamma
from research_chains.reference import ConditionalReferenceKernel
from research_chains.support import SupportModel
from research_chains.provenance import atomic_json

PROTOCOL_VERSION="chain_rp_reference_pairwise_lab_v2"


def _world(rng,m=4,eta=0.15):
    sizes=(2,)*m; full=list(np.ndindex(*sizes))
    omega=[a for a in full if rng.random()<0.7]
    # Feasible conditional kernel requires every source action to appear. Add full corners if needed.
    for j in range(m):
        for a in range(2):
            if not any(x[j]==a for x in omega):
                candidate=next(x for x in full if x[j]==a); omega.append(candidate)
    omega=tuple(sorted(set(omega)))
    primitives=tuple(rng.normal(size=2) for _ in range(m))
    residual={a:float(rng.uniform(-eta,eta)) for a in full}
    return FiniteResponseWorld(SupportModel(sizes,omega,key='truth'),primitives,residual=residual)


def run(instances=500,seed=0):
    rng=np.random.default_rng(seed); failures=[]; worst={"R1":0.0,"TV":0.0,"rho":0.0,"pairwise_sharp":0.0,"pairwise_operational":0.0}
    for idx in range(int(instances)):
        eta=float(rng.uniform(0,0.2)); world=_world(rng,eta=eta); m=world.support.n_relations; k=int(rng.integers(1,m+1))
        ctrue=world.component_spans(); chat=[]; errors=[]
        for j in range(m):
            kernel=ConditionalReferenceKernel.uniform_feasible(world.support,j,key=f'feasible_j{j}')
            qadd=kernel.response_vector(world,true_response=False); qtrue=kernel.response_vector(world,true_response=True)
            cpair_add=float(np.max(qadd)-np.min(qadd)); cpair_true=float(np.max(qtrue)-np.min(qtrue))
            chi=kernel.isolation_deviation(world); rho=kernel.residual_deviation(world)
            r1=abs(cpair_add-ctrue[j])-chi; tv=chi-kernel.tv_isolation_upper_bound(world); rv=rho-2*eta
            worst['R1']=max(worst['R1'],r1); worst['TV']=max(worst['TV'],tv); worst['rho']=max(worst['rho'],rv)
            noise=float(rng.uniform(-0.05,0.05)); estimate=max(0.0,cpair_true+noise)
            delta=abs(estimate-cpair_true); e=delta+chi+rho
            chat.append(estimate); errors.append(e)
        chat=np.asarray(chat); errors=np.asarray(errors)
        if np.any(np.abs(chat-ctrue)-errors>1e-9):
            failures.append({"kind":"score_cover","idx":idx}); continue
        selected=topk_indices(chat,k); true_opt,_=exact_optimum(world,k,true_loss=True); actual=world.true_compression_loss(selected)-true_opt
        z=zeta_def(world,k)
        sg=sharp_gamma(ctrue,chat,errors,k); og=operational_gamma(chat,errors,k,selected)
        sharp_bound=pairwise_master_bound(sg,z,eta); op_bound=pairwise_master_bound(og,z,eta)
        worst['pairwise_sharp']=max(worst['pairwise_sharp'],actual-sharp_bound); worst['pairwise_operational']=max(worst['pairwise_operational'],actual-op_bound)
        if max(r1,tv,rv,actual-sharp_bound,actual-op_bound)>1e-8:
            failures.append({"kind":"bound","idx":idx,"actual":actual,"sharp":sharp_bound,"operational":op_bound})
    return {"protocol_version":PROTOCOL_VERSION,"development_only":True,"instances":int(instances),"seed":int(seed),"failure_count":len(failures),"failures":failures[:20],"worst_violation":worst}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=500); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/new_chains_v2/chain_rp/summary.json'); a=p.parse_args(argv)
    payload=run(a.instances,a.seed); atomic_json(Path(a.out),payload); print(json.dumps({k:payload[k] for k in ('protocol_version','instances','failure_count','worst_violation')},indent=2)); return 0 if payload['failure_count']==0 else 2
if __name__=='__main__': raise SystemExit(main())
