"""External one-state D6 applicability probe with fail-closed action authority."""
from __future__ import annotations
import argparse,json,itertools,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from research_chains.provenance import atomic_json

ENVIRONMENTS=('cityflow','cyborg','flatland','rware')

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--environment',choices=ENVIRONMENTS,required=True); p.add_argument('--out',required=True); p.add_argument('--agent-count',type=int,default=3); p.add_argument('--max-steps',type=int,default=30); p.add_argument('--max-cells',type=int,default=512); p.add_argument('--config-path'); p.add_argument('--manifest-only',action='store_true'); a=p.parse_args(argv)
    from envs.external.registry import SPECS,repo_path
    spec=SPECS[a.environment]
    payload={'protocol_version':'external_d6_applicability_v1','environment':a.environment,'repo':str(repo_path(a.environment)),'repo_exists':repo_path(a.environment).exists(),'declared_capabilities':vars(spec.capabilities),'d6':{'status':'NOT_RUN','reason':'manifest_only' if a.manifest_only else None}}
    if a.manifest_only:
        atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
    from envs.external.runtime import maybe_reexec_in_external_runtime
    maybe_reexec_in_external_runtime(require_ready=True)
    from envs.external.registry import build_environment
    env=build_environment(a.environment,seed=0,n_agents=a.agent_count,max_steps=a.max_steps,config_path=a.config_path)
    env.reset(seed=101); snapshot=env.clone_state(); actions=[]
    for i in range(int(env.n_agents)):
        mask=np.asarray(env.valid_action_mask(i),dtype=bool); actions.append([int(x) for x in np.flatnonzero(mask)])
    cells=int(np.prod([len(x) for x in actions],dtype=np.int64)); payload['d6'].update({'n_agents':int(env.n_agents),'valid_action_counts':[len(x) for x in actions],'cartesian_cell_count':cells})
    if cells>a.max_cells:
        payload['d6'].update({'status':'BLOCKED','reason':'cartesian_grid_exceeds_max_cells'}); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
    # Generic adapter contract has no executed-action receipt.  Collect values but do not promote applicability.
    values={}; errors=[]
    for local in itertools.product(*(range(len(row)) for row in actions)):
        requested=[actions[i][local[i]] for i in range(len(actions))]
        env.restore_state(snapshot)
        try:
            _,rewards,_,info=env.step(requested); values[local]=float(np.sum(np.asarray(rewards,dtype=float)))
        except Exception as exc: errors.append({'local':list(local),'requested':requested,'error':f'{type(exc).__name__}: {exc}'})
    payload['d6'].update({'requested_cells':cells,'successful_cells':len(values),'errors':errors[:20],'execution_authority_observable':False,'status':'BLOCKED' if len(values)==cells else 'FAILED','reason':'adapter_does_not_expose_requested_equals_executed; command-space Cartesianity is not enough for D6 scientific applicability' if len(values)==cells else 'some requested joint actions failed'})
    # Preserve raw response table for a future authority-enabled adapter without silently certifying it now.
    payload['d6']['response_table']={','.join(map(str,k)):v for k,v in values.items()}
    atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0 if not errors else 2
if __name__=='__main__': raise SystemExit(main())
