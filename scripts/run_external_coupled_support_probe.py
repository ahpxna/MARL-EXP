"""Probe non-Cartesian *honored/executable* joint support on external adapters.

Requestable support remains the product of per-agent masks.  This runner asks a
separate question: among requested tuples, which tuples are actually resolved
and honored exactly by the environment?  Only that explicitly named support is
used for the coupled-support diagnostic.
"""
from __future__ import annotations
import argparse,itertools,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from envs.external.runtime import maybe_reexec_in_external_runtime
from envs.external.capability_audit import probe_execution_and_support
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='external_honored_support_probe_v1'


def _rectangularity(rows,n_sources):
    omega={tuple(r['requested']) for r in rows if r.get('verified') and r.get('fully_honored')}
    if not omega:return {'honored_cells':0,'projection_product_size':0,'rectangular':False,'coupled':False,'omega':[]}
    projections=[sorted({a[j] for a in omega}) for j in range(int(n_sources))]
    product=set(itertools.product(*projections))
    rejected_inside=[tuple(r['requested']) for r in rows if r.get('verified') and not r.get('fully_honored') and tuple(r['requested']) in product]
    return {'honored_cells':len(omega),'projection_product_size':len(product),'rectangular':bool(not rejected_inside and omega==product),'coupled':bool(rejected_inside),'coupling_witnesses':[list(x) for x in rejected_inside],'projection_sizes':[len(x) for x in projections],'omega':[list(x) for x in sorted(omega)]}


def run(key='rware',seed=3001,n_states=16,n_sources=2,warmup_steps=2,max_cells=512,env=None):
    if env is None:
        from envs.external.registry import build_environment
        env=build_environment(key,seed=int(seed))
    env.reset(seed=int(seed)); sources=list(range(min(int(n_sources),int(env.n_agents)))); state_rows=[]
    for state in range(int(n_states)):
        if state:
            for step in range(int(warmup_steps)):
                actions=[]
                for i in range(int(env.n_agents)):
                    mask=np.asarray(env.valid_action_mask(i),bool); valid=np.flatnonzero(mask)
                    actions.append(int(valid[(state+step+i)%len(valid)]))
                env.step(actions)
        probe=probe_execution_and_support(env,agents=sources,max_cells=int(max_cells)); geom=_rectangularity(probe['rows'],len(sources))
        state_rows.append({'state':state,'probe':{k:v for k,v in probe.items() if k!='rows'},'geometry':geom})
    coupled=[r for r in state_rows if r['geometry']['coupled']]
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'EXTERNAL_HONORED_EXECUTION_SUPPORT','semantic_scope':'post-resolution honored/executable support; NOT pre-execution requestable feasibility','adapter':key,'seed':int(seed),'n_states':int(n_states),'n_sources':len(sources),'sources':sources,'states':state_rows,'summary':{'coupled_state_fraction':float(len(coupled)/len(state_rows)) if state_rows else 0.0,'coupled_states':len(coupled),'all_receipts_verified':bool(all(r['probe']['all_receipts_verified'] for r in state_rows))}}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--adapter',choices=['rware','flatland','cyborg','cityflow'],default='rware'); p.add_argument('--seed',type=int,default=3001); p.add_argument('--n-states',type=int,default=16); p.add_argument('--n-sources',type=int,default=2); p.add_argument('--warmup-steps',type=int,default=2); p.add_argument('--max-cells',type=int,default=512); p.add_argument('--out',default='research/external/honored_support.json'); a=p.parse_args(argv)
    maybe_reexec_in_external_runtime(require_ready=True)
    payload=run(a.adapter,a.seed,a.n_states,a.n_sources,a.warmup_steps,a.max_cells); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
