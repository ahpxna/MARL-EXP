"""Compare reset states with explicitly constructed RWARE delivery-opportunity states.

This is a positive control for non-degenerate one-step query targets, not a claim
about natural trajectories or continuation returns. All generated states remain
in the denominators; no state is selected by its measured query response.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys
import numpy as np
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from scripts.run_external_query_transfer import _state_panel, aggregate_transfer_matrix
from research_chains.provenance import write_artifact_with_provenance
from envs.external.runtime import maybe_reexec_in_external_runtime

PROTOCOL_VERSION='query_rware_one_step_signal_control_v1'


def delivery_opportunity(env, candidates, seed, distance=1):
    """Place two seeded candidate carriers one legal forward step from two goals.

    Uses the pinned RWARE state's own agents/shelves/requests and reward engine;
    neither reward nor oracle values are patched. Resets precede each fixture.
    """
    from rware.warehouse import Action, Direction
    from envs.external.common import pad_observations
    raw=env.raw_env
    if len(raw.goals)<2 or len(candidates)<2:
        raise ValueError('positive control needs two goals and two candidate agents')
    rng=np.random.default_rng(int(seed))
    carriers=[int(i) for i in rng.choice(candidates,size=2,replace=False)]
    goals=list(raw.goals[:2])  # Pinned RWARE stores (x,y); the reward loop reverses names.
    if int(distance)<1: raise ValueError("distance must be positive")
    sites=[(int(x),int(y)-int(distance)) for x,y in goals]
    reserved={(int(x),int(y)-d) for x,y in goals for d in range(int(distance)+1)}
    if any(y<0 or not raw._is_highway(x,y) for x,y in reserved):
        raise ValueError('pinned layout does not have a highway directly above each goal')
    shelves=list(raw.request_queue[:2])
    if len(shelves)!=2: raise ValueError('two requested shelves are required')
    other_shelf_positions={(s.x,s.y) for s in raw.shelfs if s not in shelves}
    if reserved & other_shelf_positions: raise ValueError('delivery paths blocked by stationary shelves')
    free=[(x,y) for y in range(raw.grid_size[0]) for x in range(raw.grid_size[1])
          if raw._is_highway(x,y) and (x,y) not in reserved and (x,y) not in other_shelf_positions]
    rng.shuffle(free)
    for i,agent in enumerate(raw.agents):
        agent.carrying_shelf=None
        agent.req_action=Action.NOOP
        agent.has_delivered=False
        if i in carriers:
            j=carriers.index(i); agent.x,agent.y=sites[j]; agent.dir=Direction.DOWN
            shelf=shelves[j]; shelf.x,shelf.y=sites[j]; agent.carrying_shelf=shelf
        else:
            agent.x,agent.y=free.pop(); agent.dir=Direction.UP
        agent.prev_x,agent.prev_y=agent.x,agent.y
    raw._recalc_grid()
    env._obs=pad_observations([raw._make_obs(a) for a in raw.agents],env.obs_dim)
    env.last_requested_actions=[0]*env.n_agents
    env.last_executed_actions=[0]*env.n_agents
    env.last_actions=[0]*env.n_agents
    assert len({(a.x,a.y) for a in raw.agents})==env.n_agents
    assert len({(s.x,s.y) for s in raw.shelfs})==len(raw.shelfs)
    return {'design':'two_requested_shelf_carriers_one_step_from_goals',
            'carrier_candidates':carriers,'goals_xy':[list(g) for g in goals],'distance_to_goal':int(distance),
            'selection_uses_query_outcomes':False,'natural_trajectory_claim':False}


def summarize(rows):
    methods=sorted({m for r in rows for m in r.get('matrix',{})})
    queries=sorted({q for r in rows for m in r.get('matrix',{}).values() for q in m})
    full,fc=aggregate_transfer_matrix(rows,methods,queries,'full')
    matched,mc=aggregate_transfer_matrix(rows,methods,queries,'matched')
    targets=[q for r in rows for q in r.get('queries',{}).values()]
    return {'requested_states':len(rows),'executable_states':sum(r['status']=='OK' for r in rows),
            'state_query_targets':len(targets),
            'nonconstant_state_query_targets':sum(q['diagnostics']['regret_evaluable'] for q in targets),
            'ranking_evaluable_state_query_targets':sum(q['diagnostics']['ranking_evaluable'] for q in targets),
            'full_information_counts':fc,'matched_budget_counts':mc,
            'aggregate_transfer_matrix':full,'aggregate_transfer_matrix_matched_budget':matched,
            'states':rows}


def run(seed=8301,n_states=8,warmup_steps=3,information_budget=128):
    from envs.external.registry import build_environment
    if n_states<1 or warmup_steps<0 or information_budget<0:
        raise ValueError('positive n_states, nonnegative warmup and information budget required')
    env=build_environment('rware',seed=seed,n_agents=5)
    candidates=[1,2,3,4];banks={}
    for design in ['reset_random_warmup','delivery_opportunity']:
        rows=[]
        for j in range(n_states):
            state_seed=int(seed)+j;env.reset(seed=state_seed)
            metadata={'design':design,'selection_uses_query_outcomes':False}
            if design=='delivery_opportunity':
                metadata.update(delivery_opportunity(env,candidates,state_seed))
            else:
                rng=np.random.default_rng(state_seed)
                for _ in range(warmup_steps):
                    acts=[int(rng.choice(np.flatnonzero(env.valid_action_mask(a)))) for a in range(5)]
                    _,_,done,_=env.step(acts)
                    if bool(np.all(done)): break
            snapshot=env.clone_state()
            try:
                row=_state_panel(env,0,candidates,2,information_budget=information_budget,expected_candidates=4)
            except Exception as exc:
                row={'status':'BLOCKED','reason':f'{type(exc).__name__}: {exc}','matrix':{},'queries':{}}
            finally:
                env.restore_state(snapshot)
            row['state_seed']=state_seed;row['state_design']=metadata;rows.append(row)
        banks[design]=summarize(rows)
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'DEVELOPMENT_POSITIVE_CONTROL',
            'seed':seed,'response_estimand':'Q_one_step','execution_semantics':'full_joint',
            'matched_information_budget':information_budget,'warmup_steps':warmup_steps,
            'state_policy':'all predetermined states retained, including blocked and constant targets',
            'interpretation':'Controlled delivery states diagnose signal plumbing; they do not establish general transfer performance.',
            'banks':banks}


def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--seed',type=int,default=8301)
    p.add_argument('--n-states',type=int,default=8)
    p.add_argument('--warmup-steps',type=int,default=3)
    p.add_argument('--information-budget',type=int,default=128)
    p.add_argument('--out',default='research/external/query_signal_probe.json')
    a=p.parse_args(argv);maybe_reexec_in_external_runtime(require_ready=True)
    result=run(a.seed,a.n_states,a.warmup_steps,a.information_budget)
    write_artifact_with_provenance(Path(a.out),result,protocol={'protocol_version':PROTOCOL_VERSION,
        'seed':a.seed,'n_states':a.n_states,'warmup_steps':a.warmup_steps,'information_budget':a.information_budget},
        seed=a.seed,evidence_class=result['evidence_class'],chain='QUERY')
    print(json.dumps({name:{k:v for k,v in bank.items() if k not in ['states','aggregate_transfer_matrix','aggregate_transfer_matrix_matched_budget']}
                      for name,bank in result['banks'].items()},indent=2))
    return 0 if result['banks']['delivery_opportunity']['full_information_counts']['regret_cells']>0 else 2

if __name__=='__main__': raise SystemExit(main())
