"""Full-joint OmniArena D6 stress audit.

Unlike the historical pairwise bridge, this runner enumerates the full
Cartesian command table for 2--4 source agents at cloned states and evaluates
the active D6 diagnostics on the resulting m-coordinate response function.
It is a controlled Omni stress test, not evidence for coupled support: Omni's
command masks are still Cartesian.
"""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np

from envs.omni_arena import OmniArena
from envs.causal_adapter import resolve_env_adapter
from research_chains.oracle import CloneStateJointOracle
from research_chains.experimental_extensions import d6_diagnostics
from research_chains.finite_world import FiniteResponseWorld
from research_chains.support import SupportModel
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='omni_d6_full_joint_v1'


def _sources_and_outcome(env,m_sources):
    roles=env.zone_role_agents[0]
    outcome=int(roles[env.ROLE_COLLECTOR])
    candidates=[int(a) for a in roles.values() if int(a)!=outcome]
    if len(candidates)<m_sources:
        candidates.extend(a for a in range(env.n_agents) if a!=outcome and a not in candidates)
    return tuple(candidates[:m_sources]),outcome


def run(seed=0,m_sources=3,n_states=2,warmup_steps=3):
    if not 2 <= int(m_sources) <= 4: raise ValueError('m_sources must be in [2,4]')
    env=OmniArena(n_agents=8,n_zones=1,max_steps=max(64,int(n_states)*int(warmup_steps)+16),phase_length=1000,enable_structural_shift=False,seed=int(seed))
    env.reset(); adapter=resolve_env_adapter(env); sources,outcome=_sources_and_outcome(env,int(m_sources)); action_dim=int(env.get_action_dim())
    state_rows=[]
    for state_index in range(int(n_states)):
        if state_index>0:
            for _ in range(int(warmup_steps)):
                actions=[int(env.scripted_policy(a)) for a in range(env.n_agents)]
                env.step(actions)
        snapshot=env.clone_state(); baseline=[int(env.scripted_policy(a)) for a in range(env.n_agents)]
        action_sets=[]
        for source in sources:
            mask=np.asarray(adapter.valid_action_mask(source),dtype=bool).reshape(-1)
            if mask.shape!=(action_dim,) or not np.any(mask): raise RuntimeError(f'invalid action mask source={source}')
            actions=tuple(int(x) for x in np.flatnonzero(mask))
            if actions != tuple(range(action_dim)):
                raise RuntimeError('Omni full-joint D6 audit requires full contiguous command alphabet')
            action_sets.append(actions)
        oracle=CloneStateJointOracle(env,snapshot=snapshot,outcome_agent=outcome,baseline_actions=baseline)
        records=oracle.enumerate(sources,action_sets,fail_on_execution_mismatch=True)
        expected=int(np.prod([len(x) for x in action_sets]))
        if len(records)!=expected: raise RuntimeError('incomplete full joint response table')
        table={tuple(r.assignment):float(r.reward) for r in records}
        support=SupportModel(tuple(len(x) for x in action_sets),tuple(sorted(table)),key=f'omni_seed{seed}_state{state_index}')
        world=FiniteResponseWorld(support,tuple(np.zeros(len(x),dtype=float) for x in action_sets),residual=table)
        q={j:np.full(len(action_sets[j]),1.0/len(action_sets[j])) for j in range(len(sources))}
        by_k={}
        for k in range(1,len(sources)):
            d=d6_diagnostics(world,q,k)
            by_k[str(k)]={
                'delta_square':d['delta_square'],'surrogate_sup_error':d['surrogate_sup_error'],'surrogate_tightness':d['surrogate_tightness'],
                'decision_regret':d['true_decision_regret'],'decision_rhs':d['decision_rhs'],'decision_tightness':d['decision_tightness'],
                'decision_ratio_to_worst_rhs':d['decision_ratio_to_worst_rhs'],'half_candidate_violation':d['decision_candidate_half_violation'],
                'qavg_uniform_violation':d['qavg_uniform_candidate_violation'],'qsigned_uniform_violation':d['qsigned_uniform_candidate_violation'],
            }
        state_rows.append({'state_index':state_index,'requested_cells':expected,'verified_cells':len(records),'authority_rate':1.0,'by_k':by_k})
    flat=[row for state in state_rows for row in state['by_k'].values()]
    return {
        'protocol_version':PROTOCOL_VERSION,'development_only':True,'evidence_class':'CONTROLLED_OMNI_FULL_JOINT_D6_STRESS',
        'seed':int(seed),'m_sources':int(m_sources),'n_states':int(n_states),'warmup_steps':int(warmup_steps),'sources':list(sources),'outcome_agent':int(outcome),
        'command_support_semantics':'full Cartesian Omni command support; not coupled-support evidence',
        'states':state_rows,
        'summary':{
            'all_authority_verified':all(s['authority_rate']==1.0 for s in state_rows),
            'positive_decision_regret_fraction':float(np.mean([r['decision_regret']>1e-12 for r in flat])) if flat else 0.0,
            'max_decision_regret':float(max([r['decision_regret'] for r in flat],default=0.0)),
            'max_decision_ratio_to_worst_rhs':float(max([r['decision_ratio_to_worst_rhs'] for r in flat],default=0.0)),
            'max_delta_square':float(max([r['delta_square'] for r in flat],default=0.0)),
            'half_candidate_worst_violation':float(max([r['half_candidate_violation'] for r in flat],default=0.0)),
        },
    }


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--seed',type=int,default=3001); p.add_argument('--m-sources',type=int,default=3); p.add_argument('--n-states',type=int,default=2); p.add_argument('--warmup-steps',type=int,default=3); p.add_argument('--out',default='research/high_value_extensions/d6/omni_full_joint.json'); a=p.parse_args(argv)
    payload=run(a.seed,a.m_sources,a.n_states,a.warmup_steps); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
