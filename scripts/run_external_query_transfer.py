"""Cross-query transfer matrix on real adapter states with common interventions.

Every method/query uses the same cloned state bank and single-agent intervention
panels. Unsupported semantics are NA with an explicit blocker; no foreign query
is silently substituted.
"""
from __future__ import annotations
import argparse,itertools,json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from scipy.stats import spearmanr

from envs.external.capability_audit import audit_environment
from research_chains.oracle import CloneStateJointOracle
from research_chains.query_baselines import METHOD_SCOPE,response_primitives,exact_noop_shapley,query_regret
from research_chains.provenance import atomic_json
from envs.external.runtime import maybe_reexec_in_external_runtime

PROTOCOL_VERSION='external_query_transfer_v1'


def _valid_actions(env,a):
    mask=np.asarray(env.valid_action_mask(int(a)),bool).reshape(-1); out=tuple(int(x) for x in np.flatnonzero(mask))
    if not out: raise RuntimeError(f'no valid action agent={a}')
    return out


def _relation_feature_scores(env,outcome,candidates):
    return np.asarray([float(np.linalg.norm(np.asarray(env.relation_features(outcome,a),float))) for a in candidates])


def _coalition_values(env,snapshot,outcome,candidates,baseline,noop):
    # Active players keep baseline; inactive players are replaced by noop.
    values={}
    for bits in itertools.product((0,1),repeat=len(candidates)):
        active=tuple(i for i,b in enumerate(bits) if b); actions=list(baseline)
        for local,agent in enumerate(candidates): actions[agent]=baseline[agent] if bits[local] else noop[local]
        env.restore_state(snapshot); _,rewards,_,_=env.step(actions); values[active]=float(rewards[outcome])
    env.restore_state(snapshot); return values


def _state_panel(env,outcome,candidates,k):
    snapshot=env.clone_state(); baseline=[int(env.fixed_continuation_policy(i)) for i in range(int(env.n_agents))]
    # Prefer the state bank's actually executed behavior action when available;
    # otherwise choose a non-noop valid action as the active treatment.
    prior=getattr(env,'last_actions',None)
    if prior is not None and len(prior)==int(env.n_agents): baseline=[int(a) for a in prior]
    rows=[]; base_idx=[]; noop_idx=[]; kept=[]; honored_actions=[]
    for agent in candidates:
        acts=_valid_actions(env,agent); oracle=CloneStateJointOracle(env,snapshot=snapshot,outcome_agent=outcome,baseline_actions=baseline)
        records=oracle.enumerate([agent],[acts],fail_on_execution_mismatch=False)
        honored=[(int(r.assignment[0]),float(r.reward)) for r in records if r.execution_verified]
        if len(honored)<2: continue
        ha=tuple(a for a,_ in honored); kept.append(int(agent)); honored_actions.append(list(ha)); rows.append(np.asarray([v for _,v in honored],float))
        base_action=int(baseline[agent]); base_idx.append(ha.index(base_action) if base_action in ha else 0); noop_idx.append(ha.index(0) if 0 in ha else base_idx[-1])
    candidates=kept
    if len(candidates)<max(2,int(k)):
        raise RuntimeError('insufficient agents with at least two honored intervention actions')
    primitive=response_primitives(rows,base_idx,noop_idx)
    noop_actions=[]
    for agent,ha in zip(candidates,honored_actions):
        noop_actions.append(0 if 0 in ha else int(baseline[agent]))
    coal=_coalition_values(env,snapshot,outcome,candidates,baseline,noop_actions) if len(candidates)<=6 else None
    shap=exact_noop_shapley(coal,len(candidates)) if coal is not None else None
    scores={**primitive,'RelationFeatureNorm':_relation_feature_scores(env,outcome,candidates)}
    if shap is not None:scores['CoalitionShapley_noop']=np.abs(shap)
    queries={
        'response_sensitivity':primitive['C_response_span'],
        'signed_policy_effect':primitive['D_signed_policy_projection'],
        'removal_noop_effect':primitive['DifferenceReward_noop'],
        'randomization_effect':primitive['RandomizedActionImportance'],
        'interventional_ate':primitive['InterventionalATE_vs_noop'],
    }
    if shap is not None: queries['coalition_contribution']=np.abs(shap)
    matrix={}
    for method,score in scores.items():
        matrix[method]={}
        for query,utility in queries.items():
            rr=query_regret(score,utility,k); rho=spearmanr(score,utility).statistic if len(score)>=2 and not np.allclose(score,score[0]) and not np.allclose(utility,utility[0]) else 0.0
            matrix[method][query]={**rr,'spearman':float(rho) if np.isfinite(rho) else 0.0}
    env.restore_state(snapshot)
    return {'candidates':list(candidates),'honored_action_sets':honored_actions,'outcome_agent':int(outcome),'methods':{m:{'scores':np.asarray(s).tolist(),'implementation_scope':METHOD_SCOPE[m]} for m,s in scores.items()},'queries':{q:np.asarray(u).tolist() for q,u in queries.items()},'matrix':matrix}


def run(key='rware',seed=3001,n_states=8,warmup_steps=3,k=2,n_candidates=4,env=None):
    if env is None:
        from envs.external.registry import build_environment
        env=build_environment(key,seed=int(seed))
    env.reset(seed=int(seed)); capability=audit_environment(key,env=None)
    outcome=0; candidates=[a for a in range(int(env.n_agents)) if a!=outcome][:int(n_candidates)]
    state_rows=[]
    for state in range(int(n_states)):
        if state:
            for step in range(int(warmup_steps)):
                actions=[]
                for i in range(int(env.n_agents)):
                    valid=_valid_actions(env,i); actions.append(int(valid[(state+step+i)%len(valid)]))
                env.step(actions)
        state_rows.append(_state_panel(env,outcome,candidates,min(int(k),len(candidates))))
    methods=sorted({m for row in state_rows for m in row['matrix']}); queries=sorted({q for row in state_rows for x in row['matrix'].values() for q in x})
    aggregate={}
    for m in methods:
        aggregate[m]={}
        for q in queries:
            vals=[row['matrix'][m][q] for row in state_rows if m in row['matrix'] and q in row['matrix'][m]]
            aggregate[m][q]=None if not vals else {'query_regret':float(np.mean([v['regret'] for v in vals])),'topk_exact':float(np.mean([v['topk_exact'] for v in vals])),'spearman':float(np.mean([v['spearman'] for v in vals]))}
    blocked={name:scope for name,scope in METHOD_SCOPE.items() if name not in methods}
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'EXTERNAL_COMMON_STATE_INTERVENTION_TRANSFER','adapter':key,'seed':int(seed),'n_states':int(n_states),'k':int(k),'common_state_contract':'all methods derive from the same frozen state and intervention panel','capability_static':capability,'method_scope':METHOD_SCOPE,'blocked_methods':blocked,'states':state_rows,'aggregate_transfer_matrix':aggregate}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--adapter',choices=['rware','flatland','cyborg','cityflow'],default='rware'); p.add_argument('--seed',type=int,default=3001); p.add_argument('--n-states',type=int,default=8); p.add_argument('--warmup-steps',type=int,default=3); p.add_argument('--k',type=int,default=2); p.add_argument('--n-candidates',type=int,default=4); p.add_argument('--out',default='research/external/query_transfer.json'); a=p.parse_args(argv)
    maybe_reexec_in_external_runtime(require_ready=True)
    payload=run(a.adapter,a.seed,a.n_states,a.warmup_steps,a.k,a.n_candidates); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
