"""Cross-query transfer matrix on real adapter states with common interventions.

Every method/query uses the same cloned state bank and single-agent intervention
panels. Unsupported semantics are NA with an explicit blocker; no foreign query
is silently substituted.
"""
from __future__ import annotations
import argparse,itertools,json,hashlib
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from scipy.stats import kendalltau,spearmanr

from envs.external.capability_audit import audit_environment
from research_chains.oracle import CloneStateJointOracle,trusted_execution_receipt
from research_chains.query_baselines import response_primitives,exact_noop_shapley,query_regret
from research_chains.query_contracts import (BLOCKER_REASON, ExternalQueryContext, METHOD_SPECS,
    QUERY_SPECS, missing_capabilities)
from research_chains.query_oracles import primitive_query_utilities, query_payload
from research_chains.provenance import write_artifact_with_provenance
from envs.external.runtime import maybe_reexec_in_external_runtime

PROTOCOL_VERSION='external_query_transfer_v2'


def _blocked(reason_code, required=(), detail=None):
    row={'status':'BLOCKED_NA','reason_code':str(reason_code),'capabilities_required':list(required)}
    if detail: row['detail']=str(detail)
    return row


def _method_cost(**kwargs):
    keys=('environment_steps','clone_restores','single_agent_interventions','coalition_interventions',
          'model_forward_passes','message_interventions','oracle_calls')
    return {key:int(kwargs.get(key,0)) for key in keys}


def _cost_total(cost):
    return int(sum(int(v) for v in cost.values()))


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
        env.restore_state(snapshot); _,rewards,_,_=env.step(actions)
        receipt=trusted_execution_receipt(env)
        observed=tuple(int(receipt[a]) for a in range(int(env.n_agents))) if not isinstance(receipt,dict) else tuple(int(receipt[a]) for a in range(int(env.n_agents)))
        if any(observed[agent]!=actions[agent] for agent in candidates):
            raise RuntimeError('coalition intervention was not honored by the trusted execution receipt')
        values[active]=float(rewards[outcome])
    env.restore_state(snapshot); return values


def _verified_policy_baseline(env, snapshot):
    """Return frozen-policy actions at ``snapshot`` after receipt verification.

    The execution receipt is evidence that the policy-selected actions were
    honored at the same cloned state.  It must never be used as a substitute
    for evaluating the policy itself, because a previous receipt belongs to a
    different state/action decision.
    """
    requested=[int(env.fixed_continuation_policy(i)) for i in range(int(env.n_agents))]
    if len(requested)!=int(env.n_agents):
        raise RuntimeError('fixed continuation policy returned the wrong action width')
    env.restore_state(snapshot)
    env.step(requested)
    receipt=trusted_execution_receipt(env)
    observed=(
        [int(receipt[i]) for i in range(int(env.n_agents))]
        if isinstance(receipt,dict) else [int(a) for a in receipt]
    )
    env.restore_state(snapshot)
    if len(observed)!=int(env.n_agents):
        raise RuntimeError('trusted policy-baseline receipt has the wrong width')
    mismatches=[i for i,(want,got) in enumerate(zip(requested,observed)) if int(want)!=int(got)]
    if mismatches:
        raise RuntimeError(
            'frozen/current-policy baseline was not honored at the cloned state; '
            f'mismatched_agents={mismatches}'
        )
    return requested, observed


def _state_panel(env,outcome,candidates,k,context=None,information_budget=None):
    context=context or ExternalQueryContext()
    snapshot=env.clone_state()
    state_hash=hashlib.sha256(repr(snapshot).encode()).hexdigest()
    baseline, baseline_receipt = _verified_policy_baseline(env, snapshot)
    noop_provider=getattr(env,'query_noop_action',None); noop_supported=callable(noop_provider)
    rows=[]; base_idx=[]; noop_idx=[]; kept=[]; honored_actions=[]; single_calls=0
    for agent in candidates:
        acts=_valid_actions(env,agent); oracle=CloneStateJointOracle(env,snapshot=snapshot,outcome_agent=outcome,baseline_actions=baseline)
        records=oracle.enumerate([agent],[acts],fail_on_execution_mismatch=False)
        single_calls+=len(records)
        honored=[(int(r.assignment[0]),float(r.reward)) for r in records if r.execution_verified]
        if len(honored)<2: continue
        ha=tuple(a for a,_ in honored); kept.append(int(agent)); honored_actions.append(list(ha)); rows.append(np.asarray([v for _,v in honored],float))
        base_action=int(baseline[agent])
        if base_action not in ha: raise RuntimeError(f'baseline action was not honored for agent={agent}')
        base_idx.append(ha.index(base_action))
        if noop_supported:
            noop_action=int(noop_provider(agent))
            if noop_action not in ha: raise RuntimeError(f'explicit noop was not honored for agent={agent}')
            noop_idx.append(ha.index(noop_action))
    candidates=kept
    if len(candidates)<max(2,int(k)):
        raise RuntimeError('insufficient agents with at least two honored intervention actions')
    primitive=response_primitives(rows,base_idx,noop_idx if noop_supported else None)
    noop_actions=[int(noop_provider(agent)) for agent in candidates] if noop_supported else None
    coal=_coalition_values(env,snapshot,outcome,candidates,baseline,noop_actions) if noop_supported and len(candidates)<=6 else None
    shap=exact_noop_shapley(coal,len(candidates)) if coal is not None else None
    scores={**primitive,'RelationFeatureNorm':_relation_feature_scores(env,outcome,candidates)}
    if shap is not None:scores['CoalitionShapley_noop']=np.abs(shap)
    queries=primitive_query_utilities(primitive,noop_supported=noop_supported,shapley=shap)
    provider_metadata={}; provider_costs={}; provider_errors={}
    provider_specs=(
        ('AttentionWeights',context.attention,'relation_attention',None,()),
        ('MessageDeletion',context.communication,'deletion_effect','communication_deletion',()),
        ('CommunicationDelay',context.communication,'delay_effect','communication_delay',((1,2,4),)),
        ('VoI',context.information,'information_value','information_value',()),
        ('CausalContextAttribution',context.causal,'causal_contribution','causal_contribution',()),
    )
    for method,provider,fn_name,query,extra in provider_specs:
        if provider is None: continue
        try:
            result=getattr(provider,fn_name)(snapshot,int(outcome),tuple(candidates),*extra)
            values=np.asarray(result.values,float)
            if values.shape!=(len(candidates),): raise ValueError('provider result width mismatch')
            scores[method]=values; provider_metadata[method]=dict(result.metadata); provider_costs[method]=dict(result.cost)
            if query is not None: queries[query]=values
        except Exception as exc:
            provider_errors[method]=f'{type(exc).__name__}: {exc}'

    common_response_cost=_method_cost(environment_steps=single_calls,clone_restores=single_calls,
        single_agent_interventions=single_calls,oracle_calls=single_calls)
    method_cost={name:dict(common_response_cost) for name in primitive}
    method_cost['RelationFeatureNorm']=_method_cost(model_forward_passes=len(candidates))
    if shap is not None:
        ncoal=2**len(candidates); method_cost['CoalitionShapley_noop']=_method_cost(
            environment_steps=ncoal,clone_restores=ncoal,coalition_interventions=ncoal,oracle_calls=ncoal)
    for name,cost in provider_costs.items():
        method_cost[name]=_method_cost(**cost)
    matrix={}
    for method,score in scores.items():
        matrix[method]={}
        for query,utility in queries.items():
            rr=query_regret(score,utility,k); nonconstant=len(score)>=2 and not np.allclose(score,score[0]) and not np.allclose(utility,utility[0])
            rho=spearmanr(score,utility).statistic if nonconstant else 0.0
            tau=kendalltau(score,utility).statistic if nonconstant else 0.0
            full={**rr,'R_m_to_q':float(rr['regret']),'spearman':float(rho) if np.isfinite(rho) else 0.0,'kendall':float(tau) if np.isfinite(tau) else 0.0}
            cost=method_cost[method]; matched=(full if information_budget is None or _cost_total(cost)<=int(information_budget)
                else _blocked('METHOD_EXCEEDS_MATCHED_INFORMATION_BUDGET',detail=f"cost={_cost_total(cost)} budget={information_budget}"))
            mspec=METHOD_SPECS[method]; qspec=QUERY_SPECS[query]
            required=tuple(dict.fromkeys(mspec.required_capabilities+qspec.required_capabilities))
            matrix[method][query]={**full,'method_id':method,'method_version':'v1',
                'implementation_scope':mspec.implementation_scope,'query_id':query,
                'query_semantics':qspec.semantic_target,'capabilities_required':list(required),
                'capabilities_satisfied':list(required),'state_hash':state_hash,
                'reference_pi':qspec.reference_semantics.get('pi'),
                'reference_q':qspec.reference_semantics.get('q'),
                'full_information':full,'matched_budget':matched,
                'information_budget':cost,'information_budget_total':_cost_total(cost)}
    env.restore_state(snapshot)
    available={'clone_restore':True,'valid_action_mask':True,'intervention_authority':True,
        'trusted_execution_receipt':True,'current_policy_action':True,'response_panel':True,
        'relation_features':True,'explicit_noop_semantics':bool(noop_supported),
        'complete_noop_coalition_table':shap is not None,**context.capability_status()}
    blocked_queries={}
    for name,spec in QUERY_SPECS.items():
        if name in queries: continue
        missing=missing_capabilities(spec.required_capabilities,available)
        reason=BLOCKER_REASON.get(missing[0],'QUERY_PROVIDER_FAILED') if missing else 'QUERY_PROVIDER_FAILED'
        blocked_queries[name]=_blocked(reason,spec.required_capabilities,provider_errors)
    blocked_methods={}
    for name,spec in METHOD_SPECS.items():
        if name in scores: continue
        missing=missing_capabilities(spec.required_capabilities,available)
        reason=BLOCKER_REASON.get(missing[0],'METHOD_PROVIDER_FAILED') if missing else 'METHOD_PROVIDER_FAILED'
        blocked_methods[name]=_blocked(reason,spec.required_capabilities,provider_errors.get(name))
    methods={}
    for name,score in scores.items():
        spec=METHOD_SPECS[name]
        methods[name]={'scores':np.asarray(score).tolist(),'method_id':name,'method_version':'v1',
            'implementation_scope':spec.implementation_scope,'required_capabilities':list(spec.required_capabilities),
            'provenance':dict(spec.provenance),'information_budget_type':spec.information_budget_type,
            'information_budget':method_cost[name],'derived_from':spec.derived_from,'transform':spec.transform,
            'provider_metadata':provider_metadata.get(name)}
    return {'status':'OK','state_hash':state_hash,'candidates':list(candidates),'honored_action_sets':honored_actions,
        'outcome_agent':int(outcome),'noop_semantics_available':bool(noop_supported),
        'policy_baseline_requested':list(map(int,baseline)),'policy_baseline_receipt':list(map(int,baseline_receipt)),
        'policy_baseline_verified':True,
        'D_semantics':dict(QUERY_SPECS['signed_policy_effect'].reference_semantics),
        'methods':methods,'queries':{q:query_payload(q,u) for q,u in queries.items()},
        'blocked_methods':blocked_methods,'blocked_queries':blocked_queries,
        'benchmark_modes':['full_information_transfer','matched_budget_transfer'],
        'matched_information_budget':information_budget,'primary_endpoint':'R_m_to_q','matrix':matrix}


def run(key='rware',seed=3001,n_states=8,warmup_steps=3,k=2,n_candidates=4,env=None,
        context=None,information_budget=None):
    if env is None:
        from envs.external.registry import build_environment
        env=build_environment(key,seed=int(seed))
    env.reset(seed=int(seed)); capability=audit_environment(key,env=env,max_cells=64)
    if not capability['claim_readiness']['QUERY']['ready']:
        return {
            'protocol_version':PROTOCOL_VERSION,
            'evidence_class':'EXTERNAL_COMMON_STATE_INTERVENTION_TRANSFER',
            'status':'BLOCKED', 'adapter':key, 'seed':int(seed),
            'n_states':int(n_states), 'executable_states':0, 'k':int(k),
            'capability_runtime':capability,
            'blocker':'QUERY capability gate failed: trusted execution authority is unavailable',
            'blocked_methods':{name:_blocked('ADAPTER_QUERY_CAPABILITY_GATE_FAILED',spec.required_capabilities)
                for name,spec in METHOD_SPECS.items()},
            'blocked_queries':{name:_blocked('ADAPTER_QUERY_CAPABILITY_GATE_FAILED',spec.required_capabilities)
                for name,spec in QUERY_SPECS.items()},
            'states':[], 'aggregate_transfer_matrix':{},
        }
    outcome=0; candidates=[a for a in range(int(env.n_agents)) if a!=outcome][:int(n_candidates)]
    state_rows=[]
    for state in range(int(n_states)):
        if state:
            for step in range(int(warmup_steps)):
                actions=[]
                for i in range(int(env.n_agents)):
                    valid=_valid_actions(env,i); actions.append(int(valid[(state+step+i)%len(valid)]))
                env.step(actions)
        try: state_rows.append(_state_panel(env,outcome,candidates,min(int(k),len(candidates)),context,information_budget))
        except RuntimeError as exc: state_rows.append({'status':'BLOCKED','reason':str(exc),'matrix':{}})
    methods=sorted({m for row in state_rows for m in row['matrix']}); queries=sorted({q for row in state_rows for x in row['matrix'].values() for q in x})
    aggregate={}
    for m in methods:
        aggregate[m]={}
        for q in queries:
            vals=[row['matrix'][m][q] for row in state_rows if m in row['matrix'] and q in row['matrix'][m]]
            aggregate[m][q]=None if not vals else {'R_m_to_q':float(np.mean([v['R_m_to_q'] for v in vals])),'query_regret':float(np.mean([v['regret'] for v in vals])),'topk_exact':float(np.mean([v['topk_exact'] for v in vals])),'jaccard':float(np.mean([v['jaccard'] for v in vals])),'ndcg':float(np.mean([v['ndcg'] for v in vals])),'spearman':float(np.mean([v['spearman'] for v in vals])),'kendall':float(np.mean([v['kendall'] for v in vals]))}
    blocked={name:_blocked('NO_EXECUTABLE_STATE_WITH_REQUIRED_METHOD_CAPABILITIES',spec.required_capabilities)
        for name,spec in METHOD_SPECS.items() if name not in methods}
    ok=sum(row['status']=='OK' for row in state_rows)
    blocked_queries={name:_blocked('NO_EXECUTABLE_STATE_WITH_REQUIRED_QUERY_SEMANTICS',spec.required_capabilities)
        for name,spec in QUERY_SPECS.items()
        if not any(name in row.get('queries',{}) for row in state_rows)}
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'EXTERNAL_COMMON_STATE_INTERVENTION_TRANSFER',
        'benchmark_readiness':'EXTERNAL_PRIMITIVE_FRAMEWORK_READY_FULL_RELATIONAL_QUERY_BENCHMARK_NOT_READY',
        'status':'OK' if ok else 'BLOCKED','adapter':key,'seed':int(seed),'n_states':int(n_states),
        'executable_states':int(ok),'k':int(k),'primary_endpoint':'R_m_to_q',
        'secondary_endpoints':['topk_exact','jaccard','ndcg','spearman','kendall'],
        'common_state_contract':'all methods derive from the same frozen state and intervention panel',
        'matched_information_budget':information_budget,'capability_runtime':capability,
        'method_specs':{k:vars(v) for k,v in METHOD_SPECS.items()},
        'query_specs':{k:vars(v) for k,v in QUERY_SPECS.items()},
        'blocked_methods':blocked,'blocked_queries':blocked_queries,'states':state_rows,
        'aggregate_transfer_matrix':aggregate}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--adapter',choices=['rware','flatland','cyborg','cityflow'],default='rware'); p.add_argument('--seed',type=int,default=3001); p.add_argument('--n-states',type=int,default=8); p.add_argument('--warmup-steps',type=int,default=3); p.add_argument('--k',type=int,default=2); p.add_argument('--n-candidates',type=int,default=4); p.add_argument('--information-budget',type=int,default=None); p.add_argument('--out',default='research/external/query_transfer.json'); a=p.parse_args(argv)
    maybe_reexec_in_external_runtime(require_ready=True)
    payload=run(a.adapter,a.seed,a.n_states,a.warmup_steps,a.k,a.n_candidates,
        information_budget=a.information_budget)
    write_artifact_with_provenance(Path(a.out),payload,protocol={
        'protocol_version':PROTOCOL_VERSION,'adapter':a.adapter,'n_states':a.n_states,
        'warmup_steps':a.warmup_steps,'k':a.k,'n_candidates':a.n_candidates,
        'information_budget':a.information_budget},seed=a.seed,
        evidence_class=payload['evidence_class'],chain='QUERY')
    print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
