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

PROTOCOL_VERSION='external_query_transfer_v4_split_evaluability_and_matched_budget'
PROTOCOL_VERSION_CONTINUATION='external_query_transfer_v5_continuation_return_frozen_policy'


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


REGRET_METRICS=('R_m_to_q','regret','spearman','kendall')
RANKING_METRICS=('topk_exact','jaccard','ndcg')


# Two separate aggregate matrices.  The previous code advertised
# benchmark_modes = [full_information_transfer, matched_budget_transfer] but
# only ever aggregated the top-level (full-information) values, so the
# matched-budget mode existed per cell and nowhere in the reported matrix.
# Each metric now also carries its OWN denominator, because the regret and
# ranking endpoints are gated by different conditions (see
# _query_discriminativeness).


def _cell_payload(cell, mode):
    if mode=='full':
        payload=cell.get('full_information')
        return payload if isinstance(payload,dict) else cell
    payload=cell.get('matched_budget')
    if not isinstance(payload,dict) or payload.get('status')=='BLOCKED_NA':
        return None
    return payload

def aggregate_transfer_matrix(state_rows, methods, queries, mode):
    out={}; counts={'regret_cells':0,'ranking_cells':0,'budget_blocked_cells':0,'raw_cells':0}
    for m in methods:
        out[m]={}
        for q in queries:
            raw=[row['matrix'][m][q] for row in state_rows
                 if m in row.get('matrix',{}) and q in row['matrix'][m]]
            counts['raw_cells']+=len(raw)
            cells=[]
            for cell in raw:
                payload=_cell_payload(cell,mode)
                if payload is None:
                    counts['budget_blocked_cells']+=1
                    continue
                cells.append((cell,payload))
            reg=[pl for c,pl in cells if bool(c.get('regret_evaluable',False))]
            rnk=[pl for c,pl in cells if bool(c.get('ranking_evaluable',False))]
            counts['regret_cells']+=len(reg); counts['ranking_cells']+=len(rnk)
            if not reg and not rnk:
                out[m][q]=None
                continue
            entry={'raw_state_count':len(raw),
                'budget_blocked_state_count':len(raw)-len(cells),
                'regret_evaluable_state_count':len(reg),
                'ranking_evaluable_state_count':len(rnk),
                'degenerate_state_count':len(cells)-len(reg)}
            for name in REGRET_METRICS:
                label='query_regret' if name=='regret' else name
                entry[label]=float(np.mean([pl[name] for pl in reg])) if reg else None
            for name in RANKING_METRICS:
                entry[name]=float(np.mean([pl[name] for pl in rnk])) if rnk else None
            out[m][q]=entry
    return out,counts


def _query_discriminativeness(utility, k, tol=1e-12):
    """Return the scientific non-degeneracy diagnostics for one query target.

    Two DIFFERENT degeneracies were previously collapsed into one flag, which
    silently dropped the primary endpoint whenever a secondary one was
    undefined:

    * the target utility being constant kills EVERY endpoint, regret included;
    * a tie at the k/(k+1) boundary kills only the Top-k comparison.  The
      regret `R_m_to_q` is perfectly well defined on a tied target.

    Gating `R_m_to_q` on the Top-k boundary is a selection bias -- it removes
    exactly the states where ranking is hard while keeping the easy ones.  So
    the two conditions are now reported separately:

        regret_evaluable  <=> osc(T_q) > tol
        ranking_evaluable <=> regret_evaluable and TopK boundary gap > tol

    `status` and `reason` keep their original values so existing readers and
    artifacts stay comparable; `scientific_evaluable` is retained as the LEGACY
    STRICT flag (identical to `ranking_evaluable`) and must not be used to gate
    the primary endpoint.
    """
    arr=np.asarray(utility,dtype=float).reshape(-1)
    def _out(status, reason, oscillation, gap, regret_ok, ranking_ok):
        return {'status':status,'reason':reason,
            'utility_oscillation':oscillation,'topk_gap':gap,
            'regret_evaluable':bool(regret_ok),'ranking_evaluable':bool(ranking_ok),
            'scientific_evaluable':bool(ranking_ok)}
    if arr.size < 2 or not np.all(np.isfinite(arr)):
        return _out('EVALUABLE_DEGENERATE','QUERY_TARGET_TOO_SMALL_OR_NONFINITE',0.0,None,False,False)
    oscillation=float(np.max(arr)-np.min(arr))
    if oscillation <= float(tol):
        # constant target: no endpoint is defined
        return _out('EVALUABLE_DEGENERATE','QUERY_TARGET_CONSTANT',oscillation,0.0,False,False)
    kk=int(k)
    if not 0 < kk < arr.size:
        # regret is still defined; only the Top-k comparison is not
        return _out('EVALUABLE_DEGENERATE','TOPK_BOUNDARY_UNDEFINED',oscillation,None,True,False)
    order=np.argsort(-arr,kind='mergesort')
    gap=float(arr[order[kk-1]]-arr[order[kk]])
    if gap <= float(tol):
        return _out('EVALUABLE_DEGENERATE','TOPK_BOUNDARY_TIED',oscillation,gap,True,False)
    return _out('EVALUABLE',None,oscillation,gap,True,True)


def _valid_actions(env,a):
    mask=np.asarray(env.valid_action_mask(int(a)),bool).reshape(-1); out=tuple(int(x) for x in np.flatnonzero(mask))
    if not out: raise RuntimeError(f'no valid action agent={a}')
    return out


CONTINUATION_POLICIES=('noop','forward')


def _frozen_continuation(kind):
    """Return rho for Q^(h,rho).  Every choice here is DETERMINISTIC IN THE STATE
    and carries no hidden counter, so the estimand does not depend on the order in
    which the oracle enumerates interventions.

    ``noop``    -- env.fixed_continuation_policy, the same policy that defines the
                   baseline.  On the RWARE adapter this is NOOP for every agent, so
                   the continuation contributes exactly zero and Q^(h,rho) collapses
                   back onto the one-step reward.  Kept as the compatible default.
    ``forward`` -- each agent takes its first non-idle valid action.  A declared
                   reference policy that actually moves; it is NOT task-competent and
                   must never be reported as a policy-performance result.
    """
    kind=str(kind)
    if kind=='noop':
        return lambda e:[int(e.fixed_continuation_policy(i)) for i in range(int(e.n_agents))]
    if kind=='forward':
        def _forward(e):
            out=[]
            for i in range(int(e.n_agents)):
                valid=_valid_actions(e,i)
                out.append(int(valid[1 if len(valid)>1 else 0]))
            return out
        return _forward
    raise ValueError(f'unknown continuation policy {kind!r}; expected one of {CONTINUATION_POLICIES}')


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
        # Ceteris paribus requires the WHOLE requested joint action to be executed.
        # Checking only the candidate coordinates lets an adapter honour the
        # coalition while overriding some other agent's baseline action, in which
        # case the value recorded is not the value of the requested coalition.
        if any(int(observed[agent])!=int(actions[agent]) for agent in range(int(env.n_agents))):
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


def _state_panel(env,outcome,candidates,k,context=None,information_budget=None,expected_candidates=None,
                 horizon=1,discount=1.0,continuation_policy='noop'):
    context=context or ExternalQueryContext()
    snapshot=env.clone_state()
    state_hash=hashlib.sha256(repr(snapshot).encode()).hexdigest()
    baseline, baseline_receipt = _verified_policy_baseline(env, snapshot)
    noop_provider=getattr(env,'query_noop_action',None); noop_supported=callable(noop_provider)
    rows=[]; base_idx=[]; noop_idx=[]; kept=[]; honored_actions=[]; single_calls=0
    for agent in candidates:
        acts=_valid_actions(env,agent)
        _kw={}
        if int(horizon)>1:
            # rho in Q^(h,rho) MUST be explicit and frozen.  Reuse the very policy that
            # defines the baseline, so the continuation and the baseline are one object.
            _kw=dict(horizon=int(horizon),discount=float(discount),
                continuation_policy=_frozen_continuation(continuation_policy))
        oracle=CloneStateJointOracle(env,snapshot=snapshot,outcome_agent=outcome,
            baseline_actions=baseline,**_kw)
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
    if expected_candidates is not None and len(candidates) != int(expected_candidates):
        raise RuntimeError(
            'QUERY_PROTOCOL_DIMENSION_MISMATCH: requested '
            f'{int(expected_candidates)} candidates but only {len(candidates)} had at least two '
            'honored intervention actions'
        )
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

    query_diagnostics={name:_query_discriminativeness(values,k) for name,values in queries.items()}

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
                'cell_status':query_diagnostics[query]['status'],
                'scientific_evaluable':bool(query_diagnostics[query]['scientific_evaluable']),
                'regret_evaluable':bool(query_diagnostics[query]['regret_evaluable']),
                'ranking_evaluable':bool(query_diagnostics[query]['ranking_evaluable']),
                'degeneracy_reason':query_diagnostics[query]['reason'],
                'query_utility_oscillation':query_diagnostics[query]['utility_oscillation'],
                'query_topk_gap':query_diagnostics[query]['topk_gap'],
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
        'methods':methods,'queries':{q:{**query_payload(q,u),'diagnostics':query_diagnostics[q]} for q,u in queries.items()},
        'blocked_methods':blocked_methods,'blocked_queries':blocked_queries,
        'effective_n_candidates':int(len(candidates)),
        'query_non_degeneracy_gate':('regret endpoints require utility oscillation > 0; Top-k endpoints additionally require a strict k/(k+1) boundary gap > 0. The two are gated separately so a tied ranking boundary never removes R_m_to_q.'),
        'benchmark_modes':['full_information_transfer','matched_budget_transfer'],
        'matched_information_budget':information_budget,'primary_endpoint':'R_m_to_q','matrix':matrix}


def run(key='rware',seed=3001,n_states=8,warmup_steps=3,k=2,n_candidates=4,env=None,
        context=None,information_budget=None,agent_count=None,horizon=1,discount=1.0,continuation_policy='noop'):
    n_candidates=int(n_candidates); k=int(k)
    if n_candidates < 2:
        raise ValueError('n_candidates must be at least 2 for relational transfer')
    if not 1 <= k < n_candidates:
        raise ValueError('QUERY protocol requires 1 <= k < n_candidates; silent clipping is forbidden')
    required_agents=n_candidates+1  # one outcome agent plus the fixed candidate panel
    if agent_count is not None and int(agent_count) < required_agents:
        raise ValueError(
            f'agent_count={int(agent_count)} cannot provide outcome + {n_candidates} candidates'
        )
    requested_agents=max(required_agents,int(agent_count) if agent_count is not None else 0)
    if env is None:
        from envs.external.registry import build_environment
        env=build_environment(key,seed=int(seed),n_agents=requested_agents)
    env.reset(seed=int(seed))
    actual_agents=int(env.n_agents)
    if actual_agents < requested_agents:
        return {
            'protocol_version':PROTOCOL_VERSION,
            'evidence_class':'EXTERNAL_COMMON_STATE_INTERVENTION_TRANSFER',
            'status':'BLOCKED','scientific_transfer_status':'BLOCKED_PROTOCOL_DIMENSION_MISMATCH',
            'adapter':key,'seed':int(seed),'n_states':int(n_states),'executable_states':0,'k':k,
            'requested_n_candidates':n_candidates,'requested_n_agents':requested_agents,
            'actual_n_agents':actual_agents,'available_n_candidates':max(0,actual_agents-1),
            'blocker':f'adapter constructed {actual_agents} agents but protocol requested {requested_agents}',
            'states':[],'aggregate_transfer_matrix':{},
        }
    capability=audit_environment(key,env=env,max_cells=64)
    base_meta={
        'requested_n_candidates':n_candidates,'requested_n_agents':requested_agents,
        'actual_n_agents':actual_agents,'available_n_candidates':max(0,actual_agents-1),
    }
    if not capability['claim_readiness']['QUERY']['ready']:
        return {
            'protocol_version':PROTOCOL_VERSION,
            'evidence_class':'EXTERNAL_COMMON_STATE_INTERVENTION_TRANSFER',
            'status':'BLOCKED','scientific_transfer_status':'BLOCKED_CAPABILITY',
            'adapter':key,'seed':int(seed),'n_states':int(n_states),'executable_states':0,'k':k,
            **base_meta,'capability_runtime':capability,
            'blocker':'QUERY capability gate failed: trusted execution authority is unavailable',
            'blocked_methods':{name:_blocked('ADAPTER_QUERY_CAPABILITY_GATE_FAILED',spec.required_capabilities)
                for name,spec in METHOD_SPECS.items()},
            'blocked_queries':{name:_blocked('ADAPTER_QUERY_CAPABILITY_GATE_FAILED',spec.required_capabilities)
                for name,spec in QUERY_SPECS.items()},
            'states':[],'aggregate_transfer_matrix':{},
        }
    outcome=0
    candidates=[a for a in range(actual_agents) if a!=outcome][:n_candidates]
    if len(candidates) != n_candidates:
        raise AssertionError('post-construction candidate panel width does not match protocol')
    state_rows=[]
    for state in range(int(n_states)):
        if state:
            for step in range(int(warmup_steps)):
                actions=[]
                for i in range(actual_agents):
                    valid=_valid_actions(env,i); actions.append(int(valid[(state+step+i)%len(valid)]))
                env.step(actions)
        try:
            state_rows.append(_state_panel(
                env,outcome,candidates,k,context,information_budget,
                expected_candidates=n_candidates,horizon=horizon,discount=discount,
                continuation_policy=continuation_policy,
            ))
        except RuntimeError as exc:
            state_rows.append({'status':'BLOCKED','reason':str(exc),'matrix':{},
                'effective_n_candidates':0})
    methods=sorted({m for row in state_rows for m in row.get('matrix',{})})
    queries=sorted({q for row in state_rows for x in row.get('matrix',{}).values() for q in x})
    aggregate,full_counts=aggregate_transfer_matrix(state_rows,methods,queries,'full')
    aggregate_matched,matched_counts=aggregate_transfer_matrix(state_rows,methods,queries,'matched')
    evaluable_cells=int(full_counts['regret_cells'])
    degenerate_cells=int(full_counts['raw_cells']-full_counts['regret_cells'])
    blocked={name:_blocked('NO_EXECUTABLE_STATE_WITH_REQUIRED_METHOD_CAPABILITIES',spec.required_capabilities)
        for name,spec in METHOD_SPECS.items() if name not in methods}
    ok=sum(row.get('status')=='OK' for row in state_rows)
    blocked_queries={name:_blocked('NO_EXECUTABLE_STATE_WITH_REQUIRED_QUERY_SEMANTICS',spec.required_capabilities)
        for name,spec in QUERY_SPECS.items()
        if not any(name in row.get('queries',{}) for row in state_rows)}
    scientific_status=(
        'EVALUABLE' if evaluable_cells else
        ('EVALUABLE_DEGENERATE' if ok else 'BLOCKED')
    )
    return {'protocol_version':PROTOCOL_VERSION,'evidence_class':'EXTERNAL_COMMON_STATE_INTERVENTION_TRANSFER',
        'benchmark_readiness':'EXTERNAL_PRIMITIVE_FRAMEWORK_READY_FULL_RELATIONAL_QUERY_BENCHMARK_NOT_READY',
        'status':'OK' if ok else 'BLOCKED','scientific_transfer_status':scientific_status,
        'adapter':key,'seed':int(seed),'n_states':int(n_states),'executable_states':int(ok),'k':k,
        **base_meta,'effective_candidate_counts':[int(row.get('effective_n_candidates',0)) for row in state_rows],
        'scientifically_evaluable_matrix_cells':int(evaluable_cells),
        'degenerate_matrix_cells_excluded_from_aggregate':int(degenerate_cells),
        'query_non_degeneracy_gate':('regret endpoints require utility oscillation > 0; Top-k endpoints additionally require a strict k/(k+1) boundary gap > 0. The two are gated separately so a tied ranking boundary never removes R_m_to_q.'),
        'primary_endpoint':'R_m_to_q',
        'protocol_version':(PROTOCOL_VERSION if int(horizon)==1 else PROTOCOL_VERSION_CONTINUATION),
        'response_horizon':int(horizon),'response_discount':float(discount),
        'continuation_policy':str(continuation_policy),
        'continuation_policy_definition':(
            'rho for Q^(h,rho). noop = env.fixed_continuation_policy (all-NOOP on RWARE, so the '
            'continuation contributes zero); forward = each agent takes its first non-idle valid '
            'action, a declared reference policy that moves but is NOT task-competent and is '
            'never a policy-performance claim.'),
        'response_estimand':('Q_one_step' if int(horizon)==1
            else f'Q_continuation_h{int(horizon)}_gamma{float(discount):g}'),
        'response_estimand_definition':((
            'Q^(1)_j(a) = r_outcome(s, a_j, a_-j^baseline): the reward of a SINGLE environment '
            'step after a clone-state intervention. This is NOT a continuation return '
            'Q^(h,rho) = E[sum_t gamma^t r_t | do(A_j = a), rho]. The oracle can compute a '
            'continuation return (CloneStateJointOracle(horizon=h, discount=gamma, '
            'continuation_policy=...)), but at horizon=1 this protocol does not, and no '
            'artifact it writes may be read as one.') if int(horizon)==1 else (
            f'Q^(h,rho)_j(a) = sum_t gamma^t r_outcome(s_t) over h={int(horizon)} steps with '
            f'gamma={float(discount):g}. The intervention do(A_j = a) is applied at t=0 ONLY; the '
            'remaining steps roll the frozen continuation policy env.fixed_continuation_policy '
            'forward -- the same policy that defines the baseline -- and stop early on done. '
            'This IS a continuation return and is NOT comparable with any Q_one_step artifact '
            'written under protocol v4.')),
        'execution_semantics':'full_joint',
        'execution_semantics_definition':(
            'A cell counts as executed only when the ENTIRE requested joint action vector was '
            'executed, intervened and frozen-baseline coordinates alike. Source-only agreement '
            'is reported separately and does not establish F(a_S, a_baseline_-S).'),
        'secondary_endpoints':['topk_exact','jaccard','ndcg','spearman','kendall'],
        'common_state_contract':'all methods derive from the same frozen state and intervention panel',
        'matched_information_budget':information_budget,'capability_runtime':capability,
        'method_specs':{k:vars(v) for k,v in METHOD_SPECS.items()},
        'query_specs':{k:vars(v) for k,v in QUERY_SPECS.items()},
        'blocked_methods':blocked,'blocked_queries':blocked_queries,'states':state_rows,
        'benchmark_modes_implemented':{
            'full_information_transfer':'aggregate_transfer_matrix',
            'matched_budget_transfer':'aggregate_transfer_matrix_matched_budget'},
        'aggregate_denominators_full_information':full_counts,
        'aggregate_denominators_matched_budget':matched_counts,
        'aggregate_transfer_matrix':aggregate,
        'aggregate_transfer_matrix_matched_budget':aggregate_matched}


def main(argv=None):
    p=argparse.ArgumentParser()
    p.add_argument('--adapter',choices=['rware','flatland','cyborg','cityflow'],default='rware')
    p.add_argument('--seed',type=int,default=3001)
    p.add_argument('--n-states',type=int,default=8)
    p.add_argument('--warmup-steps',type=int,default=3)
    p.add_argument('--k',type=int,default=2)
    p.add_argument('--n-candidates',type=int,default=4)
    p.add_argument('--agent-count',type=int,default=None,
        help='optional total environment population; must be >= n_candidates + 1')
    p.add_argument('--information-budget',type=int,default=None)
    p.add_argument('--horizon',type=int,default=1,
        help='continuation-return horizon h; h=1 keeps the one-step estimand of protocol v4')
    p.add_argument('--discount',type=float,default=1.0,help='gamma, only meaningful for h>1')
    p.add_argument('--continuation-policy',choices=CONTINUATION_POLICIES,default='noop',
        help='rho for Q^(h,rho); only meaningful for h>1')
    p.add_argument('--out',default='research/external/query_transfer.json')
    a=p.parse_args(argv)
    maybe_reexec_in_external_runtime(require_ready=True)
    payload=run(a.adapter,a.seed,a.n_states,a.warmup_steps,a.k,a.n_candidates,
        information_budget=a.information_budget,agent_count=a.agent_count,
        horizon=a.horizon,discount=a.discount,continuation_policy=a.continuation_policy)
    write_artifact_with_provenance(Path(a.out),payload,protocol={
        'protocol_version':(PROTOCOL_VERSION if int(a.horizon)==1 else PROTOCOL_VERSION_CONTINUATION),'adapter':a.adapter,'n_states':a.n_states,
        'warmup_steps':a.warmup_steps,'k':a.k,'n_candidates':a.n_candidates,
        'agent_count':a.agent_count,'information_budget':a.information_budget,
        'horizon':a.horizon,'discount':a.discount,
        'continuation_policy':a.continuation_policy},seed=a.seed,
        evidence_class=payload['evidence_class'],chain='QUERY')
    print(json.dumps(payload,indent=2)); return 0

if __name__=='__main__': raise SystemExit(main())
