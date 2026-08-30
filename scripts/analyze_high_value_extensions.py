"""Aggregate extension screens into a promote/continue/kill decision matrix."""
from __future__ import annotations
import argparse,json,glob,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
import numpy as np
from research_chains.provenance import atomic_json

def _load(root,name):
    out=[]
    for path in sorted((Path(root)/name).glob('seed*.json')):
        try:
            with open(path, 'r', encoding='utf-8') as handle:
                out.append(json.load(handle))
        except Exception as exc:
            raise RuntimeError(
                f"malformed experiment artifact for lab={name}: {path}: "
                f"{type(exc).__name__}: {exc}"
            ) from exc
    return out

def _mean(rows,fn):
    vals=[fn(r) for r in rows]; vals=[float(v) for v in vals if v is not None and np.isfinite(float(v))]; return float(np.mean(vals)) if vals else None

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--root',default='research/high_value_extensions/runs'); p.add_argument('--out',default='research/high_value_extensions/DECISION_MATRIX.json'); p.add_argument('--min-promote-seeds',type=int,default=5); p.add_argument('--max-promote-fallback',type=float,default=.80); a=p.parse_args(argv); root=Path(a.root)
    M=_load(root,'master'); FD=_load(root,'functional_design'); FA=_load(root,'functional_allocation'); FS=_load(root,'functional_stopping'); D=_load(root,'d6'); Q=_load(root,'query'); S=_load(root,'structural'); DY=_load(root,'dynamic'); FBH=_load(root,'foundation_bh'); FRP=_load(root,'foundation_rp'); FREF=_load(root,'foundation_reference'); FQ=_load(root,'foundation_query')
    decisions={}
    if M:
        ru=max(max(r['reference_uncertainty']['worst_violation'].values()) for r in M); mt=max(r['master_transfer']['worst_violation'] for r in M)
        largest='256'; passive=_mean(M,lambda r:r['active_acquisition']['passive'][largest]['kernel_tv']['mean']); randomized=_mean(M,lambda r:r.get('active_acquisition',{}).get('randomized',{}).get(largest,{}).get('kernel_tv',{}).get('mean')); targeted=_mean(M,lambda r:r['active_acquisition']['targeted'][largest]['kernel_tv']['mean']); uncertainty=_mean(M,lambda r:r.get('active_acquisition',{}).get('uncertainty_targeted',{}).get(largest,{}).get('kernel_tv',{}).get('mean')); cal=_mean(M,lambda r:r.get('heldout_calibration',{}).get('uncertainty_targeted',r.get('heldout_calibration',{}).get('targeted',{})).get(largest,{}).get('heldout_coverage')); safe=_mean(M,lambda r:r['cascade']['safe_rate']); fallback=_mean(M,lambda r:r['cascade']['fallback_rate'])
        ratio=targeted/passive if passive else None; targeted_randomized_ratio=targeted/randomized if randomized else None; uncertainty_passive_ratio=uncertainty/passive if passive and uncertainty is not None else None; uncertainty_randomized_ratio=uncertainty/randomized if randomized and uncertainty is not None else None; enough=len(M)>=int(a.min_promote_seeds); deterministic_ok=ru<=1e-8 and mt<=1e-8; utility_nonvacuous=(fallback is not None and fallback<=float(a.max_promote_fallback)); acquisition_gain=any(x is not None and x<1.0 for x in (ratio,uncertainty_passive_ratio)); calibration_ok=(cal is not None and cal>=0.90); safe_ok=(safe is not None and safe>=1.0-1e-12)
        if not deterministic_ok: status='FIX'
        elif not enough: status='CONTINUE_MORE_SEEDS'
        elif acquisition_gain and calibration_ok and safe_ok and utility_nonvacuous: status='PROMOTE'
        elif acquisition_gain and calibration_ok and safe_ok: status='PROMOTE_CORE_CONTINUE_UTILITY'
        else: status='CONTINUE'
        decisions['MASTER']={'status':status,'evidence_seeds':len(M),'min_promote_seeds':int(a.min_promote_seeds),'promotion_eligible':bool(enough),'RU_worst_violation':ru,'MASTER_worst_violation':mt,'targeted_vs_passive_TV_ratio':ratio,'targeted_vs_randomized_TV_ratio':targeted_randomized_ratio,'uncertainty_targeted_vs_passive_TV_ratio':uncertainty_passive_ratio,'uncertainty_targeted_vs_randomized_TV_ratio':uncertainty_randomized_ratio,'targeted_semantics':'balanced least-observed source-action allocation; not uncertainty-adaptive','uncertainty_targeted_semantics':'posterior row-uncertainty adaptive allocation','heldout_calibration_coverage':cal,'cascade_safe_rate':safe,'cascade_fallback_rate':fallback,'max_promote_fallback':float(a.max_promote_fallback),'utility_nonvacuous':bool(utility_nonvacuous),'cascade_frontier_available':all(bool(r.get('cascade',{}).get('frontier')) for r in M),'box_gamma_mean_tightening':_mean(M,lambda r:r.get('box_gamma',{}).get('mean_tightening')),'box_gamma_strict_fraction':_mean(M,lambda r:r.get('box_gamma',{}).get('strict_tightening_fraction')),'probability_lift_good_event_false_count':sum(r.get('probability_lift',{}).get('false_certificate_on_good_event_count',0) for r in M),'RU2_sharpness_reproduced':all(r.get('reference_uncertainty',{}).get('RU2_factor_two_sharpness',{}).get('sharpness_reproduced',False) for r in M),'next_gate':'external reference-identification + calibrated learned intervals; practical promotion also requires non-vacuous fallback at declared tolerance'}
    if FD or FA or FS:
        reversal=any(r['explicit_covariance_reversal_search']['found'] for r in FD) if FD else False
        c_ratio=_mean(FD,lambda r:r['by_geometry']['random']['C_full_vs_diag_mse_ratio']) if FD else None; d_ratio=_mean(FD,lambda r:r['by_geometry']['random']['D_full_vs_diag_mse_ratio']) if FD else None
        stop_c=_mean(FS,lambda r:r['by_allocation']['C_topk_targeted']['N_topk']/max(r['by_allocation']['uniform']['N_topk'],1)) if FS else None; stop_d=_mean(FS,lambda r:r['by_allocation']['D_targeted']['N_Dsign']/max(r['by_allocation']['uniform']['N_Dsign'],1)) if FS else None
        false_ext=max([r['by_allocation'][m].get('extrema_false_certificate_rate') or 0.0 for r in FS for m in ('uniform','D_targeted','C_extremal','C_topk_targeted')],default=None)
        false_top=max([r['by_allocation'][m].get('topk_false_certificate_rate') or 0.0 for r in FS for m in ('uniform','D_targeted','C_extremal','C_topk_targeted')],default=None)
        false_d=max([r['by_allocation'][m].get('Dsign_false_certificate_rate') or 0.0 for r in FS for m in ('uniform','D_targeted','C_extremal','C_topk_targeted')],default=None)
        allocation_latest={}
        if FA:
            common=sorted(set.intersection(*[set(r['by_budget'].keys()) for r in FA]),key=lambda x:int(x)) if FA else []
            for b in common:
                allocation_latest[b]={'C_mae_winners':[r['endpoint_winners'][b]['C_mae'] for r in FA],'C_topk_winners':[r['endpoint_winners'][b]['C_topk_exact'] for r in FA],'D_mae_winners':[r['endpoint_winners'][b]['D_mae'] for r in FA],'D_sign_winners':[r['endpoint_winners'][b]['D_sign_accuracy'] for r in FA]}
        false_max=max([x for x in (false_ext,false_top,false_d) if x is not None],default=0.0)
        decisions['FUNCTIONAL']={'status':'FIX' if false_max>0 else 'CONTINUE','covariance_reversal_found':reversal,'C_full_vs_diag_mse_ratio':c_ratio,'D_full_vs_diag_mse_ratio':d_ratio,'C_targeted_stopping_ratio':stop_c,'D_targeted_stopping_ratio':stop_d,'matched_budget_winners':allocation_latest,'sequential_false_certificate_rates':{'extrema_max':false_ext,'topk_max':false_top,'Dsign_max':false_d},'next_gate':'run disjoint-seed fixed-panel confirmatory; promote acquisition only if matched-budget endpoint gains replicate'}
    if D:
        theorem=max(max(r['worst_candidate_violations']['worst'],r['worst_candidate_violations']['decision']) for r in D); sur=max(r['sharpness']['best_surrogate_ratio'] for r in D); dec=max(r['sharpness']['best_decision_ratio'] for r in D)
        qavg_uniform=_mean(D,lambda r:1.0 if r['worst_candidate_violations']['qavg_uniform']<=1e-10 else 0.0); qavg_dist=_mean(D,lambda r:1.0 if r['worst_candidate_violations']['qavg_distributional']<=1e-10 else 0.0)
        half_safe=_mean(D,lambda r:1.0 if r.get('decision_improvement_candidate',{}).get('worst_violation',float('inf'))<=1e-10 else 0.0); ql1_safe=_mean(D,lambda r:1.0 if r.get('qL1_distributional',{}).get('conditional_worst_violation',float('inf'))<=1e-10 else 0.0)
        adversarial_ratio=max([r.get('decision_improvement_candidate',{}).get('adversarial_search',{}).get('best_ratio_to_worst_rhs',-float('inf')) for r in D],default=None)
        candidate_killed=any(r.get('decision_improvement_candidate',{}).get('adversarial_search',{}).get('candidate_killed',False) for r in D)
        decisions['D6']={'status':'FIX' if theorem>1e-8 else ('HALF_FACTOR_KILLED_CONTINUE_D6' if candidate_killed else 'CONTINUE'),'evidence_seeds':len(D),'current_bound_worst_violation':theorem,'best_surrogate_sharpness_ratio':sur,'best_decision_sharpness_ratio':dec,'half_factor_candidate_seed_safe_fraction':half_safe,'half_factor_adversarial_best_ratio_to_worst_rhs':adversarial_ratio,'half_factor_candidate_killed':bool(candidate_killed),'qavg_uniform_seed_safe_fraction':qavg_uniform,'qavg_distributional_seed_safe_fraction':qavg_dist,'qL1_conditional_seed_safe_fraction':ql1_safe,'next_gate':'promote q-sensitive branch only if exact-hybrid quantities remain violation-free and materially tighter; half-factor candidate must survive targeted adversarial search and still requires proof'}
    if Q:
        native=[]
        for r in Q:
            native.extend([int(v['native_better_than_mean_foreign']) for v in r['native_query_advantage'].values()])
        conflict=_mean(Q,lambda r:r['unique_optimum_conflict']['epsilon_0_common_good_failures'])
        entangled=[]
        for r in Q:
            for v in r.get('native_query_advantage_by_regime',{}).get('cross_query_entangled',{}).values():
                if 'native_better_than_mean_foreign' in v: entangled.append(int(v['native_better_than_mean_foreign']))
        decisions['QUERY']={'status':'CONTINUE','native_advantage_fraction':float(np.mean(native)) if native else None,'entangled_native_advantage_fraction':float(np.mean(entangled)) if entangled else None,'representation_conflict_mean':conflict,'synthetic_alignment_caution':True,'next_gate':'replace synthetic proxies with real MARL/XAI baselines and external challenge environments; require native-query advantage to survive entangled and external regimes'}
    if S:
        votes=[r['kill_gate_decision'] for r in S]; merge_votes=sum(v.startswith('MERGE_INTO_MASTER') for v in votes); cont_votes=votes.count('CONTINUE_APPROXIMATE_STRUCTURAL'); status='CONTINUE' if cont_votes>=max(1,len(votes)//2+1) else ('MERGE_MASTER' if merge_votes>=max(1,len(votes)//2+1) else 'OPEN')
        open_safe=_mean(S,lambda r:1.0 if r.get('open_candidate',{}).get('safe') else 0.0)
        decisions['STRUCTURAL']={'status':status,'evidence_seeds':len(S),'votes':{x:votes.count(x) for x in sorted(set(votes))},'all_optimal_open_candidate_seed_safe_fraction':open_safe,'next_gate':'exact-iff remains closed; keep standalone only if the all-optimal-extension defect is safe, nontrivial, and materially tighter than MASTER'}
    if DY:
        decisions['DYNAMIC']={'status':'FUTURE_CONTINUE','inflated_score_bound_failure_rate':_mean(DY,lambda r:r['score_drift']['inflated_bound_failure_rate']),'old_score_bound_failure_rate':_mean(DY,lambda r:r['score_drift']['old_bound_failure_rate']),'reference_worst_violation':max(r['reference_drift']['worst_violation'] for r in DY),'next_gate':'external temporal drift before any standalone claim'}

    if FBH or FRP or FREF or FQ:
        decisions['FOUNDATION_LINKS']={
            'status':'PASS' if all(r.get('failure_count',0)==0 for r in FBH+FRP+FREF) and all(r.get('overall_status','PASS')=='PASS' for r in FQ) else 'FIX',
            'bh_worst_failure_count':max([r.get('failure_count',0) for r in FBH],default=None),
            'rp_worst_failure_count':max([r.get('failure_count',0) for r in FRP],default=None),
            'reference_worst_failure_count':max([r.get('failure_count',0) for r in FREF],default=None),
            'query_primitive_statuses':[r.get('overall_status') for r in FQ],
        }
    payload={'schema':'high_value_extension_decision_matrix_v2','min_promote_seeds':int(a.min_promote_seeds),'evidence_seed_counts':{'master':len(M),'functional_design':len(FD),'functional_allocation':len(FA),'functional_stopping':len(FS),'d6':len(D),'query':len(Q),'structural':len(S),'dynamic':len(DY)},'root':str(root),'decisions':decisions,'missing_labs':[x for x,rows in [('master',M),('functional_design',FD),('functional_allocation',FA),('functional_stopping',FS),('d6',D),('query',Q),('structural',S),('dynamic',DY),('foundation_bh',FBH),('foundation_rp',FRP),('foundation_reference',FREF),('foundation_query',FQ)] if not rows]}; atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
