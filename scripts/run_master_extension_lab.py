"""MASTER extension lab: active reference ID, uncertainty transfer, composed errors, and cascade utility."""
from __future__ import annotations
import sys
from pathlib import Path as _Path
_ROOT=_Path(__file__).resolve().parents[1]
if str(_ROOT) not in sys.path: sys.path.insert(0,str(_ROOT))

import argparse, json, time
from pathlib import Path
import numpy as np

from research_chains.certificates import exact_optimum, topk_indices, zeta_def
from research_chains.experimental_extensions import (
    cascade_evaluation, empirical_kernel_from_counts, kernel_sup_tv, mix_kernel,
    reference_uncertainty_diagnostics, sample_kernel_counts, box_gamma_diagnostics,
    box_gamma_lean_witness_diagnostics, probability_lift_diagnostics, ru2_factor_two_sharpness_diagnostics,
)
from research_chains.finite_world import FiniteResponseWorld
from research_chains.pairwise import compose_score_error, operational_gamma, pairwise_master_bound
from research_chains.provenance import atomic_json
from research_chains.reference import ConditionalReferenceKernel
from research_chains.support import SupportModel, SupportBracket, projected_span_bracket

PROTOCOL_VERSION="master_extension_lab_v2"


def _world(rng,m=5,coupled=True,residual_scale=0.05):
    sizes=(2,)*m; full=list(np.ndindex(*sizes))
    if coupled:
        omega=[a for a in full if rng.random()<0.72]
        for j in range(m):
            for x in range(2):
                if not any(a[j]==x for a in omega): omega.append(next(a for a in full if a[j]==x))
    else: omega=full
    primitives=tuple(rng.normal(size=2) for _ in range(m))
    residual={a:float(rng.uniform(-residual_scale,residual_scale)) for a in full}
    return FiniteResponseWorld(SupportModel(sizes,tuple(sorted(set(omega))),key="truth"),primitives,residual=residual)


def _truth_kernel(world,source,rng):
    # Full conditional table; not necessarily support-compatible.  This isolates reference-identification questions.
    rows={}; full=list(world.support.full_product())
    for a in range(world.support.action_sizes[source]):
        compatible=[x for x in full if x[source]==a]
        p=rng.dirichlet(np.linspace(0.5,2.0,len(compatible)))
        rows[a]={x:float(v) for x,v in zip(compatible,p)}
    return ConditionalReferenceKernel(source,world.support.action_sizes,rows,key=f"truth_j{source}")


def _identifiability_search(rng,attempts=500):
    """Reproduce RI1/RI2 exactly, then optionally search stronger random variants."""
    support=SupportModel((2,2),tuple(np.ndindex(2,2)),key="ri_exact")
    world=FiniteResponseWorld(support,(np.asarray([0.,0.]),np.asarray([0.,1.])),residual=None)
    flat=ConditionalReferenceKernel(0,(2,2),{
      0:{(0,0):1.0},1:{(1,0):1.0}},key="flat")
    reactive=ConditionalReferenceKernel(0,(2,2),{
      0:{(0,0):1.0},1:{(1,1):1.0}},key="reactive")
    chi_flat=flat.isolation_deviation(world); chi_reactive=reactive.isolation_deviation(world)
    c_flat=float(np.ptp(flat.response_vector(world,true_response=False)))
    c_reactive=float(np.ptp(reactive.response_vector(world,true_response=False)))
    competitor=0.5
    exact={
      "observed_source_actions":[0],"unobserved_source_actions":[1],
      "observed_rows_equal":bool(flat.by_source_action[0]==reactive.by_source_action[0]),
      "unobserved_rows_different":bool(flat.by_source_action[1]!=reactive.by_source_action[1]),
      "chi":[float(chi_flat),float(chi_reactive)],"measured_span":[c_flat,c_reactive],
      "competitor_score":competitor,
      "top1_flat":1 if competitor>c_flat else 0,"top1_reactive":0 if c_reactive>competitor else 1,
      "downstream_top1_changes":bool((1 if competitor>c_flat else 0)!=(0 if c_reactive>competitor else 1)),
    }
    # Also search a random family to ensure the phenomenon is not tied to the exact witness.
    random_found=None
    for attempt in range(int(attempts)):
        w=_world(rng,m=3,coupled=False,residual_scale=0.0); source=0; full=list(w.support.full_product())
        row0=[x for x in full if x[source]==0]; row1=[x for x in full if x[source]==1]
        p0=rng.dirichlet(np.ones(len(row0))); p1a=rng.dirichlet(np.ones(len(row1))); p1b=rng.dirichlet(np.ones(len(row1)))
        k1=ConditionalReferenceKernel(source,w.support.action_sizes,{0:{x:float(p) for x,p in zip(row0,p0)},1:{x:float(p) for x,p in zip(row1,p1a)}},key="k1")
        k2=ConditionalReferenceKernel(source,w.support.action_sizes,{0:{x:float(p) for x,p in zip(row0,p0)},1:{x:float(p) for x,p in zip(row1,p1b)}},key="k2")
        chi1=k1.isolation_deviation(w); chi2=k2.isolation_deviation(w); c1=float(np.ptp(k1.response_vector(w,true_response=False))); c2=float(np.ptp(k2.response_vector(w,true_response=False)))
        if abs(chi1-chi2)>1e-4 or abs(c1-c2)>1e-4:
            random_found={"found":True,"attempt":attempt,"chi_difference":abs(chi1-chi2),"span_difference":abs(c1-c2)}; break
    if random_found is None: random_found={"found":False,"attempts":int(attempts)}
    return {"exact_lean_witness":exact,"random_extension":random_found,
            "found":bool(exact['observed_rows_equal'] and exact['unobserved_rows_different'] and exact['downstream_top1_changes'])}

def run(instances=100,budgets=(16,32,64,128,256),seed=0,tolerance=0.05):
    rng=np.random.default_rng(seed)
    modes=("passive","randomized","targeted","uncertainty_targeted")
    acquisition={mode:{str(b):[] for b in budgets} for mode in modes}
    ru_viol={"pointwise":0.0,"chi":0.0,"score_interval":0.0}; composed_viol=0.0
    topk_records=[]; cascade=[]; support_records=[]; box_records=[]
    for idx in range(int(instances)):
        world=_world(rng,m=5,coupled=True,residual_scale=float(rng.uniform(0,0.08))); m=world.support.n_relations; k=2
        primitive_scores=world.component_spans(); estimated_scores=np.zeros(m); ref_errors=np.zeros(m)
        for j in range(m):
            truth=_truth_kernel(world,j,rng)
            # RU direct perturbation falsification across random mixing strengths.
            estimate=mix_kernel(truth,rng,float(rng.uniform(0,0.5)))
            d=reference_uncertainty_diagnostics(world,truth,estimate)
            ru_viol["pointwise"]=max(ru_viol["pointwise"],d["pointwise_violation"])
            ru_viol["chi"]=max(ru_viol["chi"],d["chi_violation"])
            ru_viol["score_interval"]=max(ru_viol["score_interval"],d["score_interval_violation"])
            estimated_scores[j]=d["measured_span_estimated_kernel"]
            ref_errors[j]=d["reference_error_radius"]
            for mode in modes:
                for budget in budgets:
                    counts,source_counts=sample_kernel_counts(truth,int(budget),rng,mode=mode)
                    khat=empirical_kernel_from_counts(source=j,action_sizes=world.support.action_sizes,counts=counts,smoothing=0.5,key=f"{mode}_{budget}")
                    row=reference_uncertainty_diagnostics(world,truth,khat)
                    acquisition[mode][str(budget)].append({
                        "kernel_tv":row["epsilon_kernel_tv"],"chi_error":row["chi_abs_error"],"score_error":abs(row["measured_span_estimated_kernel"]-row["measured_span_true_kernel"]),"min_source_count":int(np.min(source_counts)),"source_count_imbalance":int(np.max(source_counts)-np.min(source_counts)),
                    })
        # Explicit typed composed budget.  Support interval comes from a valid support bracket.
        truth=set(world.support.omega); full=set(world.support.full_product())
        # Stress projected-support uncertainty deliberately.  A Bernoulli subset
        # of a moderately dense binary support almost always retains both local
        # actions in every projection, producing a vacuous C^- = C^+ audit.
        # Restrict one randomly selected coordinate in the certified inner
        # support while keeping the true support inside the outer bracket.
        focus_j=int(rng.integers(0,m))
        focus_values=tuple(sorted({a[focus_j] for a in truth}))
        keep_value=int(focus_values[int(rng.integers(0,len(focus_values)))])
        lower_items=[a for a in truth if int(a[focus_j])==keep_value]
        if not lower_items:
            raise RuntimeError("failed to construct non-empty inner support bracket")
        upper_items=tuple(sorted(truth|{a for a in full-truth if rng.random()<0.2}))
        bracket=SupportBracket(
            SupportModel(world.support.action_sizes,tuple(sorted(lower_items)),key="lower"),
            SupportModel(world.support.action_sizes,upper_items,key="upper"),
        )
        cminus,cplus=projected_span_bracket(world.primitives,bracket); support_mid=0.5*(cminus+cplus); support_err=0.5*(cplus-cminus)
        # Same-target controlled composition.  The linked support layer is real;
        # reference/stat/model layers are explicit bounded perturbations rather than
        # silently adding unrelated radii to one center.
        stat_err=rng.uniform(0,0.015,size=m); model_err=rng.uniform(0,0.01,size=m)
        after_model=primitive_scores+rng.uniform(-model_err,model_err)
        # Shift from after_model to a support-layer value with a guaranteed bound.
        # The true target is in [cminus,cplus]; add the model displacement explicitly.
        after_support=support_mid+(after_model-primitive_scores)
        support_chain_err=support_err
        ref_shift=rng.uniform(-ref_errors,ref_errors)
        after_reference=after_support+ref_shift
        estimate=after_reference+rng.uniform(-stat_err,stat_err)
        total_error=compose_score_error(stat_err,ref_errors,support_chain_err,model_err)
        composed_viol=max(composed_viol,float(np.max(np.abs(estimate-primitive_scores)-total_error)))
        selected=topk_indices(estimate,k); gamma=operational_gamma(estimate,total_error,k,selected)
        # Exact support-deficit object used by the operational MASTER theorem.
        # Do not substitute selected-set regret: zeta_def is the uniform structural
        # bridge from modular Top-C geometry to support-aware compression.
        z=float(zeta_def(world,k))
        bound=pairwise_master_bound(gamma,z,world.residual_supnorm()); true_opt,_=exact_optimum(world,k,true_loss=True); true_reg=world.true_compression_loss(selected)-true_opt
        topk_records.append({"match":int(set(selected)==set(topk_indices(primitive_scores,k))),"true_regret":true_reg,"bound":bound,"violation":true_reg-bound,"gamma":gamma})
        box_records.append(box_gamma_diagnostics(estimate,total_error,k,selected))
        # Cascade utility uses a centered noisy score with a guaranteed cover.
        noise=rng.normal(scale=0.03,size=m); noisy=primitive_scores+noise; err=np.abs(noise)+1e-10
        cascade.append(cascade_evaluation(world,noisy,err,k,tolerance))
        support_records.append({
            "mean_width":float(np.mean(cplus-cminus)),
            "max_width":float(np.max(cplus-cminus)),
            "nonzero_width":bool(np.max(cplus-cminus)>1e-12),
            "focus_relation":int(focus_j),
            "truth_covered":bool(np.all(cminus<=primitive_scores+1e-10) and np.all(primitive_scores<=cplus+1e-10)),
        })
    def agg(rows,key):
        vals=np.asarray([r[key] for r in rows],dtype=float); return {"mean":float(np.mean(vals)),"median":float(np.median(vals)),"p90":float(np.quantile(vals,.9))}
    acquisition_summary={mode:{b:{"kernel_tv":agg(rows,"kernel_tv"),"chi_error":agg(rows,"chi_error"),"score_error":agg(rows,"score_error"),"mean_min_source_count":float(np.mean([r['min_source_count'] for r in rows])),"mean_source_imbalance":float(np.mean([r['source_count_imbalance'] for r in rows]))} for b,rows in by_budget.items()} for mode,by_budget in acquisition.items()}
    # Frozen split calibration: threshold is chosen on the first half and evaluated only on the second half.
    calibration={}
    for mode,by_budget in acquisition.items():
        calibration[mode]={}
        for b,rows in by_budget.items():
            split=max(1,len(rows)//2); cal=rows[:split]; test=rows[split:]
            threshold=float(np.quantile([r['score_error'] for r in cal],.95))
            calibration[mode][b]={"calibration_n":len(cal),"test_n":len(test),"frozen_score_error_radius":threshold,"heldout_coverage":float(np.mean([r['score_error']<=threshold+1e-12 for r in test])) if test else None}
    # Evaluate utility over a tolerance frontier.  This prevents a single
    # arbitrarily chosen tolerance from being mistaken for universal
    # non-vacuity and makes high fallback rates explicit.
    frontier_tolerances=sorted(set([0.0,0.01,0.02,0.05,0.1,0.2,0.5,1.0,2.0,float(tolerance)]))
    cascade_frontier={}
    for tol in frontier_tolerances:
        accepted=[r for r in cascade if r['certificate'] <= tol + 1e-15]
        fallback_rate=float(np.mean([r['certificate'] > tol + 1e-15 for r in cascade]))
        false_safe=sum(r['candidate_regret'] > tol + 1e-10 for r in accepted)
        cascade_frontier[str(tol)]={
            'tolerance':float(tol),
            'fallback_rate':fallback_rate,
            'accepted_fraction':1.0-fallback_rate,
            'accepted_count':len(accepted),
            'false_safe_count':int(false_safe),
            'false_safe_rate':float(false_safe/max(1,len(accepted))),
            'mean_candidate_regret_when_accepted':float(np.mean([r['candidate_regret'] for r in accepted])) if accepted else None,
        }
    return {
        "protocol_version":PROTOCOL_VERSION,"development_only":True,"instances":int(instances),"seed":int(seed),"budgets":list(map(int,budgets)),
        "reference_uncertainty":{"worst_violation":ru_viol,"composed_score_worst_violation":float(composed_viol),"RU2_factor_two_sharpness":ru2_factor_two_sharpness_diagnostics()},
        "reference_identifiability":_identifiability_search(rng),
        "box_gamma":{"lean_strict_witness":box_gamma_lean_witness_diagnostics(),"strict_tightening_fraction":float(np.mean([r['strict_tightening'] for r in box_records])),"mean_tightening":float(np.mean([r['tightening'] for r in box_records])),"mean_box_over_operational":float(np.mean([r['box_gamma']/max(r['operational_gamma'],1e-12) for r in box_records])),"worst_box_le_operational_violation":float(max(r['box_le_operational_violation'] for r in box_records)),"worst_vertex_bound_violation":float(max(r['vertex_bound_violation'] for r in box_records))},
        "probability_lift":probability_lift_diagnostics(repetitions=max(2000,int(instances)*20),seed=seed+707,m=6,k=2,alpha=.05,n=64),
        "active_acquisition":acquisition_summary,
        "active_acquisition_semantics":{
            "passive":"source actions follow a fixed skewed visitation distribution",
            "randomized":"source actions are sampled uniformly at random",
            "targeted":"balanced least-observed source-action allocation; this is stratified coverage targeting, not an uncertainty-adaptive policy",
            "uncertainty_targeted":"adaptive posterior row-uncertainty targeting after a small pilot; uses only accumulated observations",
        },
        "heldout_calibration":calibration,
        "master_transfer":{"mean_true_regret":float(np.mean([r['true_regret'] for r in topk_records])),"mean_bound":float(np.mean([r['bound'] for r in topk_records])),"worst_violation":float(max(r['violation'] for r in topk_records)),"topk_match_rate":float(np.mean([r['match'] for r in topk_records]))},
        "support_uncertainty":{
            "coverage_rate":float(np.mean([r['truth_covered'] for r in support_records])),
            "mean_span_interval_width":float(np.mean([r['mean_width'] for r in support_records])),
            "nonzero_width_fraction":float(np.mean([r['nonzero_width'] for r in support_records])),
        },
        "cascade":{"tolerance":float(tolerance),"fallback_rate":float(np.mean([r['fallback'] for r in cascade])),"safe_rate":float(np.mean([r['certificate_safe'] for r in cascade])),"mean_regret":float(np.mean([r['regret'] for r in cascade])),"mean_candidate_regret":float(np.mean([r['candidate_regret'] for r in cascade])),"mean_exact_runtime_when_called":float(np.mean([r['exact_runtime_seconds'] for r in cascade if r['fallback']])) if any(r['fallback'] for r in cascade) else 0.0,"mean_cascade_runtime":float(np.mean([r['cascade_runtime_seconds'] for r in cascade])),"frontier":cascade_frontier},
    }


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=100); p.add_argument('--seed',type=int,default=0); p.add_argument('--budgets',nargs='+',type=int,default=[16,32,64,128,256]); p.add_argument('--tolerance',type=float,default=.05); p.add_argument('--out',default='research/high_value_extensions/master/summary.json'); a=p.parse_args(argv)
    payload=run(a.instances,tuple(a.budgets),a.seed,a.tolerance); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); worst=max(payload['reference_uncertainty']['worst_violation'].values()); return 0 if worst<=1e-8 and payload['master_transfer']['worst_violation']<=1e-8 else 2
if __name__=='__main__': raise SystemExit(main())
