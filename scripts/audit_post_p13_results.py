"""Audit archived result artifacts against the post-P13 experiment programme.

The audit never rewrites old artifacts.  It marks stale analyses/historical
runs and missing new-proposal evidence so provenance is preserved.
"""
from __future__ import annotations
import argparse,json,re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def _load(path):
    try:return json.loads(path.read_text())
    except Exception:return None

def audit(root: Path, source_root: Path | None = None):
    root=Path(root); source_root=Path(source_root) if source_root is not None else ROOT; findings=[]
    # Functional variance analysis v1 named uniform as winner when all deployable
    # medians were right-censored at max_n+1.  Detect but never mutate artifact.
    raw=root/'research/high_value_extensions/functional/variance_stopping_deep_v5.json'
    ana=root/'research/high_value_extensions/functional/variance_stopping_deep_v5_analysis.json'
    p=_load(raw) if raw.exists() else None; a=_load(ana) if ana.exists() else None
    if p and a:
        deploy=p.get('deployable_variants',[]); max_n=int(p.get('max_n',0)); rows=p.get('by_variant',{})
        med=[float(rows[x].get('median_censored_N_certificate',rows[x].get('median_N_certificate',-1))) for x in deploy if x in rows]
        if med and min(med)>max_n and a.get('deployable_winner') is not None:
            findings.append({'severity':'STALE_ANALYSIS','artifact':str(ana.relative_to(root)),'code':'FUNCTIONAL_CENSORED_MEDIAN_WINNER',
              'detail':'all deployable median certificate times are censored at max_n+1; v1 winner is tuple-order artifact, not an identified primary-endpoint winner'})
    # Confirmatory protocol completeness.
    for name in ('confirmatory_functional_v2_fresh','confirmatory_functional'):
        d=root/'research'/name; proto=_load(d/'CONFIRMATORY_PROTOCOL.json') if (d/'CONFIRMATORY_PROTOCOL.json').exists() else None
        if not proto: continue
        expected=set(map(int,proto.get('seeds',[])))
        panel=set()
        for f in (d/'panels').glob('fixed_panel_seed*.pkl.gz') if (d/'panels').exists() else []:
            m=re.search(r'seed(\d+)',f.name)
            if m: panel.add(int(m.group(1)))
        missing=sorted(expected-panel)
        checkpoints=list(map(int,proto.get('frozen',{}).get('checkpoints',[])))
        run_seed_counts={}; missing_runs={}
        for ep in checkpoints:
            completed=set()
            epdir=d/'runs'/f'ep{ep}'
            if epdir.exists():
                for f in epdir.glob('seed*/v7_complete.json'):
                    m=re.search(r'seed(\d+)',f.parent.name)
                    if m: completed.add(int(m.group(1)))
            run_seed_counts[str(ep)]=len(completed)
            missing_runs[str(ep)]=sorted(expected-completed)
        complete=(not missing) and all(not x for x in missing_runs.values())
        if not complete:
            findings.append({'severity':'INCOMPLETE','artifact':str(d.relative_to(root)),'code':'FUNCTIONAL_CONFIRMATORY_INCOMPLETE',
              'expected_seeds':len(expected),'panel_seeds_present':len(panel),'missing_panel_seeds':missing,
              'completed_run_seeds_by_checkpoint':run_seed_counts,'missing_run_seeds_by_checkpoint':missing_runs})
    # Old high-value decision matrix predates the post-P13 v3 proposal layer.
    # It is a chain-level historical matrix and embeds no registry proposal count,
    # so do not invent a historical count.  Mark it stale *only as a coverage
    # summary* relative to the current source registry; its original decisions
    # remain valid historical artifacts.
    reg=_load(source_root/'config/PROPOSAL_EXPERIMENT_REGISTRY.json')
    matrix_path=root/'research/high_value_extensions/runs_screening_v3/DECISION_MATRIX_AUTO.json'; matrix=_load(matrix_path) if matrix_path.exists() else None
    post_p13_ids=[
      'MASTER.TYPED_CERTIFICATE_COMPLETION','FUNCTIONAL.SELECTIVE_CERTIFICATE_MAINTENANCE',
      'SUPPORT.DECISION_CRITICAL_IDENTIFICATION','STRUCTURAL.PREFIX_COVER_DIMENSION',
      'D6.COST_AWARE_PAEC_COMPLETION','D6.FIRST_ORDER_INSUFFICIENCY_B7',
      'QUERY.IDENTIFIABILITY_VERIFIER',
    ]
    if reg and matrix and reg.get('schema')=='cig_amf_proposal_experiment_registry_v3':
        registered={x.get('proposal_id') for x in reg.get('items',[])}
        if all(x in registered for x in post_p13_ids):
            findings.append({'severity':'STALE_SUMMARY','artifact':str(matrix_path.relative_to(root)),'code':'PROPOSAL_REGISTRY_DRIFT',
              'artifact_registry_count':None,'current_registry_count':len(reg.get('items',[])),'new_proposal_ids':post_p13_ids,
              'detail':'historical chain-level matrix remains valid for its generation but contains no post-P13 novelty-critical experiment evidence and must not be treated as current coverage'})
    # Later result generations supersede two historical screening summaries.
    # Preserve the old matrix but prevent it from being used as the current state.
    if matrix:
        mdec=matrix.get('decisions',{}).get('MASTER',{})
        utility=root/'research/high_value_extensions/master/full_utility_seed100_analysis.json'; u=_load(utility) if utility.exists() else None
        if mdec.get('utility_nonvacuous') is False and u:
            frontier=u.get('frontier',{})
            vals=list(frontier.values()) if isinstance(frontier,dict) else list(u.get('by_epsilon',[]))
            false_safe=[float(r.get('false_safe_rate',0.0)) for r in vals if r.get('false_safe_rate') is not None]
            cert=[float(r.get('certified_fraction',0.0)) for r in vals if r.get('certified_fraction') is not None]
            if cert and max(cert)>0 and (not false_safe or max(false_safe)<=1e-12):
                findings.append({'severity':'STALE_INTERPRETATION','artifact':str(matrix_path.relative_to(root)),'code':'MASTER_SINGLE_POINT_NONVACUITY_STALE',
                  'historical_value':False,'later_max_certified_fraction':max(cert),'later_max_false_safe_rate':max(false_safe) if false_safe else 0.0,
                  'detail':'screening-era utility_nonvacuous=false is a historical single-operating-point interpretation; later coverage-tolerance analysis must be used for current utility claims'})
        ddec=matrix.get('decisions',{}).get('D6',{})
        later=root/'research/p13_redesign/d6/optimizer_m3k1_qopt202_with_q.json'; dl=_load(later) if later.exists() else None
        if dl and isinstance(dl.get('best_witness'),dict):
            later_ratio=float(dl['best_witness'].get('ratio_regret_over_approx_rhs',-1.0)); old_ratio=float(ddec.get('half_factor_adversarial_best_ratio_to_worst_rhs',-1.0))
            if later_ratio>old_ratio+1e-12:
                findings.append({'severity':'STALE_SUMMARY','artifact':str(matrix_path.relative_to(root)),'code':'D6_ADVERSARIAL_RATIO_STALE',
                  'historical_screening_ratio':old_ratio,'later_p13_ratio':later_ratio,'candidate_killed':bool(dl.get('candidate_killed',False)),
                  'detail':'historical screening ratio remains valid for that generation but is not the current adversarial frontier'})

    # New experiment outputs expected after this patch.
    expected_new={
      'MASTER':'research/novelty_critical/tcc.json',
      'FUNCTIONAL':'research/novelty_critical/functional_selective_maintenance.json',
      'SUPPORT':'research/novelty_critical/support_critical_identification.json',
      'STRUCTURAL':'research/novelty_critical/structural_prefix_cover.json',
      'D6':'research/novelty_critical/d6_cost_aware_paec.json',
      'QUERY':'research/novelty_critical/query_identifiability.json',
    }
    for chain,rel in expected_new.items():
        if not (root/rel).exists(): findings.append({'severity':'MISSING_PLANNED_EVIDENCE','chain':chain,'artifact':rel,'code':'POST_P13_EXPERIMENT_NOT_RUN'})
    # External status is machine/check-out specific; do not carry readiness across machines.
    ext=root/'research/redesign_validation/external_status.json'; e=_load(ext) if ext.exists() else None
    if e and e.get('root') and str(root) not in str(e.get('root')):
        findings.append({'severity':'STALE_MACHINE_STATE','artifact':str(ext.relative_to(root)),'code':'EXTERNAL_PATH_FROM_DIFFERENT_CHECKOUT',
                         'recorded_root':e.get('root'),'detail':'rerun external environment audit on the execution machine before using readiness flags'})
    return {'schema':'post_p13_result_audit_v2','artifact_root':str(root),'source_root':str(source_root),'finding_count':len(findings),'findings':findings}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--root',default='.',help='artifact/result tree to audit'); p.add_argument('--source-root',default=str(ROOT),help='current source tree whose registry defines expected post-P13 coverage'); p.add_argument('--out'); a=p.parse_args(argv); out=audit(Path(a.root).resolve(),Path(a.source_root).resolve())
    if a.out: Path(a.out).write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
