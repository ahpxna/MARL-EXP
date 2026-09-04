"""Current one-command development suite for all six CIG-AMF reports.

Unlike historical suites, this runner reflects the post-2026-09-03 state:
* unrestricted D6 m-1 is already falsified and is NOT retested as a live law;
* Structural tests the parametric staircase exact-chi discovery target;
* Functional tests certificate acquisition and selective maintenance;
* MASTER tests typed completion, reference acquisition/budget split and utility;
* Support tests decision-critical support discovery;
* Query tests semantic transfer + identifiability.

Scientific counterexamples are reported as findings, not orchestration errors.
"""
from __future__ import annotations
import argparse,json,sys,time,traceback
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))

from research_chains.provenance import atomic_json,source_fingerprint
from scripts import run_master_extension_lab as master_ext
from scripts import run_typed_certificate_completion_lab as tcc
from scripts import run_reference_response_budget_lab as ref_budget
from scripts import run_master_certificate_utility as master_utility
from scripts import run_functional_variance_stopping_lab as fvar
from scripts import run_functional_selective_maintenance_lab as fmaint
from scripts import run_support_critical_identification_lab as support_lab
from scripts import run_structural_staircase_exact_lab as staircase
from scripts import run_d6_contrast_rank_falsification as d6rank
from scripts import run_query_extension_lab as query_ext
from scripts import run_query_identifiability_lab as query_id

PROTOCOL_VERSION='current_six_report_suite_v1'
PROFILES={
 'quick':{
   'master_ext':20,'tcc':60,'ref_instances':8,'ref_seeds':(7101,), 'ref_budgets':(64,128),
   'utility_instances':1,'utility_ms':(3,4,6),'utility_families':('cartesian','weak_coupling','strong_coupling','nonnested','support_uncertainty'),
   'fvar_instances':6,'fvar_seeds':(7201,), 'fvar_max_n':768,'fvar_batch':16,'fmaint':120,
   'support':60,'stair_r':(1,2,3,4,5),'d6':90,'d6_m':(4,), 'b3_restarts':1,'b3_steps':60,
   'query':90,'query_id':250,
 },
 'screening':{
   'master_ext':120,'tcc':500,'ref_instances':50,'ref_seeds':(7101,7102,7103),'ref_budgets':(64,128,256,512),
   'utility_instances':2,'utility_ms':(3,4,6,8,12),'utility_families':('cartesian','coextremizable','weak_coupling','moderate_coupling','strong_coupling','cancellation','nonnested','support_uncertainty'),
   'fvar_instances':40,'fvar_seeds':(7201,7202,7203),'fvar_max_n':4096,'fvar_batch':16,'fmaint':1000,
   'support':500,'stair_r':(1,2,3,4,5,6),'d6':900,'d6_m':(4,6),'b3_restarts':4,'b3_steps':180,
   'query':800,'query_id':3000,
 },
}

def _false_safe_master_utility(payload):
    return int(sum(1 for r in payload.get('rows',[]) if r.get('false_safe') is True))

def _false_safe_ref_budget(payload):
    total=0.0
    for by_split in payload.get('by_budget',{}).values():
        for row in by_split.values(): total+=float(row.get('false_safe',0.0))
    return float(total)

def _functional_false_safe(payload):
    return int(sum(int(v.get('false_safe_count',0)) for k,v in payload.get('by_variant',{}).items() if k in payload.get('deployable_variants',[])))

def _query_lower_violation(payload):
    return float(payload.get('two_world_lower_bound',{}).get('worst_violation',0.0))

def run(profile='quick',seed=7000,out_root='research/current_six_reports'):
    cfg=PROFILES[str(profile)]; out=Path(out_root); out.mkdir(parents=True,exist_ok=True)
    jobs={
      'MASTER':[
        ('master_extension',lambda:master_ext.run(cfg['master_ext'],(16,32,64),seed+1,.05)),
        ('master_typed_completion',lambda:tcc.run(cfg['tcc'],seed+2)),
        ('master_reference_response_budget',lambda:ref_budget.run(cfg['ref_instances'],cfg['ref_seeds'],cfg['ref_budgets'],(0.0,.1,.3,.5,.7,.9),4,3,2,.05)),
        ('master_certificate_utility',lambda:master_utility.run(seed+3,cfg['utility_instances'],cfg['utility_ms'],(.01,.05,.2,.5,1.0),cfg['utility_families'],4096,500000)),
      ],
      'FUNCTIONAL':[
        ('functional_variance_stopping',lambda:fvar.run(cfg['fvar_instances'],cfg['fvar_seeds'],5,6,2,.05,cfg['fvar_max_n'],cfg['fvar_batch'],.15)),
        ('functional_selective_maintenance',lambda:fmaint.run(cfg['fmaint'],seed+11,8,3)),
      ],
      'SUPPORT':[
        ('support_critical_identification',lambda:support_lab.run(cfg['support'],seed+21,4,2,.05)),
      ],
      'STRUCTURAL':[
        ('structural_staircase_exact',lambda:staircase.run(cfg['stair_r'],True)),
      ],
      'D6':[
        ('d6_contrast_rank_falsification',lambda:d6rank.run(cfg['d6'],seed+31,cfg['d6_m'],3,cfg['b3_restarts'],cfg['b3_steps'],False)),
      ],
      'QUERY':[
        ('query_transfer',lambda:query_ext.run(cfg['query'],seed+41,10,3)),
        ('query_identifiability',lambda:query_id.run(cfg['query_id'],seed+42)),
      ],
    }
    records=[]; payloads={}
    for paper,items in jobs.items():
        payloads[paper]={}
        for name,fn in items:
            t0=time.perf_counter(); status='PASS'; error=None
            try: payload=fn()
            except Exception as exc:
                status='ERROR'; error=f'{type(exc).__name__}: {exc}'; payload={'error':error,'traceback':traceback.format_exc()}
            elapsed=time.perf_counter()-t0; payloads[paper][name]=payload
            path=out/paper.lower()/f'{name}.json'; atomic_json(path,payload)
            rec={'paper':paper,'job':name,'status':status,'seconds':float(elapsed),'path':str(path),'error':error}; records.append(rec); print(json.dumps(rec),flush=True)

    # Hard gates are code/theorem-sanity gates only.  Discovery counterexamples
    # (e.g. D6 rank-one candidate killed, staircase chi != r) are scientific
    # findings and must not be converted into runner failures.
    gates={
      'MASTER':{
        'typed_completion_cost_not_above_direct':bool(payloads['MASTER']['master_typed_completion'].get('mean_cost_ratio_vs_individual_direct',2)<=1.0+1e-10),
        'master_utility_false_safe_zero':_false_safe_master_utility(payloads['MASTER']['master_certificate_utility'])==0,
        'reference_budget_false_safe_zero':_false_safe_ref_budget(payloads['MASTER']['master_reference_response_budget'])<=1e-12,
      },
      'FUNCTIONAL':{
        'variance_stopping_false_safe_zero':_functional_false_safe(payloads['FUNCTIONAL']['functional_variance_stopping'])==0,
        'maintenance_false_safe_zero':int(payloads['FUNCTIONAL']['functional_selective_maintenance'].get('false_safe_count',1))==0,
      },
      'SUPPORT':{
        'support_false_safe_zero':int(payloads['SUPPORT']['support_critical_identification'].get('false_safe_count',1))==0,
      },
      'STRUCTURAL':{
        'staircase_dp_milp_agree':bool(payloads['STRUCTURAL']['structural_staircase_exact'].get('all_dp_milp_agree')),
        'staircase_designated_zero':bool(payloads['STRUCTURAL']['structural_staircase_exact'].get('all_designated_zero')),
        'staircase_designated_unique':bool(payloads['STRUCTURAL']['structural_staircase_exact'].get('all_designated_unique')),
      },
      'D6':{
        'generated_rank_one_construction_valid':int(payloads['D6']['d6_contrast_rank_falsification'].get('rank_one_construction_failure_count',1))==0,
      },
      'QUERY':{
        'two_world_lower_bound_no_violation':_query_lower_violation(payloads['QUERY']['query_transfer'])<=1e-10,
        'identifiability_status_contract':set(payloads['QUERY']['query_identifiability'].get('status_values',[]))=={'IDENTIFIABLE','INSUFFICIENT','BLOCKED_NA'},
      },
    }
    hard_gate_pass=all(all(v.values()) for v in gates.values()) and all(r['status']=='PASS' for r in records)
    science={
      'STRUCTURAL':{
        'observed_chi_sequence':payloads['STRUCTURAL']['structural_staircase_exact'].get('observed_sequence'),
        'chi_equals_r_on_tested_range':payloads['STRUCTURAL']['structural_staircase_exact'].get('exact_chi_equals_r_on_tested_range'),
        'interpretation':'finite exact evidence for the next Lean upper construction; not a parametric proof',
      },
      'D6':{
        'rank_one_candidate_killed':payloads['D6']['d6_contrast_rank_falsification'].get('candidate_killed'),
        'killed_by':payloads['D6']['d6_contrast_rank_falsification'].get('killed_by'),
        'interpretation':'a kill falsifies the replacement conjecture; survival does not prove it',
      },
      'FUNCTIONAL':{
        'variance_stopping_winner_status':payloads['FUNCTIONAL']['functional_variance_stopping'].get('deployable_winner_status'),
        'maintenance_cost_fraction':payloads['FUNCTIONAL']['functional_selective_maintenance'].get('mean_refresh_cost_fraction_vs_full'),
      },
      'SUPPORT':{
        'mean_query_fraction':payloads['SUPPORT']['support_critical_identification'].get('mean_query_fraction_of_full_product'),
      },
      'MASTER':{
        'typed_completion_cost_ratio':payloads['MASTER']['master_typed_completion'].get('mean_cost_ratio_vs_individual_direct'),
      },
      'QUERY':{
        'native_query_advantage':payloads['QUERY']['query_transfer'].get('native_query_advantage'),
        'insufficient_fraction':payloads['QUERY']['query_identifiability'].get('insufficient_fraction'),
      },
    }
    manifest={'protocol_version':PROTOCOL_VERSION,'profile':profile,'seed':int(seed),'source_fingerprint':source_fingerprint(ROOT),
              'config':cfg,'records':records,'hard_gates':gates,'hard_gate_pass':bool(hard_gate_pass),'scientific_findings':science,
              'scope':'development-only six-report suite; external/confirmatory blockers remain fail-closed and are not faked'}
    atomic_json(out/'SUITE_MANIFEST.json',manifest)
    return manifest

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--profile',choices=PROFILES,default='quick'); p.add_argument('--seed',type=int,default=7000); p.add_argument('--out-root',default='research/current_six_reports'); a=p.parse_args(argv)
    payload=run(a.profile,a.seed,a.out_root); print(json.dumps({'hard_gate_pass':payload['hard_gate_pass'],'scientific_findings':payload['scientific_findings'],'manifest':str(Path(a.out_root)/'SUITE_MANIFEST.json')},indent=2)); return 0 if payload['hard_gate_pass'] else 2
if __name__=='__main__': raise SystemExit(main())
