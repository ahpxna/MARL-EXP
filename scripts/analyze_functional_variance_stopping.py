from __future__ import annotations
import argparse,json
from pathlib import Path
from research_chains.provenance import write_artifact_with_provenance
from scripts.run_functional_variance_stopping_lab import PROTOCOL_VERSION

def analyze(p):
    if p.get('protocol_version')!=PROTOCOL_VERSION: raise ValueError('protocol mismatch')
    rows=p['by_variant']; deploy=p['deployable_variants']; max_n=int(p.get('max_n',0))
    med={x:float(rows[x].get('median_censored_N_certificate',rows[x]['median_N_certificate'])) for x in deploy}
    best=min(med.values()); tied=[x for x in deploy if abs(med[x]-best)<=1e-12]
    winner=tied[0] if len(tied)==1 and (max_n<=0 or best<=max_n) else None
    status='IDENTIFIED_BY_MEDIAN' if winner is not None else ('NO_MEDIAN_IDENTIFIED_CENSORING' if max_n>0 and best>max_n else 'NO_MEDIAN_IDENTIFIED_TIE')
    secondary=sorted(deploy,key=lambda x:(-float(rows[x].get('certificate_fraction',0.0)),float(rows[x].get('restricted_mean_censored_N_certificate',rows[x]['median_N_certificate'])),float(rows[x].get('mean_final_capacity_interval_width',float('inf'))),x))
    return {'schema':'functional_variance_stopping_analysis_v2','primary_endpoint':'N_certificate',
        'deployable_winner':winner,'deployable_winner_status':status,'deployable_secondary_order':secondary,
        'known_sigma_excluded':p['diagnostic_variants']==['C_known_sigma'],
        'all_deployable_false_safe_zero':all(rows[x]['false_safe_count']==0 for x in deploy),'by_variant':rows,
        'analysis_correction':'v1 incorrectly named the first deployable variant as winner when right-censored median N_certificate tied at max_n+1'}

def main(argv=None):
    q=argparse.ArgumentParser(); q.add_argument('artifact'); q.add_argument('--out',default='research/high_value_extensions/functional/variance_stopping_analysis.json'); a=q.parse_args(argv)
    out=analyze(json.load(open(a.artifact))); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'analysis_schema':'v2','input':a.artifact},evidence_class='DEVELOPMENT_ANALYSIS',chain='FUNCTIONAL'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
