from __future__ import annotations
import argparse,json
from pathlib import Path
from research_chains.provenance import write_artifact_with_provenance
from scripts.run_functional_variance_stopping_lab import PROTOCOL_VERSION
def analyze(p):
    if p.get('protocol_version')!=PROTOCOL_VERSION: raise ValueError('protocol mismatch')
    rows=p['by_variant']; deploy=p['deployable_variants']; winner=min(deploy,key=lambda x:rows[x]['median_N_certificate'])
    return {'schema':'functional_variance_stopping_analysis_v1','primary_endpoint':'N_certificate',
        'deployable_winner':winner,'known_sigma_excluded':p['diagnostic_variants']==['C_known_sigma'],
        'all_deployable_false_safe_zero':all(rows[x]['false_safe_count']==0 for x in deploy),'by_variant':rows}
def main(argv=None):
    q=argparse.ArgumentParser(); q.add_argument('artifact'); q.add_argument('--out',default='research/high_value_extensions/functional/variance_stopping_analysis.json'); a=q.parse_args(argv)
    out=analyze(json.load(open(a.artifact))); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'input':a.artifact},evidence_class='DEVELOPMENT_ANALYSIS',chain='FUNCTIONAL'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
