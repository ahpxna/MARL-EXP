from __future__ import annotations
import argparse,json
from pathlib import Path
from research_chains.provenance import write_artifact_with_provenance
from scripts.run_reference_response_budget_lab import PROTOCOL_VERSION
def analyze(p):
    if p.get('protocol_version')!=PROTOCOL_VERSION: raise ValueError('protocol mismatch')
    return {'schema':'reference_response_budget_analysis_v1','required_metrics':p['required_metrics'],
        'best_split_by_endpoint':p['best_split_by_endpoint'],'all_false_safe_zero':all(
            row['false_safe']==0 for by in p['by_budget'].values() for row in by.values()),
        'interpretation':'endpoint-specific optima test whether response geometry and reference uncertainty require different budget splits'}
def main(argv=None):
    q=argparse.ArgumentParser(); q.add_argument('artifact'); q.add_argument('--out',default='research/high_value_extensions/master/reference_response_budget_analysis.json'); a=q.parse_args(argv)
    out=analyze(json.load(open(a.artifact))); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'input':a.artifact},evidence_class='DEVELOPMENT_ANALYSIS',chain='REFERENCE'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
