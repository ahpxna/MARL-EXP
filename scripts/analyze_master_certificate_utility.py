from __future__ import annotations
import argparse,json
from pathlib import Path
import numpy as np
from research_chains.provenance import write_artifact_with_provenance
from scripts.run_master_certificate_utility import PROTOCOL_VERSION

def analyze(payload):
    rows=payload['rows']; out={}
    for tol in payload['tolerances']:
        group=[r for r in rows if r['tolerance']==tol]; known=[r for r in group if r['regret'] is not None]
        certified=[r for r in known if not r['fallback']]
        out[str(tol)]={'certified_fraction':len(certified)/max(1,len(known)),'fallback_fraction':sum(r['fallback'] for r in known)/max(1,len(known)),
            'false_safe_rate':sum(bool(r['false_safe']) for r in certified)/max(1,len(certified)),
            'mean_regret':float(np.mean([r['regret'] for r in known])) if known else None,
            'worst_regret':float(max([r['regret'] for r in known])) if known else None,
            'mean_certificate_seconds':float(np.mean([r['certificate_seconds'] for r in group]))}
    return {'schema':'master_certificate_utility_analysis_v1','protocol_version':PROTOCOL_VERSION,'frontier':out,
        'all_known_bounds_covered':all(r['covered'] is not False for r in rows)}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('artifact'); p.add_argument('--out',default='research/high_value_extensions/master/full_utility_analysis.json'); a=p.parse_args(argv)
    payload=analyze(json.load(open(a.artifact))); write_artifact_with_provenance(Path(a.out),payload,protocol={'protocol_version':PROTOCOL_VERSION,'input':a.artifact},evidence_class='DEVELOPMENT_ANALYSIS',chain='MASTER'); print(json.dumps(payload,indent=2)); return 0 if payload['all_known_bounds_covered'] else 2
if __name__=='__main__': raise SystemExit(main())
