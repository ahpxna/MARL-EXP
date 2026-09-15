from __future__ import annotations
import argparse,json
from pathlib import Path
import numpy as np
from research_chains.provenance import write_artifact_with_provenance
from scripts.run_master_certificate_utility import PROTOCOL_VERSION

def _frontier_for(rows,tolerances,prefix):
    out={}
    fallback_key='fallback' if prefix=='active' else f'fallback_{prefix}'
    false_key='false_safe' if prefix=='active' else f'false_safe_{prefix}'
    cert_key='certificate' if prefix=='active' else f'certificate_{prefix}'
    covered_key='covered' if prefix=='active' else f'covered_{prefix}'
    for tol in tolerances:
        group=[r for r in rows if r['tolerance']==tol]
        known=[r for r in group if r['regret'] is not None]
        certified=[r for r in known if not bool(r[fallback_key])]
        out[str(tol)]={
            'certified_fraction':len(certified)/max(1,len(known)),
            'fallback_fraction':sum(bool(r[fallback_key]) for r in known)/max(1,len(known)),
            'false_safe_rate':sum(bool(r[false_key]) for r in certified)/max(1,len(certified)),
            'mean_regret':float(np.mean([r['regret'] for r in known])) if known else None,
            'worst_regret':float(max([r['regret'] for r in known])) if known else None,
            'mean_certificate':float(np.mean([r[cert_key] for r in group])) if group else None,
            'mean_certificate_seconds':float(np.mean([r['certificate_seconds'] for r in group])) if group else None,
            'all_known_bounds_covered':all(r.get(covered_key) is not False for r in group),
        }
    return out


def analyze(payload):
    rows=payload['rows']; tolerances=payload['tolerances']
    active=_frontier_for(rows,tolerances,'active')
    operational=_frontier_for(rows,tolerances,'operational')
    box=_frontier_for(rows,tolerances,'box')
    delta={}
    for tol in tolerances:
        key=str(tol)
        delta[key]={
            'box_minus_operational_certified_fraction':box[key]['certified_fraction']-operational[key]['certified_fraction'],
            'operational_minus_box_fallback_fraction':operational[key]['fallback_fraction']-box[key]['fallback_fraction'],
        }
    return {
        'schema':'master_certificate_utility_analysis_v2','protocol_version':PROTOCOL_VERSION,
        'active_gamma':payload.get('active_gamma','op'),'frontier':active,
        'frontier_operational':operational,'frontier_box':box,
        'paired_frontier_delta':delta,
        'gamma_box_strict_tightening_fraction':float(np.mean([bool(r.get('gamma_box_strict_tightening')) for r in rows])) if rows else None,
        'all_known_bounds_covered':all(r['covered'] is not False for r in rows),
        'all_known_operational_bounds_covered':all(r.get('covered_operational') is not False for r in rows),
        'all_known_box_bounds_covered':all(r.get('covered_box') is not False for r in rows),
    }


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('artifact'); p.add_argument('--out',default='research/high_value_extensions/master/full_utility_analysis.json'); a=p.parse_args(argv)
    payload=analyze(json.load(open(a.artifact))); write_artifact_with_provenance(Path(a.out),payload,protocol={'protocol_version':PROTOCOL_VERSION,'input':a.artifact},evidence_class='DEVELOPMENT_ANALYSIS',chain='MASTER'); print(json.dumps(payload,indent=2)); return 0 if payload['all_known_bounds_covered'] else 2
if __name__=='__main__': raise SystemExit(main())
