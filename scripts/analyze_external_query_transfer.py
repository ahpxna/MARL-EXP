"""Fail-closed analysis of typed external Query transfer artifacts."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

import numpy as np

ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.provenance import write_artifact_with_provenance
from scripts.run_external_query_transfer import PROTOCOL_VERSION


def analyze(paths):
    artifacts=[]; cells={}; blocked_methods={}; blocked_queries={}; invalid=[]
    for path in map(Path,paths):
        row=json.loads(path.read_text())
        if row.get('protocol_version')!=PROTOCOL_VERSION:
            invalid.append({'path':str(path),'reason_code':'PROTOCOL_MISMATCH'}); continue
        artifacts.append(str(path))
        blocked_methods.update(row.get('blocked_methods',{})); blocked_queries.update(row.get('blocked_queries',{}))
        for method,queries in row.get('aggregate_transfer_matrix',{}).items():
            for query,metric in queries.items():
                if metric is None: continue
                cells.setdefault((method,query),[]).append(metric)
    matrix={}
    for (method,query),rows in cells.items():
        matrix.setdefault(method,{})[query]={key:float(np.mean([r[key] for r in rows]))
            for key in ('R_m_to_q','topk_exact','jaccard','ndcg','spearman','kendall')}
    faithful_missing=sorted(set(('AttentionWeights','MessageDeletion','CommunicationDelay','VoI','CausalContextAttribution')) & set(blocked_methods))
    return {'schema':'external_query_transfer_analysis_v2','protocol_version':PROTOCOL_VERSION,
        'artifacts':artifacts,'invalid_artifacts':invalid,'primary_endpoint':'R_m_to_q',
        'aggregate_transfer_matrix':matrix,'blocked_methods':blocked_methods,'blocked_queries':blocked_queries,
        'primitive_framework_ready':bool(artifacts and matrix and not invalid),
        'full_relational_query_benchmark_ready':bool(artifacts and matrix and not invalid and not faithful_missing),
        'faithful_method_blockers':faithful_missing,
        'interpretation':'NA cells preserve typed semantic capability; they are not replaced by foreign-query scores.'}


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('artifacts',nargs='+'); p.add_argument('--out',default='research/external/QUERY_TRANSFER_ANALYSIS.json')
    a=p.parse_args(argv); payload=analyze(a.artifacts)
    write_artifact_with_provenance(Path(a.out),payload,protocol={'protocol_version':PROTOCOL_VERSION,
        'input_artifacts':sorted(map(str,a.artifacts))},evidence_class='EXTERNAL_QUERY_ANALYSIS',chain='QUERY')
    print(json.dumps(payload,indent=2)); return 0 if payload['primitive_framework_ready'] else 2


if __name__=='__main__': raise SystemExit(main())
