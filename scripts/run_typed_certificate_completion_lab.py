"""Development lab for Typed Heterogeneous Certificate Completion (TCC).

This is not generic active-feature acquisition.  It measures the cost of
completing *typed proof obligations* and records how often cheap evidence is
semantically unusable for the obligation it superficially resembles.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.novelty_completion import EvidenceItem, minimum_cost_typed_completion
from research_chains.provenance import write_artifact_with_provenance

PROTOCOL_VERSION='typed_certificate_completion_lab_v1'
TYPES=('RESPONSE','REFERENCE','SUPPORT','INTERACTION','QUERY')

def run(instances=500,seed=0):
    rng=np.random.default_rng(seed); rows=[]
    for idx in range(int(instances)):
        n=int(rng.integers(5,10)); obligations={f'o{j}':TYPES[j%len(TYPES)] for j in range(n)}
        evidence=[]; individual_cost=0.0
        for j,(o,t) in enumerate(obligations.items()):
            c=float(rng.uniform(.8,2.5)); individual_cost+=c
            evidence.append(EvidenceItem(f'direct_{j}',t,c,frozenset({o})))
            # Cheap wrong-type decoy: it must never discharge the obligation.
            wrong=TYPES[(TYPES.index(t)+1)%len(TYPES)]
            evidence.append(EvidenceItem(f'decoy_{j}',wrong,float(rng.uniform(.05,.3)),frozenset()))
        # Same-type bundles create a real completion-cost optimization problem.
        for t in TYPES:
            obs=[o for o,ot in obligations.items() if ot==t]
            if len(obs)>=2:
                direct=sum(x.cost for x in evidence if x.evidence_type==t and len(x.discharges)==1 and next(iter(x.discharges)) in obs)
                evidence.append(EvidenceItem(f'bundle_{t}',t,float(direct*rng.uniform(.45,.85)),frozenset(obs)))
        sol=minimum_cost_typed_completion(obligations,evidence)
        if not sol['complete']: raise AssertionError('constructed catalogue must be completable')
        rows.append({'optimal_cost':sol['cost'],'individual_direct_cost':individual_cost,
                     'cost_ratio':sol['cost']/individual_cost,'selected_count':len(sol['selected']),
                     'decoy_count':sum(x.key.startswith('decoy_') for x in evidence)})
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'instances':int(instances),'seed':int(seed),
            'evidence_types':list(TYPES),'semantics':'evidence may discharge only obligations of the same declared type',
            'mean_cost_ratio_vs_individual_direct':float(np.mean([r['cost_ratio'] for r in rows])),
            'median_cost_ratio_vs_individual_direct':float(np.median([r['cost_ratio'] for r in rows])),
            'mean_selected_evidence_count':float(np.mean([r['selected_count'] for r in rows])),
            'typed_decoys_never_used_by_construction':True,'rows':rows[:50]}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=500); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/novelty_critical/tcc.json'); a=p.parse_args(argv)
    out=run(a.instances,a.seed); write_artifact_with_provenance(Path(a.out),out,protocol={'protocol_version':PROTOCOL_VERSION,'instances':a.instances},seed=a.seed,evidence_class='DEVELOPMENT_SYNTHETIC_CERTIFICATE_COMPLETION',chain='MASTER'); print(json.dumps(out,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
