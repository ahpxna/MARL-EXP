"""Current D6 falsification campaign for the rank-one replacement conjecture."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))

from research_chains.d6_contrast_rank import search_generated_rank_one,direct_rank_one_penalty_search,adversarial_multiaffine_rank_one_search
from research_chains.provenance import write_artifact_with_provenance

PROTOCOL_VERSION='d6_contrast_rank_falsification_v1'


def run(instances=300,seed=0,m_values=(4,6),actions=3,b3_restarts=2,b3_steps=100,skip_b3=False,b2_adv_restarts=2,b2_adv_steps=120):
    families=('B1_pairwise','Bproduct','B2_multiaffine'); results={}
    for offset,family in enumerate(families):
        results[family]=search_generated_rank_one(
            family=family,instances=int(instances),seed=int(seed)+101*offset,
            m_values=tuple(map(int,m_values)),K=int(actions),
            reference_modes=('point0','uniform','rational'))
    results['B2_adversarial']=adversarial_multiaffine_rank_one_search(seed=int(seed)+733,restarts=int(b2_adv_restarts),steps=int(b2_adv_steps),m=4,K=int(actions))
    if skip_b3:
        results['B3_direct']={'available':False,'reason':'SKIPPED_BY_CALLER','candidate_killed':False}
    else:
        # The direct penalty search is intentionally kept at m=4: it is a
        # small-domain adversarial gate, not a scalability benchmark.
        results['B3_direct']=direct_rank_one_penalty_search(
            seed=int(seed)+997,restarts=int(b3_restarts),steps=int(b3_steps),m=4,K=int(actions))
    killed=[name for name,row in results.items() if row.get('candidate_killed')]
    construction_failures=sum(int(row.get('rank_one_construction_failures',0)) for row in results.values())
    return {
        'protocol_version':PROTOCOL_VERSION,'development_only':True,
        'scientific_target':'AllCoordinatesInteractionContrastRankOne => 2D <= (m-1) delta_square',
        'known_general_status':'FALSE without the rank-one restriction, including strict Top-C ternary worlds',
        'instances_per_generated_family':int(instances),'seed':int(seed),'m_values':list(map(int,m_values)),'actions':int(actions),
        'results':results,'rank_one_construction_failure_count':int(construction_failures),
        'candidate_killed':bool(killed),'killed_by':killed,
        'survival_interpretation':'B1/B-product/B2/B3 survival is theorem-discovery evidence only; do not promote to proof',
        'next_action':('formalize the first exact/rational counterexample and abandon rank-only law' if killed else
                       'increase adversarial/exact coverage before any universal Lean proof'),
    }


def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--instances',type=int,default=300); p.add_argument('--seed',type=int,default=0)
    p.add_argument('--m-values',nargs='+',type=int,default=[4,6]); p.add_argument('--actions',type=int,default=3)
    p.add_argument('--b3-restarts',type=int,default=2); p.add_argument('--b3-steps',type=int,default=100); p.add_argument('--skip-b3',action='store_true'); p.add_argument('--b2-adv-restarts',type=int,default=2); p.add_argument('--b2-adv-steps',type=int,default=120)
    p.add_argument('--out',default='research/current_six_reports/d6/contrast_rank_falsification.json'); a=p.parse_args(argv)
    payload=run(a.instances,a.seed,tuple(a.m_values),a.actions,a.b3_restarts,a.b3_steps,a.skip_b3,a.b2_adv_restarts,a.b2_adv_steps)
    write_artifact_with_provenance(Path(a.out),payload,
        protocol={'protocol_version':PROTOCOL_VERSION,'instances':a.instances,'m_values':a.m_values,'actions':a.actions,'b3_restarts':a.b3_restarts,'b3_steps':a.b3_steps,'skip_b3':a.skip_b3,'b2_adv_restarts':a.b2_adv_restarts,'b2_adv_steps':a.b2_adv_steps},
        seed=a.seed,evidence_class='DEVELOPMENT_ADVERSARIAL_FALSIFICATION',chain='D6')
    print(json.dumps(payload,indent=2)); return 0

if __name__=='__main__': raise SystemExit(main())
