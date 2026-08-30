"""Fail-closed audit of which relational queries each external adapter can actually ground."""
from __future__ import annotations
import argparse,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))
from research_chains.provenance import atomic_json
ENVIRONMENTS=('cityflow','cyborg','flatland','rware')

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--environment',choices=ENVIRONMENTS,required=True); p.add_argument('--out',required=True); a=p.parse_args(argv)
    from envs.external.registry import SPECS,repo_path
    cap=SPECS[a.environment].capabilities
    h1=bool(cap.clone_restore and cap.fixed_continuation and cap.fixed_discrete_actions)
    queries={
      'response_sensitivity':{'runnable':h1,'requires':['clone_restore','fixed_continuation','oracle_lag_response']},
      'signed_policy_projection':{'runnable':h1,'requires':['same response surface + declared weights']},
      'information_value':{'runnable':False,'blocker':'adapter has no information-query oracle/latent law contract'},
      'removal_randomization':{'runnable':False,'blocker':'adapter has no standardized agent-removal/randomization intervention contract'},
      'deletion_logit_stability':{'runnable':False,'blocker':'adapter has no standardized message/edge deletion and logit-stability oracle contract'},
      'causal_contribution':{'runnable':False,'blocker':'adapter has no causal attribution ground-truth contract'},
      'coalition_synergy':{'runnable':False,'blocker':'adapter has no coalition/hyperedge intervention oracle'},
      'overlapping_group_hyperedge':{'runnable':False,'blocker':'adapter has no overlapping-group/hyperedge ground-truth contract'},
      'communication_staleness':{'runnable':False,'blocker':'adapter has no standardized delayed-message intervention contract'},
    }
    payload={'protocol_version':'external_query_capability_v1','environment':a.environment,'repo':str(repo_path(a.environment)),'repo_exists':repo_path(a.environment).exists(),'queries':queries,'all_query_transfer_runnable':all(v['runnable'] for v in queries.values()),'scientific_rule':'blocked query cells must remain NA, never be replaced by a different semantics'}
    atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
