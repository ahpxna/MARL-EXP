"""Fail-closed external capability audit for MASTER reference/support experiments."""
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
    payload={'protocol_version':'external_master_capability_v1','environment':a.environment,'repo':str(repo_path(a.environment)),'repo_exists':repo_path(a.environment).exists(),'capabilities':vars(cap),'master':{
      'clone_state_interventions':h1,
      'state_dependent_action_mask':bool(cap.state_dependent_action_mask),
      'reference_kernel_observable':False,
      'reference_identifiability_experiment_runnable':False,
      'support_outer_inner_bracket_oracle':False,
      'blockers':['generic adapter exposes response interventions but not the conditional co-action kernel kappa','generic adapter does not expose certified inner/outer feasible-support brackets'],
      'allowed_now':['response-surface collection where H1 panel is supported','command/action-mask diagnostics'],
    },'scientific_rule':'do not infer kappa or true feasible support from policy visitation alone'}
    atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
