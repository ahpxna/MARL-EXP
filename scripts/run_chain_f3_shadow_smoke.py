"""Moving-estimand paired-shadow plumbing smoke test (not scientific evidence)."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, copy, hashlib, json
from dataclasses import dataclass
from pathlib import Path
import numpy as np
from research_chains.f3 import paired_shadow_experiment
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='chain_f3_shadow_plumbing_v1'

class ToyEnv:
    def __init__(self): self.state={'x':0.0}
    def clone_state(self): return copy.deepcopy(self.state)
    def restore_state(self,state): self.state=copy.deepcopy(state)

@dataclass
class ToyLearner:
    theta: float=0.0
    updates: int=0


def _version(learner): return hashlib.sha256(f'{learner.theta:.12g}/{learner.updates}'.encode()).hexdigest()[:16]
def _key(learner): return f'policy={_version(learner)}/response=h1'
def _step(env,learner,measurement):
    reward=1.0 if measurement else 0.2
    action_effect=1.0 if measurement else 0.0
    env.state['x']+=action_effect
    learner.theta += 0.25*(reward-learner.theta); learner.updates+=1

def _target(env,learner):
    # Deliberately policy-dependent target to test target-version plumbing.
    return float(1.0/(1.0+np.exp(-learner.theta)))

def run():
    out=paired_shadow_experiment(environment=ToyEnv(),learner=ToyLearner(),policy_version=_version,estimand_key=_key,step_branch=_step,measure_target=_target)
    return {'protocol_version':PROTOCOL_VERSION,'development_only':True,'evidence_class':'PLUMBING_SMOKE_ONLY','no_measurement_target':out.no_measurement_target,'measurement_target':out.measurement_target,'target_drift':out.target_drift,'target_key_changed':out.target_key_changed,'gate_pass':bool(out.target_drift>0 and out.target_key_changed),'limitation':'This proves paired-shadow plumbing only. A learned CIG-AMF learner adapter is still required for F3 scientific experiments.'}

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--out',default='research/new_chains_v2/chain_f3/summary.json'); a=p.parse_args(argv); payload=run(); atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0 if payload['gate_pass'] else 2
if __name__=='__main__': raise SystemExit(main())
