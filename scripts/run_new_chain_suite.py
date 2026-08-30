"""One development-only entry point for cheap post-Round-10 chain blockers."""
from __future__ import annotations

# Allow both `python -m scripts.<runner>` and direct `python scripts/<runner>.py`.
import sys
from pathlib import Path as _BootstrapPath
_REPO_ROOT = _BootstrapPath(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))
import argparse, json
from pathlib import Path
from scripts.run_chain_bh_lab import run as run_bh
from scripts.run_chain_rp_lab import run as run_rp
from scripts.run_chain_a_functional_lab import run as run_a
from scripts.run_chain_structural_search import run as run_struct
from scripts.run_chain_reference_fidelity_search import run as run_ref
from scripts.run_chain_e_semantic_lab import run as run_e
from scripts.run_chain_f3_shadow_smoke import run as run_f3
from research_chains.provenance import atomic_json

PROTOCOL_VERSION='new_chain_suite_v2'

def main(argv=None):
    p=argparse.ArgumentParser(); p.add_argument('--quick',action='store_true'); p.add_argument('--seed',type=int,default=0); p.add_argument('--out',default='research/new_chains_v2/suite_summary.json'); a=p.parse_args(argv)
    n=100 if a.quick else 1000; reps=300 if a.quick else 3000; worlds=500 if a.quick else 5000
    payload={'protocol_version':PROTOCOL_VERSION,'development_only':True,'bh':run_bh(n,a.seed),'rp':run_rp(n,a.seed+1),'a':run_a(reps,a.seed+2,8,40),'structural':run_struct('quick',a.seed+3,worlds),'reference_fidelity':run_ref(max(200,n*2),a.seed+4),'query_semantics':run_e(),'f3_shadow':run_f3()}
    payload['hard_failure']=bool(payload['bh']['failure_count'] or payload['rp']['failure_count'] or payload['reference_fidelity']['failure_count'] or payload['query_semantics']['overall_status']!='PASS' or not payload['f3_shadow']['gate_pass'])
    atomic_json(Path(a.out),payload); print(json.dumps({'out':str(Path(a.out).resolve()),'hard_failure':payload['hard_failure'],'bh_failures':payload['bh']['failure_count'],'rp_failures':payload['rp']['failure_count'],'structural_worlds':payload['structural']['processed_worlds']},indent=2)); return 2 if payload['hard_failure'] else 0
if __name__=='__main__': raise SystemExit(main())
