"""Run static and optional managed-runtime capability audits for adapters."""
from __future__ import annotations
import argparse, json
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path: sys.path.insert(0,str(ROOT))

from envs.external.capability_audit import audit_environment
from research_chains.provenance import atomic_json
from envs.external.runtime import maybe_reexec_in_external_runtime


def run(keys, *, runtime=False, seed=0, max_cells=256):
    rows = {}
    for key in keys:
        env = None
        if runtime and key != "omni":
            from envs.external.registry import build_environment
            env = build_environment(key, seed=int(seed))
        elif runtime and key == "omni":
            from envs.omni_arena import OmniArena
            env = OmniArena(n_agents=8, n_zones=1, max_steps=64, phase_length=1000, enable_structural_shift=False, seed=int(seed))
            env.reset()
        rows[key] = audit_environment(key, env=env, max_cells=max_cells)
    return {"protocol_version":"adapter_capability_audit_v1", "runtime_requested":bool(runtime), "seed":int(seed), "adapters":rows}


def main(argv=None):
    p=argparse.ArgumentParser()
    p.add_argument('--adapters', nargs='+', default=['omni','rware','flatland','cyborg','cityflow'])
    p.add_argument('--runtime', action='store_true')
    p.add_argument('--seed', type=int, default=3001)
    p.add_argument('--max-cells', type=int, default=256)
    p.add_argument('--out', default='research/external/ADAPTER_CAPABILITY_AUDIT.json')
    a=p.parse_args(argv)
    if a.runtime and any(key != 'omni' for key in a.adapters):
        maybe_reexec_in_external_runtime(require_ready=True)
    payload=run(a.adapters,runtime=a.runtime,seed=a.seed,max_cells=a.max_cells)
    atomic_json(Path(a.out),payload); print(json.dumps(payload,indent=2)); return 0
if __name__=='__main__': raise SystemExit(main())
