"""Fail-closed disjoint-seed replication of the frozen V7 fixed-panel protocol."""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from research_chains.provenance import atomic_json
from scripts import run_h1_fixed_panel_v7 as v7

PROTOCOL_VERSION = "h1_fixed_panel_confirmatory_v2"
DEV_SEEDS = {3001, 3002, 3003, 3004, 3005}
FROZEN = {
    "checkpoints": [20, 80, 320],
    "tiny_states": 24,
    "max_steps": 30,
    "phase_length": 40,
    "reference_train_episodes": 1,
    "panel_seed_offset": 700000,
}


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--seeds", nargs="+", type=int, default=list(range(5001, 5021)))
    p.add_argument("--device", default="cpu")
    p.add_argument("--out-root", default=str(ROOT / "research" / "confirmatory_functional"))
    p.add_argument("--dry-run", action="store_true")
    p.add_argument("--quiet", action="store_true")
    a = p.parse_args(argv)
    seeds = [int(x) for x in a.seeds]
    if DEV_SEEDS & set(seeds):
        p.error("confirmatory seeds overlap V7 development seeds 3001-3005")
    if len(set(seeds)) != len(seeds) or len(seeds) < 10:
        p.error("use at least 10 unique disjoint confirmatory seeds")

    protocol = {
        "protocol_version": PROTOCOL_VERSION,
        "underlying_v7_protocol": v7.V7_PROTOCOL,
        "frozen": FROZEN,
        "seeds": seeds,
        "development_seeds": sorted(DEV_SEEDS),
        "development_seed_overlap": False,
        "seed_is_inference_unit": True,
        "no_tuning_after_results": True,
    }
    out = Path(a.out_root)
    out.mkdir(parents=True, exist_ok=True)
    atomic_json(out / "CONFIRMATORY_PROTOCOL.json", protocol)

    args = [
        "--seeds", *map(str, seeds),
        "--checkpoints", *map(str, FROZEN["checkpoints"]),
        "--device", a.device,
        "--tiny-states", str(FROZEN["tiny_states"]),
        "--max-steps", str(FROZEN["max_steps"]),
        "--phase-length", str(FROZEN["phase_length"]),
        "--reference-train-episodes", str(FROZEN["reference_train_episodes"]),
        "--panel-seed-offset", str(FROZEN["panel_seed_offset"]),
        "--out-root", str(out),
    ]
    if a.quiet:
        args.append("--quiet")
    if a.dry_run:
        print(json.dumps({
            "protocol": protocol,
            "command": ["python", "-m", "scripts.run_h1_fixed_panel_v7", *args],
        }, indent=2))
        return 0
    rc = int(v7.main(args) or 0)
    if rc == 0:
        atomic_json(out / "CONFIRMATORY_RUN_COMPLETE.json", {
            "protocol_version": PROTOCOL_VERSION,
            "seeds": seeds,
            "checkpoints": FROZEN["checkpoints"],
            "run_completed": True,
        })
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
