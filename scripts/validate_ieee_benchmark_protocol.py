"""Validate the frozen three-tier benchmark/statistics/ablation contract."""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--protocol", default="config/ieee_benchmark_protocol_v1.json")
    args = p.parse_args(argv)
    path = Path(args.protocol)
    data = json.loads(path.read_text(encoding="utf-8"))
    errors = []
    stats = data.get("statistics", {})
    seeds = stats.get("confirmatory_seeds", [])
    if stats.get("confirmatory_seed_count") != len(seeds):
        errors.append("confirmatory_seed_count does not match frozen seed list")
    if len(set(seeds)) != len(seeds):
        errors.append("confirmatory seeds are not unique")
    if not stats.get("false_safe_rate_required_for_certificate_methods", False):
        errors.append("false-safe rate must be required for certificate methods")
    for tier in ("A", "B", "C"):
        if tier not in data.get("tiers", {}):
            errors.append(f"missing tier {tier}")
    required_ablations = {
        "D6": "certificate_driven_adaptive_order",
        "STRUCTURAL": "prefix_consistency_on",
        "MASTER": "remove_interaction",
    }
    for chain, item in required_ablations.items():
        if item not in data.get("ablations", {}).get(chain, []):
            errors.append(f"missing {chain} ablation {item}")
    print(json.dumps({"protocol": str(path), "valid": not errors, "errors": errors}, indent=2))
    return 0 if not errors else 2


if __name__ == "__main__":
    raise SystemExit(main())
