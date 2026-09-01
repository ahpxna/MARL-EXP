"""Proposal-registry coverage helpers.

The high-value suite is intentionally only one orchestration surface.  A clean
suite must never be reported as evidence that every registered proposal has
been executed, because several confirmatory/external/P13 falsification runners
live outside it.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Iterable


HIGH_VALUE_SUITE_RUNNERS = frozenset({
    "scripts.run_master_extension_lab",
    "scripts.run_functional_design_extension_lab",
    "scripts.run_query_optimal_allocation_lab",
    "scripts.run_functional_stopping_lab",
    "scripts.run_d6_extension_lab",
    "scripts.run_query_extension_lab",
    "scripts.run_structural_defect_lab",
    "scripts.run_dynamic_extension_lab",
    "scripts.run_chain_bh_lab",
    "scripts.run_chain_rp_lab",
    "scripts.run_chain_reference_fidelity_search",
    "scripts.run_chain_e_semantic_lab",
})


def load_registry(path: str | Path) -> dict:
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    items = payload.get("items")
    if not isinstance(items, list):
        raise ValueError("proposal registry must contain an items list")
    ids = [str(item["proposal_id"]) for item in items]
    if len(ids) != len(set(ids)):
        raise ValueError("proposal registry contains duplicate proposal_id values")
    return payload


def runner_coverage(registry: dict, runner_modules: Iterable[str]) -> dict:
    runner_modules = {str(x) for x in runner_modules}
    items = registry["items"]
    covered = sorted(str(item["proposal_id"]) for item in items if str(item.get("runner")) in runner_modules)
    outside = sorted(str(item["proposal_id"]) for item in items if str(item.get("runner")) not in runner_modules)
    return {
        "scope": "runner membership in this orchestration surface; outside-suite does not imply missing independent evidence",
        "registry_proposal_count": int(len(items)),
        "covered_by_suite_count": int(len(covered)),
        "outside_suite_count": int(len(outside)),
        "covered_by_suite_ids": covered,
        "outside_suite_ids": outside,
        "all_registry_proposals_covered_by_suite": bool(not outside),
        "suite_runner_modules": sorted(runner_modules),
    }
