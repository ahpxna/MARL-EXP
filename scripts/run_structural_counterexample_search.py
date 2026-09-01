"""Exact-small and directed falsification for the final Structural defect.

The open candidate is

    best all-budget nested-prefix regret <= m * all-optimal-extension defect.

This runner is a falsifier, never a proof.  Exact mode enumerates every binary
m=3 support with full coordinate projections and every +/- unit primitive
orientation.  Directed mode mutates binary supports and integer primitive
slopes to maximize the candidate violation for m=4/5/6.
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import numpy as np

from research_chains.experimental_extensions import (
    all_optimal_extension_defect,
    best_nested_prefix_regret,
)
from research_chains.finite_world import FiniteResponseWorld
from research_chains.provenance import atomic_json
from research_chains.support import SupportModel

PROTOCOL_VERSION = "structural_counterexample_search_v1"


def _world(m: int, omega, slopes) -> FiniteResponseWorld:
    support = SupportModel((2,) * m, tuple(sorted(omega)), key="structural-search")
    primitives = tuple(np.asarray([0.0, float(s)]) for s in slopes)
    return FiniteResponseWorld(support, primitives)


def _full_projection(omega, m: int) -> bool:
    return bool(omega) and all({a[j] for a in omega} == {0, 1} for j in range(m))


def _evaluate(world: FiniteResponseWorld) -> dict:
    nested = best_nested_prefix_regret(world)
    defect = all_optimal_extension_defect(world, nested)
    return {
        "best_nested_max_regret": float(nested["best_nested_max_regret"]),
        "all_optimal_extension_defect": float(defect["all_optimal_extension_defect"]),
        "m_times_defect": float(defect["m_times_defect"]),
        "candidate_violation": float(defect["candidate_violation"]),
        "best_nested_order": nested["best_nested_order"],
        "best_nested_per_budget": nested["best_nested_per_budget"],
    }


def exact_m3() -> dict:
    m = 3
    actions = tuple(itertools.product((0, 1), repeat=m))
    checked = 0
    worst = None
    for mask in range(1, 1 << len(actions)):
        omega = tuple(actions[i] for i in range(len(actions)) if mask & (1 << i))
        if not _full_projection(omega, m):
            continue
        for slopes in itertools.product((-1, 1), repeat=m):
            row = _evaluate(_world(m, omega, slopes))
            checked += 1
            candidate = {**row, "omega": [list(a) for a in omega], "slopes": list(slopes)}
            if worst is None or candidate["candidate_violation"] > worst["candidate_violation"]:
                worst = candidate
    return {
        "mode": "exact_m3_binary_unit_slopes",
        "worlds_checked": checked,
        "candidate_killed": bool(worst and worst["candidate_violation"] > 1e-12),
        "worst_witness": worst,
    }


def _repair(mask: np.ndarray, rng: np.random.Generator, actions, m: int) -> np.ndarray:
    mask = mask.copy()
    if not np.any(mask):
        mask[int(rng.integers(0, len(actions)))] = True
    for j in range(m):
        for value in (0, 1):
            if not any(mask[i] and actions[i][j] == value for i in range(len(actions))):
                choices = [i for i, a in enumerate(actions) if a[j] == value]
                mask[int(rng.choice(choices))] = True
    return mask


def directed(m: int, restarts: int, steps: int, seed: int) -> dict:
    rng = np.random.default_rng(seed)
    actions = tuple(itertools.product((0, 1), repeat=m))
    best = None
    killed = False
    for _ in range(restarts):
        mask = _repair(rng.random(len(actions)) < rng.uniform(0.15, 0.85), rng, actions, m)
        slopes = rng.choice((-3, -2, -1, 1, 2, 3), size=m)
        omega = tuple(actions[i] for i in range(len(actions)) if mask[i])
        row = _evaluate(_world(m, omega, slopes))
        score = row["candidate_violation"]
        temperature = 0.5
        for _step in range(steps):
            proposed_mask = mask.copy()
            proposed_slopes = slopes.copy()
            if rng.random() < 0.7:
                idx = int(rng.integers(0, len(actions)))
                proposed_mask[idx] = ~proposed_mask[idx]
                proposed_mask = _repair(proposed_mask, rng, actions, m)
            else:
                j = int(rng.integers(0, m))
                proposed_slopes[j] = int(rng.choice((-4, -3, -2, -1, 1, 2, 3, 4)))
            proposed_omega = tuple(actions[i] for i in range(len(actions)) if proposed_mask[i])
            proposed = _evaluate(_world(m, proposed_omega, proposed_slopes))
            proposed_score = proposed["candidate_violation"]
            accept = proposed_score >= score or rng.random() < math.exp(
                (proposed_score - score) / max(temperature, 1e-9)
            )
            if accept:
                mask, slopes, omega, row, score = (
                    proposed_mask,
                    proposed_slopes,
                    proposed_omega,
                    proposed,
                    proposed_score,
                )
            temperature *= 0.99
            witness = {**row, "omega": [list(a) for a in omega], "slopes": slopes.tolist()}
            if best is None or witness["candidate_violation"] > best["candidate_violation"]:
                best = witness
            if score > 1e-10:
                killed = True
                break
        if killed:
            break
    return {
        "mode": "directed_binary_support_integer_slopes",
        "m": m,
        "restarts_requested": restarts,
        "steps_per_restart": steps,
        "seed": seed,
        "candidate_killed": killed,
        "best_witness": best,
    }


def run(mode="all", restarts=1000, steps=200, seed=0):
    results = {}
    if mode in {"all", "exact"}:
        results["exact_m3"] = exact_m3()
    if mode in {"all", "directed"}:
        results["directed"] = [directed(m, restarts, steps, seed + m) for m in (4, 5, 6)]
    result_rows = ([results["exact_m3"]] if "exact_m3" in results else []) + results.get("directed", [])
    killed = any(bool(row.get("candidate_killed")) for row in result_rows)
    return {
        "protocol_version": PROTOCOL_VERSION,
        "evidence_class": "EXACT_SMALL_AND_DIRECTED_FALSIFICATION_NOT_PROOF",
        "candidate": "best_nested_max_regret <= m * all_optimal_extension_defect",
        "candidate_killed": bool(killed),
        "results": results,
    }


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--mode", choices=("all", "exact", "directed"), default="all")
    p.add_argument("--restarts", type=int, default=1000)
    p.add_argument("--steps", type=int, default=200)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--out", default="research/high_value_extensions/structural/counterexample_search.json")
    a = p.parse_args(argv)
    payload = run(a.mode, a.restarts, a.steps, a.seed)
    atomic_json(Path(a.out), payload)
    print(json.dumps(payload, indent=2))
    return 2 if payload["candidate_killed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
