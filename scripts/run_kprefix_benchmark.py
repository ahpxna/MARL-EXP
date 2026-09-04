"""Tier-A K-Prefix benchmark: exact, greedy COVER-RANK, and KPrefixNet.

Outputs one JSON artifact plus plots of K against worst/mean budget regret,
inference/solve time, and memory.  Policy return is explicitly unavailable in
Tier A; Tier B/C adapters can add it without pretending a finite-objective
proxy is an RL return.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time

import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.finite_world import FiniteResponseWorld
from research_chains.support import SupportModel
from research_chains.kprefix import (
    dense_subset_objective,
    epsilon_k_exact,
    epsilon_k_greedy,
    estimate_menu_memory_bytes,
    structural_world_features,
)
from research_chains.kprefix_deep import KPrefixInstance, train_kprefix_net, evaluate_kprefix_net
from research_chains.provenance import write_artifact_with_provenance
from utils.debug_trace import DebugTrace
from utils.experiment_protocol import summarize_replicates

PROTOCOL_VERSION = "kprefix_three_level_tierA_v1"


def random_supportosc_world(rng: np.random.Generator, m: int) -> FiniteResponseWorld:
    sizes = (2,) * int(m)
    full = list(np.ndindex(*sizes))
    density = float(rng.uniform(0.20, 0.85))
    omega = [a for a in full if rng.random() < density]
    if not omega:
        omega = [full[0]]
    # Preserve both actions in every marginal so score spans remain meaningful.
    for j in range(m):
        for u in (0, 1):
            if not any(a[j] == u for a in omega):
                omega.append(next(a for a in full if a[j] == u))
    primitives = tuple(
        np.asarray([0.0, float(rng.choice([-5, -4, -3, -2, -1, 1, 2, 3, 4, 5]))], dtype=np.float64)
        for _ in range(m)
    )
    return FiniteResponseWorld(
        SupportModel(sizes, tuple(sorted(set(omega))), key="kprefix_benchmark"),
        primitives,
    )


def _aggregate_method(rows: list[dict], confidence: float) -> dict:
    return {
        "epsilon_K": summarize_replicates([r["epsilon_K"] for r in rows], confidence),
        "worst_budget_regret": summarize_replicates([r["metrics"]["worst_budget_regret"] for r in rows], confidence),
        "mean_budget_regret": summarize_replicates([r["metrics"]["mean_budget_regret"] for r in rows], confidence),
        "inference_or_solve_seconds": summarize_replicates([r["solve_seconds"] for r in rows], confidence),
        "memory_bytes": summarize_replicates([r["memory_bytes"] for r in rows], confidence),
        "policy_return": None,
        "policy_return_status": "NOT_AVAILABLE_IN_TIER_A_FINITE_WORLD",
    }


def _plot_metric(result: dict, metric: str, outdir: Path) -> str:
    fig, ax = plt.subplots(figsize=(7, 4.5))
    ks = [int(k) for k in result["K_values"]]
    for method in ("exact", "greedy", "deep"):
        ys = []
        for k in ks:
            block = result["by_K"][str(k)][method]
            if method == "deep":
                if metric == "worst_budget_regret":
                    ys.append(block["worst_budget_regret_mean"])
                elif metric == "mean_budget_regret":
                    ys.append(block["mean_budget_regret_mean"])
                elif metric == "inference_or_solve_seconds":
                    ys.append(block["inference_seconds_mean"])
                elif metric == "memory_bytes":
                    ys.append(block["memory_bytes"])
                else:
                    raise KeyError(metric)
            else:
                ys.append(block[metric]["mean"])
        ax.plot(ks, ys, marker="o", label=method)
    ax.set_xlabel("K rankings")
    ax.set_ylabel(metric.replace("_", " "))
    ax.set_title(f"K-Prefix Tier-A: {metric.replace('_', ' ')}")
    ax.grid(True, alpha=0.25)
    ax.legend()
    fig.tight_layout()
    path = outdir / f"kprefix_{metric}.png"
    fig.savefig(path, dpi=170)
    plt.close(fig)
    return str(path)


def run(args) -> dict:
    rng = np.random.default_rng(int(args.seed))
    trace = DebugTrace(Path(args.trace_out), enabled=bool(args.debug), run_id=f"kprefix-{args.seed}")
    train_worlds = [random_supportosc_world(rng, args.m) for _ in range(args.train_instances)]
    test_worlds = [random_supportosc_world(rng, args.m) for _ in range(args.test_instances)]
    train_instances = [
        KPrefixInstance(structural_world_features(w), dense_subset_objective(w), args.m)
        for w in train_worlds
    ]
    test_instances = [
        KPrefixInstance(structural_world_features(w), dense_subset_objective(w), args.m)
        for w in test_worlds
    ]
    by_k = {}
    for K in range(1, int(args.k_max) + 1):
        trace.event("kprefix.K.start", K=K, m=args.m)
        exact_rows = []
        greedy_rows = []
        for idx, inst in enumerate(test_instances):
            t0 = time.perf_counter()
            exact = epsilon_k_exact(inst.values, inst.m, K, verify_milp=bool(args.verify_milp))
            exact["solve_seconds"] = float(time.perf_counter() - t0)
            exact["memory_bytes"] = estimate_menu_memory_bytes(exact["rankings"])
            exact_rows.append(exact)
            t0 = time.perf_counter()
            greedy = epsilon_k_greedy(inst.values, inst.m, K)
            greedy["solve_seconds"] = float(time.perf_counter() - t0)
            greedy["memory_bytes"] = estimate_menu_memory_bytes(greedy["rankings"])
            greedy_rows.append(greedy)
            if args.debug:
                trace.event(
                    "kprefix.instance",
                    K=K,
                    instance=idx,
                    exact_epsilon=exact["epsilon_K"],
                    greedy_epsilon=greedy["epsilon_K"],
                )

        model, train_diag = train_kprefix_net(
            train_instances,
            K=K,
            epochs=args.epochs,
            lr=args.lr,
            hidden_dim=args.hidden_dim,
            entropy_weight=args.entropy_weight,
            seed=args.seed + 97 * K,
            device=args.device,
        )
        deep_eval = evaluate_kprefix_net(model, test_instances, device=args.device)
        by_k[str(K)] = {
            "exact": _aggregate_method(exact_rows, args.confidence),
            "greedy": _aggregate_method(greedy_rows, args.confidence),
            "deep": deep_eval,
            "deep_training": train_diag,
            "raw_exact": exact_rows if args.include_raw else None,
            "raw_greedy": greedy_rows if args.include_raw else None,
        }
        trace.event(
            "kprefix.K.end",
            K=K,
            exact_worst=by_k[str(K)]["exact"]["worst_budget_regret"]["mean"],
            greedy_worst=by_k[str(K)]["greedy"]["worst_budget_regret"]["mean"],
            deep_worst=deep_eval["worst_budget_regret_mean"],
        )

    outdir = Path(args.plot_dir); outdir.mkdir(parents=True, exist_ok=True)
    result = {
        "protocol_version": PROTOCOL_VERSION,
        "development_only": True,
        "tier": "A_EXACT_FINITE",
        "m": int(args.m),
        "K_values": list(range(1, int(args.k_max) + 1)),
        "seed": int(args.seed),
        "train_instances": int(args.train_instances),
        "test_instances": int(args.test_instances),
        "confidence": float(args.confidence),
        "by_K": by_k,
        "false_safe_rate": None,
        "false_safe_status": "NOT_APPLICABLE_STRUCTURAL_NONCERTIFICATE_BENCHMARK",
        "policy_return": None,
        "policy_return_status": "DEFERRED_TO_TIER_B_C_MARL_ADAPTERS",
        "plots": {},
    }
    for metric in ("worst_budget_regret", "mean_budget_regret", "inference_or_solve_seconds", "memory_bytes"):
        result["plots"][metric] = _plot_metric(result, metric, outdir)
    write_artifact_with_provenance(
        Path(args.out),
        result,
        protocol={
            "protocol_version": PROTOCOL_VERSION,
            "m": args.m,
            "K_values": result["K_values"],
            "train_instances": args.train_instances,
            "test_instances": args.test_instances,
            "epochs": args.epochs,
            "confidence": args.confidence,
        },
        seed=args.seed,
        evidence_class="DEVELOPMENT_TIER_A_ALGORITHM_BENCHMARK",
        chain="STRUCTURAL",
    )
    return result


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--m", type=int, default=6)
    p.add_argument("--k-max", type=int, default=4)
    p.add_argument("--train-instances", type=int, default=32)
    p.add_argument("--test-instances", type=int, default=12)
    p.add_argument("--epochs", type=int, default=120)
    p.add_argument("--lr", type=float, default=3e-3)
    p.add_argument("--hidden-dim", type=int, default=128)
    p.add_argument("--entropy-weight", type=float, default=1e-3)
    p.add_argument("--device", default="cpu")
    p.add_argument("--seed", type=int, default=20260902)
    p.add_argument("--confidence", type=float, default=0.95)
    p.add_argument("--verify-milp", action="store_true")
    p.add_argument("--include-raw", action="store_true")
    p.add_argument("--out", default="research/kprefix/benchmark.json")
    p.add_argument("--plot-dir", default="research/kprefix/plots")
    p.add_argument("--debug", action="store_true")
    p.add_argument("--trace-out", default="research/kprefix/debug_trace.jsonl")
    args = p.parse_args(argv)
    result = run(args)
    print(json.dumps({
        "protocol_version": result["protocol_version"],
        "tier": result["tier"],
        "m": result["m"],
        "K_values": result["K_values"],
        "out": args.out,
        "plots": result["plots"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
