"""Multi-seed D6 active-cell discovery with fail-closed exact-counterexample handling."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from research_chains.d6_active_cell_lp import discover_active_cells
from research_chains.provenance import write_artifact_with_provenance
from utils.debug_trace import DebugTrace

PROTOCOL_VERSION = "d6_active_cell_lp_multiseed_v1"


def run(args) -> dict:
    rows = []
    exact_counterexamples = []
    trace = DebugTrace(Path(args.trace_out), enabled=bool(args.debug), run_id="d6-lp-sweep")
    for seed in args.seeds:
        for offset, m in enumerate(args.m_values):
            run_seed = int(seed) + 1009 * offset
            trace.event("d6.sweep.start", seed=int(seed), run_seed=run_seed, m=int(m))
            row = discover_active_cells(
                int(m),
                seed=run_seed,
                restarts=int(args.restarts),
                closure_steps=int(args.closure_steps),
                reference_modes=tuple(args.reference_modes),
                dual_tol=float(args.dual_tol),
                trace=trace,
                search_encoding=args.search_encoding,
                refine_top=int(args.refine_top),
                topc_margin=float(args.topc_margin),
                random_reference_denominator=int(args.random_reference_denominator),
                mutation_trials=int(args.mutation_trials),
                mutation_scale=float(args.mutation_scale),
                mutation_elites=int(args.mutation_elites),
            )
            rows.append({"base_seed": int(seed), "run_seed": run_seed, **row})
            if row["exact_counterexample_verified"]:
                exact_counterexamples.append(rows[-1])
            trace.event(
                "d6.sweep.end", seed=int(seed), m=int(m), max_gamma=row["max_gamma"],
                exact_counterexample=row["exact_counterexample_verified"],
            )
            if exact_counterexamples and args.fail_on_counterexample:
                break
        if exact_counterexamples and args.fail_on_counterexample:
            break

    maxima = {}
    for m in args.m_values:
        candidates = [r for r in rows if int(r["m"]) == int(m) and r["max_gamma"] is not None]
        maxima[str(int(m))] = None if not candidates else max(candidates, key=lambda r: float(r["max_gamma"]))
    result = {
        "protocol_version": PROTOCOL_VERSION,
        "development_only": True,
        "seeds": list(map(int, args.seeds)),
        "m_values": list(map(int, args.m_values)),
        "reference_modes": list(args.reference_modes),
        "rows": rows,
        "best_by_m": maxima,
        "observed_pattern": [None if maxima[str(int(m))] is None else maxima[str(int(m))]["max_gamma"] for m in args.m_values],
        "target_pattern": [int(m) - 1 for m in args.m_values],
        "any_numerical_candidate": any(r["numerical_counterexample_candidate"] for r in rows),
        "any_exact_counterexample": bool(exact_counterexamples),
        "exact_counterexamples": exact_counterexamples,
        "scope": "multi-seed development discovery; sampled cells are not an exhaustive proof",
    }
    write_artifact_with_provenance(
        Path(args.out), result,
        protocol={
            "protocol_version": PROTOCOL_VERSION,
            "seeds": list(map(int, args.seeds)),
            "m_values": list(map(int, args.m_values)),
            "restarts": int(args.restarts),
            "closure_steps": int(args.closure_steps),
            "reference_modes": list(args.reference_modes),
            "refine_top": int(args.refine_top),
            "topc_margin": float(args.topc_margin),
            "random_reference_denominator": int(args.random_reference_denominator),
            "mutation_trials": int(args.mutation_trials),
            "mutation_scale": float(args.mutation_scale),
            "mutation_elites": int(args.mutation_elites),
        },
        seed=int(args.seeds[0]) if args.seeds else None,
        evidence_class="DEVELOPMENT_EXACT_LP_DISCOVERY_MULTI_SEED",
        chain="D6",
    )
    return result


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--m-values", nargs="+", type=int, default=[4, 6, 8])
    p.add_argument("--seeds", nargs="+", type=int, default=[20260902, 701, 709, 719, 727])
    p.add_argument("--restarts", type=int, default=24)
    p.add_argument("--closure-steps", type=int, default=8)
    p.add_argument("--reference-modes", nargs="+", default=["uniform", "point0", "point1", "random"])
    p.add_argument("--dual-tol", type=float, default=1e-8)
    p.add_argument("--search-encoding", choices=["range", "pairwise"], default="range")
    p.add_argument("--refine-top", type=int, default=4)
    p.add_argument("--topc-margin", type=float, default=0.0)
    p.add_argument("--random-reference-denominator", type=int, default=100)
    p.add_argument("--mutation-trials", type=int, default=4)
    p.add_argument("--mutation-scale", type=float, default=0.05)
    p.add_argument("--mutation-elites", type=int, default=4)
    p.add_argument("--out", default="research/d6_active_cell_lp/sweep.json")
    p.add_argument("--debug", action="store_true")
    p.add_argument("--trace-out", default="research/d6_active_cell_lp/sweep_debug_trace.jsonl")
    p.add_argument("--fail-on-counterexample", action="store_true")
    args = p.parse_args(argv)
    result = run(args)
    print(json.dumps({
        "protocol_version": result["protocol_version"],
        "observed_pattern": result["observed_pattern"],
        "target_pattern": result["target_pattern"],
        "any_numerical_candidate": result["any_numerical_candidate"],
        "any_exact_counterexample": result["any_exact_counterexample"],
        "out": args.out,
    }, indent=2))
    return 2 if result["any_exact_counterexample"] and args.fail_on_counterexample else 0


if __name__ == "__main__":
    raise SystemExit(main())
