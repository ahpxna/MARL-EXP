"""Run sparse active-cell LP discovery for m=4,6,8 and save dual diagnostics."""
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

PROTOCOL_VERSION = "d6_active_cell_lp_discovery_v2"


def run(args) -> dict:
    trace = DebugTrace(Path(args.trace_out), enabled=bool(args.debug), run_id=f"d6-lp-{args.seed}")
    rows = []
    for offset, m in enumerate(args.m_values):
        trace.event("d6.dimension.start", m=int(m))
        row = discover_active_cells(
            int(m),
            seed=int(args.seed) + 1009 * offset,
            restarts=int(args.restarts),
            closure_steps=int(args.closure_steps),
            reference_modes=tuple(args.reference_modes),
            dual_tol=float(args.dual_tol),
            trace=trace,
            dump_dir=Path(args.dump_dir) if args.dump_matrices else None,
            search_encoding=args.search_encoding,
            refine_top=args.refine_top,
            topc_margin=args.topc_margin,
            random_reference_denominator=args.random_reference_denominator,
            mutation_trials=args.mutation_trials,
            mutation_scale=args.mutation_scale,
            mutation_elites=args.mutation_elites,
        )
        rows.append(row)
        trace.event("d6.dimension.end", m=int(m), max_gamma=row["max_gamma"], max_violation=row["max_violation"])
        if row["counterexample_found"] and args.fail_on_counterexample:
            break
    gammas = [r["max_gamma"] for r in rows]
    targets = [r["target_m_minus_1"] for r in rows]
    result = {
        "protocol_version": PROTOCOL_VERSION,
        "development_only": True,
        "seed": int(args.seed),
        "dimensions": rows,
        "observed_max_gammas": gammas,
        "targets": targets,
        "observed_pattern": [None if g is None else round(float(g), 10) for g in gammas],
        "target_pattern": targets,
        "all_observed_match_targets": bool(len(rows) == len(args.m_values) and all(r["pattern_match"] for r in rows)),
        "any_counterexample": bool(any(r["counterexample_found"] for r in rows)),
        "interpretation": "3,5,7 across m=4,6,8 is structural evidence for Lean discovery, not a proof. Floating Gamma>m-1 is only a numerical candidate; counterexample_found is true only after the independent rational verifier confirms it under the requested Top-C margin.",
    }
    out = Path(args.out)
    write_artifact_with_provenance(
        out,
        result,
        protocol={
            "protocol_version": PROTOCOL_VERSION,
            "m_values": list(map(int, args.m_values)),
            "restarts": int(args.restarts),
            "closure_steps": int(args.closure_steps),
            "reference_modes": list(args.reference_modes),
            "dual_tol": float(args.dual_tol),
            "search_encoding": str(args.search_encoding),
            "refine_top": int(args.refine_top),
            "topc_margin": float(args.topc_margin),
            "random_reference_denominator": int(args.random_reference_denominator),
            "mutation_trials": int(args.mutation_trials),
            "mutation_scale": float(args.mutation_scale),
            "mutation_elites": int(args.mutation_elites),
        },
        seed=int(args.seed),
        evidence_class="DEVELOPMENT_EXACT_LP_DISCOVERY",
        chain="D6",
    )
    return result


def main(argv=None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--m-values", nargs="+", type=int, default=[4, 6, 8])
    p.add_argument("--seed", type=int, default=20260902)
    p.add_argument("--restarts", type=int, default=6)
    p.add_argument("--closure-steps", type=int, default=4)
    p.add_argument("--reference-modes", nargs="+", default=["uniform", "point0"])
    p.add_argument("--dual-tol", type=float, default=1e-8)
    p.add_argument("--search-encoding", choices=["range", "pairwise"], default="range")
    p.add_argument("--refine-top", type=int, default=3)
    p.add_argument("--topc-margin", type=float, default=0.0, help="debug stress test; 0 matches non-strict Lean Top-C")
    p.add_argument("--random-reference-denominator", type=int, default=100, help="rational grid denominator for exact random q reconstruction")
    p.add_argument("--mutation-trials", type=int, default=4, help="local selector-neighbour trials around each closure fixed point")
    p.add_argument("--mutation-scale", type=float, default=0.05, help="maximum Gaussian scale for elite cell-neighbour search")
    p.add_argument("--mutation-elites", type=int, default=4, help="number of highest-Gamma cells used as mutation parents")
    p.add_argument("--out", default="research/d6_active_cell_lp/discovery.json")
    p.add_argument("--debug", action="store_true")
    p.add_argument("--trace-out", default="research/d6_active_cell_lp/debug_trace.jsonl")
    p.add_argument("--dump-matrices", action="store_true")
    p.add_argument("--dump-dir", default="research/d6_active_cell_lp/matrices")
    p.add_argument("--fail-on-counterexample", action="store_true")
    args = p.parse_args(argv)
    result = run(args)
    print(json.dumps(result, indent=2))
    return 2 if result["any_counterexample"] and args.fail_on_counterexample else 0


if __name__ == "__main__":
    raise SystemExit(main())
