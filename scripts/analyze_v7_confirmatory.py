"""Seed-level confirmatory analysis for the frozen V7 two-margin replication.

This script does not tune thresholds or redefine endpoints.  Seed/run is the
independent inference unit.  It verifies protocol/completion first, then reports
paired 20->320 effects with bootstrap CIs and deterministic certificate gates.
"""
from __future__ import annotations
import argparse, json, sys
from pathlib import Path
import numpy as np
import pandas as pd
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from research_chains.provenance import atomic_json
from scripts.run_h1_fixed_panel_confirmatory import DEV_SEEDS, FROZEN, PROTOCOL_VERSION
from scripts.run_h1_fixed_panel_v7 import V7_PROTOCOL

METRICS = {
    "q_gauge_sup_error_median": "lower",
    "lambda_C_median_unique": "lower",
    "local_certified_fraction_unique": "higher",
    "local_extrema_swap_rate_unique": "lower",
    "capacity_mae": "lower",
    "topk_match_rate": "higher",
    "lambda_topk_Q_median": "lower",
    "strict_relation_pair_order_accuracy": "higher",
    "direction_sign_agreement": "higher",  # learned D-head metric
    "direction_sign_certified_fraction": "higher",
    "lambda_D_median": "lower",
}
VIOLATION_COLUMNS = [
    "capacity_q_error_bound_violation_count",
    "topk_q_certified_violation_count",
    "direction_sign_certified_violation_count",
    "local_theorem_violation_count",
]


def _load_json(path: Path):
    return json.loads(path.read_text()) if path.exists() else None


def _bootstrap_mean_ci(values, rng, reps=10000, alpha=.05):
    x = np.asarray(values, dtype=float)
    x = x[np.isfinite(x)]
    if not len(x):
        return {"n": 0, "mean": None, "median": None, "q25": None, "q75": None,
                "ci_low": None, "ci_high": None}
    if len(x) == 1:
        lo = hi = float(x[0])
    else:
        idx = rng.integers(0, len(x), size=(int(reps), len(x)))
        boot = x[idx].mean(axis=1)
        lo, hi = np.quantile(boot, [alpha / 2, 1 - alpha / 2])
    return {
        "n": int(len(x)), "mean": float(np.mean(x)), "median": float(np.median(x)),
        "q25": float(np.quantile(x, .25)), "q75": float(np.quantile(x, .75)),
        "ci_low": float(lo), "ci_high": float(hi),
    }


def analyze(root: Path, bootstrap_reps=10000, bootstrap_seed=20260830):
    protocol = _load_json(root / "CONFIRMATORY_PROTOCOL.json")
    manifest = _load_json(root / "v7_manifest.json")
    completion = _load_json(root / "v7_completion_status.json")
    hard = _load_json(root / "v7_hard_gates.json")
    panel_consistency = _load_json(root / "v7_panel_consistency.json")
    required = [protocol, manifest, completion, hard, panel_consistency]
    if any(x is None for x in required):
        missing = [n for n, x in zip(
            ["CONFIRMATORY_PROTOCOL.json", "v7_manifest.json", "v7_completion_status.json",
             "v7_hard_gates.json", "v7_panel_consistency.json"], required) if x is None]
        raise RuntimeError(f"missing confirmatory artifacts: {missing}")

    expected_seeds = [int(x) for x in protocol.get("seeds", [])]
    expected_cp = list(FROZEN["checkpoints"])
    protocol_ok = bool(
        protocol.get("protocol_version") == PROTOCOL_VERSION
        and protocol.get("underlying_v7_protocol") == V7_PROTOCOL
        and protocol.get("frozen") == FROZEN
        and not (set(expected_seeds) & DEV_SEEDS)
        and len(expected_seeds) >= 10
        and len(expected_seeds) == len(set(expected_seeds))
    )
    completion_ok = bool(
        sorted(map(int, completion.get("expected_seeds", []))) == sorted(expected_seeds)
        and sorted(map(int, completion.get("expected_checkpoints", []))) == expected_cp
        and not completion.get("incomplete_cells")
        and len(completion.get("completed_cells", [])) == len(expected_seeds) * len(expected_cp)
    )
    panel_ok = bool(panel_consistency.get("pass", False))
    hard_ok = bool(hard.get("all_deterministic_checks_pass", False))

    seed_path = root / "v7_seed_checkpoint_summary.csv"
    pair_path = root / "v7_pair_panel.csv"
    if not seed_path.exists() or not pair_path.exists():
        raise RuntimeError("missing v7_seed_checkpoint_summary.csv or v7_pair_panel.csv")
    seed_df = pd.read_csv(seed_path)
    pair_df = pd.read_csv(pair_path)
    got_grid = set(zip(seed_df["experiment_seed"].astype(int), seed_df["checkpoint"].astype(int)))
    exp_grid = {(s, c) for s in expected_seeds for c in expected_cp}
    grid_ok = got_grid == exp_grid and len(seed_df) == len(exp_grid)

    violations = {}
    for col in VIOLATION_COLUMNS:
        violations[col] = int(pd.to_numeric(seed_df[col], errors="coerce").fillna(0).sum()) if col in seed_df else None
    # Interval certificate violation is available at pair/state reporting level only through hard gates.
    violations["topk_interval_certificate_violation_count"] = int(hard.get("topk_interval_certificate_violation_count", -1))
    violation_free = all(v == 0 for v in violations.values() if v is not None)

    before = seed_df[seed_df.checkpoint == 20].set_index("experiment_seed")
    after = seed_df[seed_df.checkpoint == 320].set_index("experiment_seed")
    common = sorted(set(before.index) & set(after.index))
    if common != sorted(expected_seeds):
        raise RuntimeError("paired 20->320 seed grid incomplete")
    rng = np.random.default_rng(int(bootstrap_seed))
    rows = []
    result_metrics = {}
    for metric, preferred in METRICS.items():
        b = pd.to_numeric(before.loc[common, metric], errors="coerce").to_numpy(float)
        a = pd.to_numeric(after.loc[common, metric], errors="coerce").to_numpy(float)
        delta = a - b
        stats = _bootstrap_mean_ci(delta, rng, bootstrap_reps)
        stats.update({"metric": metric, "preferred_direction": preferred,
                      "before_mean": float(np.nanmean(b)), "after_mean": float(np.nanmean(a))})
        result_metrics[metric] = stats
        rows.append(stats)

    # Keep Q-derived sign diagnostic explicitly separate from learned D-head sign accuracy.
    q_sign_by_seed = None
    if "direction_sign_match_from_q" in pair_df.columns:
        tmp = (pair_df[pair_df["checkpoint"].isin([20, 320])]
               .groupby(["experiment_seed", "checkpoint"])["direction_sign_match_from_q"].mean().unstack())
        if 20 in tmp.columns and 320 in tmp.columns:
            q_delta = (tmp[320] - tmp[20]).reindex(expected_seeds).to_numpy(float)
            q_sign_by_seed = _bootstrap_mean_ci(q_delta, rng, bootstrap_reps)
            q_sign_by_seed.update({
                "metric": "direction_sign_match_from_q",
                "semantics": "Q-derived sign diagnostic; NOT learned D-head direction_sign_agreement",
                "before_mean": float(tmp[20].reindex(expected_seeds).mean()),
                "after_mean": float(tmp[320].reindex(expected_seeds).mean()),
            })

    gates = {
        "frozen_protocol": protocol_ok,
        "complete_seed_checkpoint_grid": completion_ok and grid_ok,
        "fixed_panel_invariance": panel_ok,
        "deterministic_hard_gates": hard_ok,
        "certificate_theorem_violations_zero": violation_free,
        "development_seed_overlap_zero": not bool(set(expected_seeds) & DEV_SEEDS),
        "minimum_confirmatory_seeds": len(expected_seeds) >= 10,
    }
    payload = {
        "schema": "v7_confirmatory_analysis_v1",
        "root": str(root), "seed_is_inference_unit": True,
        "n_seeds": len(expected_seeds), "seeds": expected_seeds,
        "checkpoints": expected_cp, "gates": gates,
        "all_integrity_gates_pass": bool(all(gates.values())),
        "violations": violations,
        "paired_20_to_320": result_metrics,
        "q_derived_direction_sign_20_to_320": q_sign_by_seed,
        "interpretation_guardrails": [
            "This is frozen confirmatory replication; do not tune definitions or thresholds after viewing results.",
            "Seed/run is the inference unit; row-level observations are not treated as independent replicates.",
            "direction_sign_agreement is the learned D-head metric; direction_sign_match_from_q is a distinct Q-derived diagnostic.",
            "Zero theorem violations establishes consistency of sufficient certificates, not certificate nonvacuity or universal converses.",
        ],
    }
    return payload, pd.DataFrame(rows)


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--root", default=str(ROOT / "research" / "confirmatory_functional"))
    p.add_argument("--bootstrap-reps", type=int, default=10000)
    p.add_argument("--bootstrap-seed", type=int, default=20260830)
    p.add_argument("--out", default=None)
    a = p.parse_args(argv)
    root = Path(a.root)
    payload, table = analyze(root, a.bootstrap_reps, a.bootstrap_seed)
    out = Path(a.out) if a.out else root / "CONFIRMATORY_ANALYSIS.json"
    atomic_json(out, payload)
    table.to_csv(root / "confirmatory_seed_effects.csv", index=False)
    print(json.dumps(payload, indent=2))
    if not payload["all_integrity_gates_pass"]:
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
