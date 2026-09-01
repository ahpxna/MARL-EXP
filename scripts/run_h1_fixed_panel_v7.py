#!/usr/bin/env python3
"""V7 fixed-panel H1 experiment: local extrema + global C-ranking margins.

This development-only runner was introduced after the V6 experiment showed
that lambda_C cleanly predicts *within-relation* extrema stability but does not
by itself explain *between-relation* C ranking.  V7 fixes the evaluation panel
across training budgets and measures both selection layers on exactly the same
oracle states, factual joint actions, target-policy rows, and raw context.
"""

from __future__ import annotations

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import shutil
import sys

import numpy as np
import pandas as pd
from scipy.stats import spearmanr

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import run_experiment as RE  # noqa: E402
from research_chains.h1_fixed_panel import (  # noqa: E402
    load_fixed_panel,
    save_fixed_panel,
)
from scripts.exp_common import make_args  # noqa: E402
from scripts.run_h1_calibration import build_h1_config  # noqa: E402


V7_PROTOCOL = "h1_fixed_panel_two_level_margin_v1"
V7_REPORT_SCHEMA = "v7_fixed_panel_reporting_v1"
EVIDENCE_CLASSES = ("DEVELOPMENT_EMPIRICAL", "CONFIRMATORY_EMPIRICAL")
PLUGIN_CFG = {"proxy_use_doubly_robust": False, "eps": 0.05}


def _development_only(args) -> bool:
    return str(args.evidence_class) == "DEVELOPMENT_EMPIRICAL"


def _evidence_protocol(args) -> str:
    return str(args.evidence_protocol or V7_PROTOCOL)


def _json_hash(payload) -> str:
    text = json.dumps(payload, sort_keys=True, separators=(",", ":"), default=float)
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _safe_float(value, default=float("nan")):
    try:
        out = float(value)
        return out if math.isfinite(out) else default
    except Exception:
        return default


def _panel_path(panel_root: Path, seed: int) -> Path:
    return panel_root / f"fixed_panel_seed{int(seed)}.pkl.gz"


def _build_panel(
    *,
    seed: int,
    panel_seed: int,
    panel_path: Path,
    tiny_states: int,
    max_steps: int,
    phase_length: int,
    reference_train_episodes: int,
    device: str,
):
    RE.set_global_seed(int(panel_seed))
    cfg = build_h1_config(PLUGIN_CFG, int(panel_seed), threshold_calibration=None)
    args = make_args(
        seed=int(panel_seed),
        device=device,
        result_dir=str(panel_path.parent),
        tiny_horizon=1,
        tiny_proxy_train_episodes=max(1, int(reference_train_episodes)),
        tiny_states=int(tiny_states),
        max_steps=int(max_steps),
        phase_length=int(phase_length),
    )
    args.h1_exact_protocol = True
    args.h1_diagnostic_only = True
    tiny_env = RE.make_tiny_env(
        seed=int(panel_seed),
        max_steps=int(max_steps),
        phase_length=int(phase_length),
    )
    tiny_cfg = RE._tiny_train_cfg_from_base(cfg)
    runner = RE._train_tiny_runner_for_proxy(tiny_env, tiny_cfg, args, device)
    steps, reference_return = RE._collect_h1_eval_steps(runner, int(tiny_states))
    metadata = {
        "v7_protocol": V7_PROTOCOL,
        "experiment_seed": int(seed),
        "panel_seed": int(panel_seed),
        "tiny_states": int(tiny_states),
        "max_steps": int(max_steps),
        "phase_length": int(phase_length),
        "reference_train_episodes": int(reference_train_episodes),
        "reference_variant": "plugin_eps005",
        "reference_cfg_fingerprint": _json_hash(cfg),
        "reference_policy_return": reference_return,
        "scientific_scope": (
            "frozen covariate/oracle panel; reference-runner contexts are held "
            "fixed so checkpoint comparisons isolate learned response estimation"
        ),
    }
    return save_fixed_panel(panel_path, steps, metadata)


def _ensure_panel(args, seed: int):
    panel_root = Path(args.panel_root).resolve()
    panel_root.mkdir(parents=True, exist_ok=True)
    path = _panel_path(panel_root, seed)
    expected_panel_seed = int(args.panel_seed_offset) + int(seed)
    if path.exists() and not args.rebuild_panels:
        payload = load_fixed_panel(path)
        meta = payload["metadata"]
        required = {
            "v7_protocol": V7_PROTOCOL,
            "experiment_seed": int(seed),
            "panel_seed": expected_panel_seed,
            "tiny_states": int(args.tiny_states),
            "max_steps": int(args.max_steps),
            "phase_length": int(args.phase_length),
            "reference_train_episodes": int(args.reference_train_episodes),
        }
        mismatched = {
            key: (meta.get(key), value)
            for key, value in required.items()
            if meta.get(key) != value
        }
        if mismatched:
            raise RuntimeError(
                f"Existing fixed panel {path} has incompatible metadata: {mismatched}"
            )
        return path, payload

    sidecar = _build_panel(
        seed=int(seed),
        panel_seed=expected_panel_seed,
        panel_path=path,
        tiny_states=int(args.tiny_states),
        max_steps=int(args.max_steps),
        phase_length=int(args.phase_length),
        reference_train_episodes=int(args.reference_train_episodes),
        device=args.device,
    )
    payload = load_fixed_panel(path)
    if sidecar["panel_fingerprint"] != payload["panel_fingerprint"]:
        raise RuntimeError("fixed-panel fingerprint changed across save/load")
    return path, payload


def _run_checkpoint(args, seed: int, checkpoint: int, panel_path: Path, panel_fingerprint: str):
    out_dir = (
        Path(args.out_root).resolve()
        / "runs"
        / f"ep{int(checkpoint)}"
        / f"seed{int(seed)}"
    )
    out_dir.mkdir(parents=True, exist_ok=True)
    cfg = build_h1_config(PLUGIN_CFG, int(seed), threshold_calibration=None)
    run_args = make_args(
        seed=int(seed),
        device=args.device,
        result_dir=str(out_dir),
        tiny_horizon=1,
        tiny_proxy_train_episodes=int(checkpoint),
        tiny_states=int(args.tiny_states),
        max_steps=int(args.max_steps),
        phase_length=int(args.phase_length),
    )
    run_args.h1_exact_protocol = True
    # V7 is a development mechanism study, not a confirmatory H1 gate.  Keep
    # protocol diagnostics, but do not abort a tiny smoke merely because the
    # learned scientific recovery gate is false.
    run_args.h1_diagnostic_only = True
    run_args.h1_fixed_panel_path = str(panel_path)

    if args.quiet:
        import contextlib
        with open(os.devnull, "w", encoding="utf-8") as sink:
            with contextlib.redirect_stdout(sink):
                summary = RE.run_tiny_task(
                    run_args, cfg, args.device, out_dir=str(out_dir),
                    run_label=f"v7_ep{checkpoint}_seed{seed}",
                )
    else:
        summary = RE.run_tiny_task(
            run_args, cfg, args.device, out_dir=str(out_dir),
            run_label=f"v7_ep{checkpoint}_seed{seed}",
        )

    summary.update({
        "v7_protocol": V7_PROTOCOL,
        "v7_evidence_protocol": _evidence_protocol(args),
        "v7_evidence_class": str(args.evidence_class),
        "v7_development_only": _development_only(args),
        "v7_checkpoint_episodes": int(checkpoint),
        "v7_fixed_panel_fingerprint": str(panel_fingerprint),
        "v7_training_mode": "independent_same_seed_from_scratch",
    })
    RE.save_json(summary, str(out_dir / "tiny_oracle_summary.json"))
    return out_dir



def _run_dir(out_root: Path, seed: int, checkpoint: int) -> Path:
    return out_root / "runs" / f"ep{int(checkpoint)}" / f"seed{int(seed)}"


def _completion_marker_path(run_dir: Path) -> Path:
    return run_dir / "v7_complete.json"


def _validate_complete_run(
    run_dir: Path,
    *,
    seed: int | None = None,
    checkpoint: int | None = None,
    panel_fingerprint: str | None = None,
):
    """Validate a V7 run cell without trusting a marker file.

    Existing pre-resume V7 cells do not have completion markers, so the
    scientific artifacts themselves are authoritative.  A marker is only a
    cache/provenance aid and is never sufficient on its own.
    """
    required = {
        "pair": run_dir / "tiny_oracle_pair_rows.csv",
        "state": run_dir / "tiny_oracle_calibration_by_state.csv",
        "summary": run_dir / "tiny_oracle_summary.json",
    }
    missing = [name for name, path in required.items() if not path.is_file() or path.stat().st_size == 0]
    if missing:
        return False, f"missing_or_empty:{','.join(missing)}", {}
    try:
        pair = pd.read_csv(required["pair"])
        state = pd.read_csv(required["state"])
        with open(required["summary"], encoding="utf-8") as handle:
            summary = json.load(handle)
    except Exception as exc:
        return False, f"parse_error:{type(exc).__name__}:{exc}", {}
    if pair.empty or state.empty:
        return False, "empty_csv_rows", {}
    if checkpoint is not None:
        recorded = summary.get("v7_checkpoint_episodes")
        if recorded is not None and int(recorded) != int(checkpoint):
            return False, f"checkpoint_mismatch:{recorded}!={checkpoint}", {}
    expected_fp = panel_fingerprint
    recorded_fp = (
        summary.get("v7_fixed_panel_fingerprint")
        or summary.get("fixed_eval_panel_fingerprint")
    )
    if expected_fp is not None and recorded_fp is not None and str(recorded_fp) != str(expected_fp):
        return False, "panel_fingerprint_mismatch", {}
    pair_fp = sorted(set(pair.get("fixed_panel_fingerprint", pd.Series(dtype=str)).dropna().astype(str)))
    if expected_fp is not None and pair_fp and pair_fp != [str(expected_fp)]:
        return False, "pair_panel_fingerprint_mismatch", {}
    metadata = {
        "seed": int(seed) if seed is not None else None,
        "checkpoint": int(checkpoint) if checkpoint is not None else None,
        "pair_rows": int(len(pair)),
        "state_rows": int(len(state)),
        "panel_fingerprint": str(recorded_fp) if recorded_fp is not None else (pair_fp[0] if len(pair_fp) == 1 else None),
        "summary_attempt_complete": summary.get("attempt_complete"),
    }
    return True, "complete", metadata


def _write_completion_marker(run_dir: Path, metadata: dict, *, backfilled: bool = False):
    payload = {
        "protocol": V7_PROTOCOL,
        "complete": True,
        "validated_from_artifacts": True,
        "backfilled": bool(backfilled),
        "validated_at_utc": datetime.now(timezone.utc).isoformat(),
        **metadata,
    }
    _write_json_atomic(_completion_marker_path(run_dir), payload)


def _discover_run_cells(out_root: Path):
    """Discover all run directories and classify them by artifact validity."""
    cells = []
    runs_root = out_root / "runs"
    if not runs_root.exists():
        return cells
    for ep_dir in sorted(runs_root.glob("ep*")):
        if not ep_dir.is_dir():
            continue
        try:
            checkpoint = int(ep_dir.name[2:])
        except ValueError:
            continue
        for seed_dir in sorted(ep_dir.glob("seed*")):
            if not seed_dir.is_dir():
                continue
            try:
                seed = int(seed_dir.name[4:])
            except ValueError:
                continue
            valid, reason, metadata = _validate_complete_run(
                seed_dir, seed=seed, checkpoint=checkpoint
            )
            cell = {
                "seed": seed,
                "checkpoint": checkpoint,
                "run_dir": str(seed_dir),
                "complete": bool(valid),
                "reason": reason,
                **metadata,
            }
            cells.append(cell)
            if valid and not _completion_marker_path(seed_dir).exists():
                _write_completion_marker(seed_dir, metadata, backfilled=True)
    return cells


def _completed_cell_tuples(cells):
    return sorted(
        {(int(c["seed"]), int(c["checkpoint"])) for c in cells if c.get("complete")},
        key=lambda x: (x[1], x[0]),
    )


def _read_cells(out_root: Path, cells):
    pair_frames = []
    state_frames = []
    summary_rows = []
    for seed, checkpoint in cells:
        run_dir = _run_dir(out_root, int(seed), int(checkpoint))
        valid, reason, _ = _validate_complete_run(
            run_dir, seed=int(seed), checkpoint=int(checkpoint)
        )
        if not valid:
            raise RuntimeError(f"Attempted to aggregate incomplete V7 cell seed={seed} checkpoint={checkpoint}: {reason}")
        pair = pd.read_csv(run_dir / "tiny_oracle_pair_rows.csv")
        state = pd.read_csv(run_dir / "tiny_oracle_calibration_by_state.csv")
        pair["checkpoint"] = int(checkpoint)
        pair["experiment_seed"] = int(seed)
        state["checkpoint"] = int(checkpoint)
        state["experiment_seed"] = int(seed)
        pair_frames.append(pair)
        state_frames.append(state)
        with open(run_dir / "tiny_oracle_summary.json", encoding="utf-8") as handle:
            summary = json.load(handle)
        summary_rows.append({
            "checkpoint": int(checkpoint),
            "experiment_seed": int(seed),
            "capacity_active_spearman": _safe_float(summary.get("capacity_active_spearman_mean")),
            "q_normalized_rmse": _safe_float(summary.get("q_normalized_rmse_mean")),
            "q_within_state_spearman": _safe_float(summary.get("q_within_state_action_spearman_mean")),
            "direction_active_spearman": _safe_float(summary.get("direction_active_spearman_mean")),
            "direction_sign_agreement": _safe_float(summary.get("direction_active_sign_agreement_mean")),
            "fixed_panel_fingerprint": summary.get("fixed_eval_panel_fingerprint") or summary.get("v7_fixed_panel_fingerprint"),
            "local_theorem_violations": int(summary.get("functional_boundary_violation_count", 0)),
            "topk_q_violations": int(summary.get("two_level_capacity_topk_q_violation_count", 0)),
            "direction_sign_violations": int(summary.get("direction_sign_boundary_violation_count", 0)),
        })
    if not pair_frames:
        raise RuntimeError("No complete V7 run cells were found for aggregation")
    return (
        pd.concat(pair_frames, ignore_index=True),
        pd.concat(state_frames, ignore_index=True),
        pd.DataFrame(summary_rows),
    )

def _assert_panel_consistency(pair_df: pd.DataFrame):
    """Check oracle invariance across every pair of completed checkpoints per seed.

    Partial grids are allowed: a seed with only one completed checkpoint is
    reported but cannot contribute a cross-checkpoint comparison yet.
    """
    oracle_cols = [
        "oracle_range",
        "oracle_signed",
        "oracle_argmax_action",
        "oracle_argmin_action",
        "oracle_extrema_gap",
        "oracle_topk_gap",
    ]
    details = {}
    all_pass = True
    for seed, seed_df in pair_df.groupby("experiment_seed"):
        checkpoints = sorted(int(x) for x in seed_df["checkpoint"].unique())
        fingerprints = sorted(set(seed_df["fixed_panel_fingerprint"].dropna().astype(str)))
        hash_sets = {
            checkpoint: set(
                seed_df[seed_df["checkpoint"] == checkpoint]["fixed_panel_step_hash"]
                .dropna().astype(str)
            )
            for checkpoint in checkpoints
        }
        base_checkpoint = checkpoints[0]
        hash_equal = all(hash_sets[c] == hash_sets[base_checkpoint] for c in checkpoints)
        seed_result = {
            "completed_checkpoints": checkpoints,
            "fingerprints": fingerprints,
            "single_fingerprint": len(fingerprints) == 1,
            "step_hash_sets_identical": bool(hash_equal),
            "cross_checkpoint_comparison_available": len(checkpoints) >= 2,
            "comparisons": {},
        }
        all_pass &= len(fingerprints) == 1 and hash_equal

        keys = ["fixed_panel_step_hash", "ego_id", "neighbor_id"]
        base = seed_df[seed_df["checkpoint"] == base_checkpoint].set_index(keys)
        for checkpoint in checkpoints[1:]:
            other = seed_df[seed_df["checkpoint"] == checkpoint].set_index(keys)
            common = base.index.intersection(other.index)
            comparison = {"row_count": int(len(common)), "columns": {}}
            if len(common) != len(base) or len(common) != len(other):
                all_pass = False
            for col in oracle_cols:
                if col not in base.columns or col not in other.columns:
                    continue
                left = base.loc[common, col].to_numpy()
                right = other.loc[common, col].to_numpy()
                if np.issubdtype(np.asarray(left).dtype, np.number):
                    equal = np.isclose(
                        left.astype(float), right.astype(float),
                        atol=1e-12, rtol=0.0, equal_nan=True,
                    )
                else:
                    equal = left == right
                rate = float(np.mean(equal)) if len(equal) else float("nan")
                comparison["columns"][col] = rate
                if not bool(np.all(equal)):
                    all_pass = False
            seed_result["comparisons"][f"{base_checkpoint}_vs_{checkpoint}"] = comparison
        details[str(int(seed))] = seed_result
    return {"pass": bool(all_pass), "seeds": details}

def _seed_checkpoint_summary(pair_df, state_df, summary_df):
    rows = []
    for (checkpoint, seed), pair in pair_df.groupby(["checkpoint", "experiment_seed"]):
        state = state_df[
            (state_df["checkpoint"] == checkpoint)
            & (state_df["experiment_seed"] == seed)
        ]
        summary = summary_df[
            (summary_df["checkpoint"] == checkpoint)
            & (summary_df["experiment_seed"] == seed)
        ].iloc[0]
        unique = pair[pair["oracle_extrema_unique"] == 1]
        finite_lambda = unique[np.isfinite(pd.to_numeric(unique["lambda_C"], errors="coerce"))]
        finite_d = pair[np.isfinite(pd.to_numeric(pair["lambda_D"], errors="coerce"))]
        finite_topk = state[np.isfinite(pd.to_numeric(state["lambda_topk_Q"], errors="coerce"))]
        rows.append({
            "checkpoint": int(checkpoint),
            "experiment_seed": int(seed),
            "q_normalized_rmse": summary["q_normalized_rmse"],
            "q_within_state_spearman": summary["q_within_state_spearman"],
            "capacity_active_spearman": summary["capacity_active_spearman"],
            "direction_active_spearman": summary["direction_active_spearman"],
            "direction_sign_agreement": summary["direction_sign_agreement"],
            "q_gauge_sup_error_median": float(pair["q_gauge_sup_error"].median()),
            "lambda_C_median_unique": float(finite_lambda["lambda_C"].median()) if len(finite_lambda) else float("nan"),
            "local_certified_fraction_unique": float(unique["extrema_stability_certified"].mean()) if len(unique) else float("nan"),
            "local_extrema_swap_rate_unique": float((1 - unique["both_extrema_match"]).mean()) if len(unique) else float("nan"),
            "capacity_mae": float(pair["capacity_abs_error"].mean()),
            "capacity_q_error_bound_violation_count": int(pair["capacity_q_error_bound_violation"].sum()),
            "topk_match_rate": float(state["capacity_topk_match"].mean()),
            "topk_q_certified_rate": float(state["capacity_topk_q_certified"].mean()),
            "topk_q_certified_violation_count": int(state["capacity_topk_q_certified_violation"].sum()),
            "topk_interval_certified_rate": float(state["capacity_topk_interval_certified"].mean()),
            "lambda_topk_Q_median": float(finite_topk["lambda_topk_Q"].median()) if len(finite_topk) else float("nan"),
            "oracle_topk_gap_median": float(state["oracle_topk_gap"].median()),
            "strict_relation_pair_order_accuracy": float(
                np.average(
                    state["strict_relation_pair_order_accuracy"].fillna(0.0),
                    weights=state["strict_relation_pair_count"].clip(lower=0),
                )
            ) if state["strict_relation_pair_count"].sum() > 0 else float("nan"),
            "direction_sign_certified_fraction": float(pair["direction_sign_certified"].mean()),
            "direction_sign_certified_violation_count": int(pair["direction_sign_violation"].sum()),
            "lambda_D_median": float(finite_d["lambda_D"].median()) if len(finite_d) else float("nan"),
            "local_theorem_violation_count": int(pair["extrema_stability_violation"].sum()),
        })
    return pd.DataFrame(rows).sort_values(["checkpoint", "experiment_seed"])


def _checkpoint_summary(seed_summary: pd.DataFrame):
    numeric = [c for c in seed_summary.columns if c not in {"checkpoint", "experiment_seed"}]
    rows = []
    for checkpoint, frame in seed_summary.groupby("checkpoint"):
        row = {"checkpoint": int(checkpoint), "n_seeds": int(len(frame))}
        for col in numeric:
            values = pd.to_numeric(frame[col], errors="coerce")
            finite = values[np.isfinite(values)]
            row[f"{col}_mean"] = float(finite.mean()) if len(finite) else float("nan")
            row[f"{col}_median"] = float(finite.median()) if len(finite) else float("nan")
        rows.append(row)
    return pd.DataFrame(rows).sort_values("checkpoint")


def _heterogeneity(seed_summary: pd.DataFrame, checkpoint: int):
    frame = seed_summary[seed_summary["checkpoint"] == int(checkpoint)]
    out = {"checkpoint": int(checkpoint), "n_seeds": int(len(frame))}
    target = frame["capacity_active_spearman"].to_numpy(dtype=float)
    for name in (
        "local_certified_fraction_unique",
        "lambda_C_median_unique",
        "topk_q_certified_rate",
        "lambda_topk_Q_median",
        "oracle_topk_gap_median",
        "strict_relation_pair_order_accuracy",
    ):
        x = frame[name].to_numpy(dtype=float)
        keep = np.isfinite(x) & np.isfinite(target)
        if (
            int(keep.sum()) >= 3
            and len(np.unique(x[keep])) > 1
            and len(np.unique(target[keep])) > 1
        ):
            rho, p = spearmanr(x[keep], target[keep])
            out[name] = {"spearman": float(rho), "p_value": float(p)}
        else:
            out[name] = {"spearman": float("nan"), "p_value": float("nan")}
    return out



def _phase_label(values: pd.Series, cuts, labels):
    x = pd.to_numeric(values, errors="coerce").to_numpy(dtype=float)
    out = np.full(len(x), None, dtype=object)
    finite = np.isfinite(x)
    if not finite.any():
        return pd.Series(out, index=values.index, dtype="object")
    lower = -np.inf
    for upper, label in zip(cuts, labels[:-1]):
        mask = finite & (x >= lower) & (x < upper)
        out[mask] = label
        lower = upper
    out[finite & (x >= lower)] = labels[-1]
    return pd.Series(out, index=values.index, dtype="object")


def _lambda_c_phase_table(pair_df: pd.DataFrame):
    rows = []
    for checkpoint, frame in pair_df.groupby("checkpoint"):
        frame = frame[frame["oracle_extrema_unique"] == 1].copy()
        frame["phase_bin"] = _phase_label(
            frame["lambda_C"],
            [0.25, 0.5, 1.0],
            ["lt_0_25", "0_25_to_0_5", "0_5_to_1", "ge_1"],
        )
        for phase, group in frame.dropna(subset=["phase_bin"]).groupby("phase_bin", sort=False):
            rows.append({
                "checkpoint": int(checkpoint),
                "phase_bin": str(phase),
                "row_count": int(len(group)),
                "lambda_C_median": float(pd.to_numeric(group["lambda_C"], errors="coerce").median()),
                "q_gauge_sup_error_median": float(pd.to_numeric(group["q_gauge_sup_error"], errors="coerce").median()),
                "extrema_match_rate": float(pd.to_numeric(group["both_extrema_match"], errors="coerce").mean()),
                "extrema_swap_rate": float((1.0 - pd.to_numeric(group["both_extrema_match"], errors="coerce")).mean()),
                "capacity_mae": float(pd.to_numeric(group["capacity_abs_error"], errors="coerce").mean()),
                "theorem_certified_rate": float(pd.to_numeric(group["extrema_stability_certified"], errors="coerce").mean()),
                "theorem_violation_count": int(pd.to_numeric(group["extrema_stability_violation"], errors="coerce").fillna(0).sum()),
            })
    return pd.DataFrame(rows)


def _lambda_topk_phase_table(state_df: pd.DataFrame):
    rows = []
    for checkpoint, frame in state_df.groupby("checkpoint"):
        frame = frame.copy()
        frame["phase_bin"] = _phase_label(
            frame["lambda_topk_Q"],
            [1.0, 2.0, 5.0],
            ["lt_1", "1_to_2", "2_to_5", "ge_5"],
        )
        for phase, group in frame.dropna(subset=["phase_bin"]).groupby("phase_bin", sort=False):
            counts = pd.to_numeric(group["strict_relation_pair_count"], errors="coerce").fillna(0).clip(lower=0)
            accuracy = pd.to_numeric(group["strict_relation_pair_order_accuracy"], errors="coerce")
            valid = np.isfinite(accuracy.to_numpy(dtype=float)) & (counts.to_numpy(dtype=float) > 0)
            weighted_order = float(
                np.average(accuracy.to_numpy(dtype=float)[valid], weights=counts.to_numpy(dtype=float)[valid])
            ) if valid.any() else float("nan")
            rows.append({
                "checkpoint": int(checkpoint),
                "phase_bin": str(phase),
                "state_count": int(len(group)),
                "lambda_topk_Q_median": float(pd.to_numeric(group["lambda_topk_Q"], errors="coerce").median()),
                "oracle_topk_gap_median": float(pd.to_numeric(group["oracle_topk_gap"], errors="coerce").median()),
                "topk_match_rate": float(pd.to_numeric(group["capacity_topk_match"], errors="coerce").mean()),
                "strict_relation_pair_order_accuracy": weighted_order,
                "q_certificate_rate": float(pd.to_numeric(group["capacity_topk_q_certified"], errors="coerce").mean()),
                "q_certificate_violation_count": int(pd.to_numeric(group["capacity_topk_q_certified_violation"], errors="coerce").fillna(0).sum()),
                "interval_certificate_rate": float(pd.to_numeric(group["capacity_topk_interval_certified"], errors="coerce").mean()),
                "interval_certificate_violation_count": int(pd.to_numeric(group["capacity_topk_interval_certified_violation"], errors="coerce").fillna(0).sum()),
            })
    return pd.DataFrame(rows)


def _lambda_d_phase_table(pair_df: pd.DataFrame):
    rows = []
    for checkpoint, frame in pair_df.groupby("checkpoint"):
        frame = frame.copy()
        frame["phase_bin"] = _phase_label(
            frame["lambda_D"],
            [1.0, 2.0, 5.0],
            ["lt_1", "1_to_2", "2_to_5", "ge_5"],
        )
        for phase, group in frame.dropna(subset=["phase_bin"]).groupby("phase_bin", sort=False):
            rows.append({
                "checkpoint": int(checkpoint),
                "phase_bin": str(phase),
                "row_count": int(len(group)),
                "lambda_D_median": float(pd.to_numeric(group["lambda_D"], errors="coerce").median()),
                "direction_sign_match_rate": float(pd.to_numeric(group["direction_sign_match_from_q"], errors="coerce").mean()),
                "direction_abs_error_mean": float(pd.to_numeric(group["direction_abs_error"], errors="coerce").mean()),
                "sign_certificate_rate": float(pd.to_numeric(group["direction_sign_certified"], errors="coerce").mean()),
                "sign_certificate_violation_count": int(pd.to_numeric(group["direction_sign_violation"], errors="coerce").fillna(0).sum()),
            })
    return pd.DataFrame(rows)


def _certificate_nonvacuity_table(pair_df: pd.DataFrame, state_df: pd.DataFrame):
    rows = []
    for checkpoint in sorted(int(x) for x in pair_df["checkpoint"].unique()):
        pair = pair_df[pair_df["checkpoint"] == checkpoint]
        state = state_df[state_df["checkpoint"] == checkpoint]

        unique = pair[pair["oracle_extrema_unique"] == 1]
        cert = unique[pd.to_numeric(unique["extrema_stability_certified"], errors="coerce") == 1]
        rows.append({
            "checkpoint": checkpoint,
            "certificate": "local_extrema_lambdaC",
            "eligible_count": int(len(unique)),
            "certified_count": int(len(cert)),
            "coverage_among_eligible": float(len(cert) / len(unique)) if len(unique) else float("nan"),
            "correctness_among_certified": float(pd.to_numeric(cert["both_extrema_match"], errors="coerce").mean()) if len(cert) else float("nan"),
            "violation_count": int(pd.to_numeric(unique["extrema_stability_violation"], errors="coerce").fillna(0).sum()),
        })

        for name, cert_col, violation_col in [
            ("topk_q_margin", "capacity_topk_q_certified", "capacity_topk_q_certified_violation"),
            ("topk_interval", "capacity_topk_interval_certified", "capacity_topk_interval_certified_violation"),
        ]:
            eligible = state
            certified = eligible[pd.to_numeric(eligible[cert_col], errors="coerce") == 1]
            rows.append({
                "checkpoint": checkpoint,
                "certificate": name,
                "eligible_count": int(len(eligible)),
                "certified_count": int(len(certified)),
                "coverage_among_eligible": float(len(certified) / len(eligible)) if len(eligible) else float("nan"),
                "correctness_among_certified": float(pd.to_numeric(certified["capacity_topk_match"], errors="coerce").mean()) if len(certified) else float("nan"),
                "violation_count": int(pd.to_numeric(eligible[violation_col], errors="coerce").fillna(0).sum()),
            })

        finite_d = pair[np.isfinite(pd.to_numeric(pair["lambda_D"], errors="coerce"))]
        dcert = finite_d[pd.to_numeric(finite_d["direction_sign_certified"], errors="coerce") == 1]
        rows.append({
            "checkpoint": checkpoint,
            "certificate": "direction_sign_lambdaD",
            "eligible_count": int(len(finite_d)),
            "certified_count": int(len(dcert)),
            "coverage_among_eligible": float(len(dcert) / len(finite_d)) if len(finite_d) else float("nan"),
            "correctness_among_certified": float(pd.to_numeric(dcert["direction_sign_match_from_q"], errors="coerce").mean()) if len(dcert) else float("nan"),
            "violation_count": int(pd.to_numeric(finite_d["direction_sign_violation"], errors="coerce").fillna(0).sum()),
        })
    return pd.DataFrame(rows)


def _paired_longitudinal_table(pair_df: pd.DataFrame, state_df: pd.DataFrame):
    """Paired same-panel changes between every pair of completed checkpoints."""
    rows = []
    checkpoints = sorted(int(x) for x in pair_df["checkpoint"].unique())
    pair_keys = ["experiment_seed", "fixed_panel_step_hash", "ego_id", "neighbor_id"]
    state_keys = ["experiment_seed", "fixed_panel_step_hash", "ego_id"]

    for i, before_cp in enumerate(checkpoints):
        for after_cp in checkpoints[i + 1:]:
            before = pair_df[pair_df["checkpoint"] == before_cp].set_index(pair_keys)
            after = pair_df[pair_df["checkpoint"] == after_cp].set_index(pair_keys)
            common = before.index.intersection(after.index)
            if not len(common):
                continue
            b = before.loc[common]
            a = after.loc[common]
            unique = (
                (pd.to_numeric(b["oracle_extrema_unique"], errors="coerce") == 1)
                & (pd.to_numeric(a["oracle_extrema_unique"], errors="coerce") == 1)
            )
            bq = pd.to_numeric(b["q_gauge_sup_error"], errors="coerce").to_numpy(dtype=float)
            aq = pd.to_numeric(a["q_gauge_sup_error"], errors="coerce").to_numpy(dtype=float)
            finite_q = np.isfinite(bq) & np.isfinite(aq)
            bl = pd.to_numeric(b["lambda_C"], errors="coerce").to_numpy(dtype=float)
            al = pd.to_numeric(a["lambda_C"], errors="coerce").to_numpy(dtype=float)
            unique_np = unique.to_numpy(dtype=bool)
            finite_l = unique_np & np.isfinite(bl) & np.isfinite(al)

            bs = state_df[state_df["checkpoint"] == before_cp].set_index(state_keys)
            aas = state_df[state_df["checkpoint"] == after_cp].set_index(state_keys)
            scommon = bs.index.intersection(aas.index)
            sb = bs.loc[scommon]
            sa = aas.loc[scommon]
            btop = pd.to_numeric(sb["capacity_topk_match"], errors="coerce").to_numpy(dtype=float)
            atop = pd.to_numeric(sa["capacity_topk_match"], errors="coerce").to_numpy(dtype=float)
            btl = pd.to_numeric(sb["lambda_topk_Q"], errors="coerce").to_numpy(dtype=float)
            atl = pd.to_numeric(sa["lambda_topk_Q"], errors="coerce").to_numpy(dtype=float)
            finite_tl = np.isfinite(btl) & np.isfinite(atl)

            rows.append({
                "before_checkpoint": before_cp,
                "after_checkpoint": after_cp,
                "paired_pair_rows": int(len(common)),
                "paired_state_rows": int(len(scommon)),
                "q_gauge_error_decrease_fraction": float(np.mean(aq[finite_q] < bq[finite_q])) if finite_q.any() else float("nan"),
                "q_gauge_error_before_median": float(np.median(bq[finite_q])) if finite_q.any() else float("nan"),
                "q_gauge_error_after_median": float(np.median(aq[finite_q])) if finite_q.any() else float("nan"),
                "unique_extrema_paired_rows": int(finite_l.sum()),
                "lambda_C_decrease_fraction": float(np.mean(al[finite_l] < bl[finite_l])) if finite_l.any() else float("nan"),
                "lambda_C_before_median": float(np.median(bl[finite_l])) if finite_l.any() else float("nan"),
                "lambda_C_after_median": float(np.median(al[finite_l])) if finite_l.any() else float("nan"),
                "local_certified_before_rate": float(pd.to_numeric(b.loc[unique, "extrema_stability_certified"], errors="coerce").mean()) if unique.any() else float("nan"),
                "local_certified_after_rate": float(pd.to_numeric(a.loc[unique, "extrema_stability_certified"], errors="coerce").mean()) if unique.any() else float("nan"),
                "extrema_swap_before_rate": float((1.0 - pd.to_numeric(b.loc[unique, "both_extrema_match"], errors="coerce")).mean()) if unique.any() else float("nan"),
                "extrema_swap_after_rate": float((1.0 - pd.to_numeric(a.loc[unique, "both_extrema_match"], errors="coerce")).mean()) if unique.any() else float("nan"),
                "capacity_mae_before": float(pd.to_numeric(b["capacity_abs_error"], errors="coerce").mean()),
                "capacity_mae_after": float(pd.to_numeric(a["capacity_abs_error"], errors="coerce").mean()),
                "topk_match_before_rate": float(np.nanmean(btop)) if len(btop) else float("nan"),
                "topk_match_after_rate": float(np.nanmean(atop)) if len(atop) else float("nan"),
                "topk_gained_fraction": float(np.mean((btop == 0) & (atop == 1))) if len(btop) else float("nan"),
                "topk_lost_fraction": float(np.mean((btop == 1) & (atop == 0))) if len(btop) else float("nan"),
                "lambda_topk_decrease_fraction": float(np.mean(atl[finite_tl] < btl[finite_tl])) if finite_tl.any() else float("nan"),
                "lambda_topk_before_median": float(np.median(btl[finite_tl])) if finite_tl.any() else float("nan"),
                "lambda_topk_after_median": float(np.median(atl[finite_tl])) if finite_tl.any() else float("nan"),
                "strict_order_before_mean": float(pd.to_numeric(sb["strict_relation_pair_order_accuracy"], errors="coerce").mean()),
                "strict_order_after_mean": float(pd.to_numeric(sa["strict_relation_pair_order_accuracy"], errors="coerce").mean()),
                "q_derived_direction_sign_before_rate": float(pd.to_numeric(b["direction_sign_match_from_q"], errors="coerce").mean()),
                "q_derived_direction_sign_after_rate": float(pd.to_numeric(a["direction_sign_match_from_q"], errors="coerce").mean()),
            })
    return pd.DataFrame(rows)



def _seed_paired_longitudinal_table(pair_df: pd.DataFrame, state_df: pd.DataFrame):
    frames = []
    for seed in sorted(int(x) for x in pair_df["experiment_seed"].unique()):
        pair = pair_df[pair_df["experiment_seed"] == seed]
        state = state_df[state_df["experiment_seed"] == seed]
        table = _paired_longitudinal_table(pair, state)
        if len(table):
            table.insert(0, "experiment_seed", seed)
            frames.append(table)
    return pd.concat(frames, ignore_index=True) if frames else pd.DataFrame()


def _spearman_record(checkpoint, name, x, y):
    x = pd.to_numeric(x, errors="coerce").to_numpy(dtype=float)
    y = pd.to_numeric(y, errors="coerce").to_numpy(dtype=float)
    keep = np.isfinite(x) & np.isfinite(y)
    if int(keep.sum()) >= 3 and len(np.unique(x[keep])) > 1 and len(np.unique(y[keep])) > 1:
        rho, p = spearmanr(x[keep], y[keep])
        rho, p = float(rho), float(p)
    else:
        rho, p = float("nan"), float("nan")
    return {
        "checkpoint": int(checkpoint),
        "analysis": name,
        "n": int(keep.sum()),
        "spearman": rho,
        "p_value": p,
    }


def _phase_correlation_table(pair_df: pd.DataFrame, state_df: pd.DataFrame):
    rows = []
    checkpoints = sorted(int(x) for x in pair_df["checkpoint"].unique())
    for checkpoint in checkpoints:
        pair = pair_df[pair_df["checkpoint"] == checkpoint]
        unique = pair[pair["oracle_extrema_unique"] == 1]
        state = state_df[state_df["checkpoint"] == checkpoint]
        rows.append(_spearman_record(
            checkpoint, "lambda_C_vs_capacity_abs_error",
            unique["lambda_C"], unique["capacity_abs_error"],
        ))
        rows.append(_spearman_record(
            checkpoint, "lambda_C_vs_extrema_match",
            unique["lambda_C"], unique["both_extrema_match"],
        ))
        rows.append(_spearman_record(
            checkpoint, "lambda_topk_Q_vs_topk_match",
            state["lambda_topk_Q"], state["capacity_topk_match"],
        ))
        rows.append(_spearman_record(
            checkpoint, "lambda_topk_Q_vs_strict_pair_order_accuracy",
            state["lambda_topk_Q"], state["strict_relation_pair_order_accuracy"],
        ))
        finite_d = pair[np.isfinite(pd.to_numeric(pair["lambda_D"], errors="coerce"))]
        rows.append(_spearman_record(
            checkpoint, "lambda_D_vs_q_derived_sign_match",
            finite_d["lambda_D"], finite_d["direction_sign_match_from_q"],
        ))
    return pd.DataFrame(rows)


def _final_scientific_report(checkpoint_summary, paired, seed_paired, lambda_c, lambda_topk, lambda_d, certs, correlations, *, evidence_class, evidence_protocol):
    checkpoints = sorted(int(x) for x in checkpoint_summary["checkpoint"].unique()) if len(checkpoint_summary) else []
    latest = checkpoints[-1] if checkpoints else None
    report = {
        "report_schema": V7_REPORT_SCHEMA,
        "protocol": V7_PROTOCOL,
        "evidence_protocol": str(evidence_protocol),
        "evidence_class": str(evidence_class),
        "development_only": str(evidence_class) == "DEVELOPMENT_EMPIRICAL",
        "completed_checkpoints_in_aggregate": checkpoints,
        "latest_checkpoint": latest,
        "claims_guardrails": [
            "Fixed-panel longitudinal claims require v7_panel_consistency.json pass=true.",
            "lambda_C<0.5 is a sufficient local-extrema certificate, not a global-ranking certificate.",
            "lambda_topk_Q is a between-relation selection diagnostic/certificate ratio.",
            "lambda_D<1 certifies direction sign only; it does not certify magnitude ranking.",
            "Certificate coverage is reported separately from correctness; zero violations does not imply nonvacuity.",
        ],
        "output_tables": {
            "paired_longitudinal": "v7_paired_longitudinal.csv",
            "paired_longitudinal_by_seed": "v7_paired_longitudinal_by_seed.csv",
            "lambda_C_phase": "v7_lambdaC_phase.csv",
            "lambda_topk_phase": "v7_lambda_topk_phase.csv",
            "lambda_D_phase": "v7_lambdaD_phase.csv",
            "certificate_nonvacuity": "v7_certificate_nonvacuity.csv",
            "phase_correlations": "v7_phase_correlations.csv",
        },
    }
    if latest is not None:
        cp = checkpoint_summary[checkpoint_summary["checkpoint"] == latest].iloc[0]
        report["latest_checkpoint_snapshot"] = {
            key: _safe_float(cp.get(key))
            for key in checkpoint_summary.columns
            if key != "checkpoint"
        }
    if len(paired):
        report["longitudinal_transitions"] = paired.to_dict(orient="records")
    return report


def _write_reporting_outputs(out_root: Path, pair_df, state_df, checkpoint_summary, *, evidence_class, evidence_protocol):
    paired = _paired_longitudinal_table(pair_df, state_df)
    seed_paired = _seed_paired_longitudinal_table(pair_df, state_df)
    lambda_c = _lambda_c_phase_table(pair_df)
    lambda_topk = _lambda_topk_phase_table(state_df)
    lambda_d = _lambda_d_phase_table(pair_df)
    certs = _certificate_nonvacuity_table(pair_df, state_df)
    correlations = _phase_correlation_table(pair_df, state_df)
    paired.to_csv(out_root / "v7_paired_longitudinal.csv", index=False)
    seed_paired.to_csv(out_root / "v7_paired_longitudinal_by_seed.csv", index=False)
    lambda_c.to_csv(out_root / "v7_lambdaC_phase.csv", index=False)
    lambda_topk.to_csv(out_root / "v7_lambda_topk_phase.csv", index=False)
    lambda_d.to_csv(out_root / "v7_lambdaD_phase.csv", index=False)
    certs.to_csv(out_root / "v7_certificate_nonvacuity.csv", index=False)
    correlations.to_csv(out_root / "v7_phase_correlations.csv", index=False)
    report = _final_scientific_report(
        checkpoint_summary, paired, seed_paired, lambda_c, lambda_topk, lambda_d, certs, correlations,
        evidence_class=evidence_class, evidence_protocol=evidence_protocol,
    )
    _write_json_atomic(out_root / "v7_final_scientific_report.json", report)
    return {
        "paired": paired,
        "seed_paired": seed_paired,
        "lambda_C": lambda_c,
        "lambda_topk": lambda_topk,
        "lambda_D": lambda_d,
        "certificates": certs,
        "correlations": correlations,
        "report": report,
    }


def _write_json_atomic(path: Path, payload):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    tmp.write_text(
        json.dumps(payload, indent=2, sort_keys=True, default=float),
        encoding="utf-8",
    )
    os.replace(tmp, path)


def _write_json(path: Path, payload):
    _write_json_atomic(path, payload)


def _load_json_if_exists(path: Path):
    if not path.is_file():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return None


def _stable_scientific_config(args):
    return {
        "protocol": V7_PROTOCOL,
        "tiny_states": int(args.tiny_states),
        "max_steps": int(args.max_steps),
        "phase_length": int(args.phase_length),
        "reference_train_episodes": int(args.reference_train_episodes),
        "panel_seed_offset": int(args.panel_seed_offset),
        "variant": "plugin_eps005",
    }


def _check_manifest_compatibility(existing, args):
    if not existing:
        return
    current = _stable_scientific_config(args)
    previous = existing.get("scientific_config")
    if previous is None:
        # Backward compatibility with the original V7 manifest schema.
        previous = {key: existing.get(key) for key in current}
    mismatched = {
        key: (previous.get(key), value)
        for key, value in current.items()
        if previous.get(key) is not None and previous.get(key) != value
    }
    if mismatched:
        raise RuntimeError(
            "Existing V7 output root was created with incompatible scientific settings: "
            f"{mismatched}. Use a different --out-root or restore matching settings."
        )
    previous_evidence = existing.get("evidence_class")
    if previous_evidence is not None and str(previous_evidence) != str(args.evidence_class):
        raise RuntimeError(
            "Existing V7 output root has incompatible evidence_class: "
            f"{previous_evidence} != {args.evidence_class}"
        )


def _completion_payload(out_root: Path, args, cells, invocation=None):
    existing = _load_json_if_exists(out_root / "v7_manifest.json") or {}
    old_expected_seeds = set(int(x) for x in existing.get("expected_seeds", existing.get("seeds", [])))
    old_expected_checkpoints = set(int(x) for x in existing.get("expected_checkpoints", existing.get("checkpoints", [])))
    discovered_seeds = set(int(c["seed"]) for c in cells)
    discovered_checkpoints = set(int(c["checkpoint"]) for c in cells)
    expected_seeds = sorted(old_expected_seeds | discovered_seeds | set(int(x) for x in args.seeds))
    expected_checkpoints = sorted(
        old_expected_checkpoints
        | discovered_checkpoints
        | set(int(x) for x in args.checkpoints)
    )
    complete = {(int(c["seed"]), int(c["checkpoint"])) for c in cells if c.get("complete")}
    incomplete = [
        {
            "seed": int(c["seed"]),
            "checkpoint": int(c["checkpoint"]),
            "reason": c.get("reason"),
        }
        for c in cells if not c.get("complete")
    ]
    # Expected-but-not-created cells are also incomplete for grid provenance.
    known = {(int(c["seed"]), int(c["checkpoint"])) for c in cells}
    for checkpoint in expected_checkpoints:
        for seed in expected_seeds:
            if (seed, checkpoint) not in known:
                incomplete.append({
                    "seed": seed,
                    "checkpoint": checkpoint,
                    "reason": "not_created",
                })
    completed_checkpoints = [
        checkpoint
        for checkpoint in expected_checkpoints
        if expected_seeds and all((seed, checkpoint) in complete for seed in expected_seeds)
    ]
    partial_checkpoints = [
        checkpoint
        for checkpoint in expected_checkpoints
        if any((seed, checkpoint) in complete for seed in expected_seeds)
        and checkpoint not in completed_checkpoints
    ]
    invocations = list(existing.get("invocations", []))
    if invocation is not None:
        invocations.append(invocation)
    payload = {
        "manifest_version": 2,
        "protocol": V7_PROTOCOL,
        "evidence_protocol": _evidence_protocol(args),
        "evidence_class": str(args.evidence_class),
        "development_only": _development_only(args),
        "scientific_config": _stable_scientific_config(args),
        "scientific_config_fingerprint": _json_hash(_stable_scientific_config(args)),
        "expected_seeds": expected_seeds,
        "expected_checkpoints": expected_checkpoints,
        "completed_checkpoints": completed_checkpoints,
        "partially_completed_checkpoints": partial_checkpoints,
        "completed_cells": [
            {"seed": seed, "checkpoint": checkpoint}
            for seed, checkpoint in sorted(complete, key=lambda x: (x[1], x[0]))
        ],
        "incomplete_cells": sorted(incomplete, key=lambda x: (x["checkpoint"], x["seed"])),
        "invocations": invocations,
        "scientific_questions": [
            "Does Q error decrease on the identical oracle panel as training increases?",
            "Does lambda_C explain within-relation extrema stability?",
            "Do between-relation C margins explain TopK/global ranking beyond lambda_C?",
            "Does lambda_D certify D sign even when D magnitude ranking is weak?",
        ],
        "updated_at_utc": datetime.now(timezone.utc).isoformat(),
    }
    return payload


def _set_invocation_status(out_root: Path, invocation_id: str, status: str, **extra):
    path = out_root / "v7_manifest.json"
    manifest = _load_json_if_exists(path)
    if not manifest:
        return
    for invocation in reversed(manifest.get("invocations", [])):
        if invocation.get("id") == invocation_id:
            invocation["status"] = status
            invocation.update(extra)
            break
    manifest["updated_at_utc"] = datetime.now(timezone.utc).isoformat()
    _write_json_atomic(path, manifest)


def _validate_evidence_context(out_root: Path, args) -> None:
    if str(args.evidence_class) != "CONFIRMATORY_EMPIRICAL":
        return
    if not args.evidence_protocol:
        raise RuntimeError("confirmatory evidence requires --evidence-protocol")
    protocol_path = out_root / "CONFIRMATORY_PROTOCOL.json"
    if not protocol_path.is_file():
        raise RuntimeError("confirmatory evidence requires CONFIRMATORY_PROTOCOL.json in --out-root")
    payload = _load_json_if_exists(protocol_path)
    if not payload or str(payload.get("protocol_version")) != str(args.evidence_protocol):
        raise RuntimeError("confirmatory protocol identifier does not match --evidence-protocol")
    if payload.get("development_seed_overlap") is not False:
        raise RuntimeError("confirmatory protocol must explicitly record development_seed_overlap=false")
    frozen = payload.get("frozen", {})
    if frozen and list(map(int, frozen.get("checkpoints", []))) != list(map(int, args.checkpoints)):
        raise RuntimeError("confirmatory checkpoint grid differs from frozen protocol")
    allowed = set(map(int, payload.get("seeds", [])))
    if not set(map(int, args.seeds)) <= allowed:
        raise RuntimeError("requested confirmatory seeds are not contained in the frozen protocol")


def _cell_evidence_matches(run_dir: Path, args) -> bool:
    """Confirm that a completed cell was generated under this evidence layer.

    Historical development artifacts are never relabeled confirmatory after
    completion. Confirmatory reuse is allowed only when the cell itself records
    the frozen evidence protocol and class.
    """
    summary_path = run_dir / "tiny_oracle_summary.json"
    if not summary_path.is_file():
        return False
    summary = _load_json_if_exists(summary_path)
    if not summary:
        return False
    if _development_only(args):
        return summary.get("v7_evidence_class") in (None, "DEVELOPMENT_EMPIRICAL")
    return bool(
        summary.get("v7_evidence_class") == str(args.evidence_class)
        and summary.get("v7_evidence_protocol") == _evidence_protocol(args)
        and summary.get("v7_development_only") is False
    )


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--seeds", type=int, nargs="+", default=[3001, 3002, 3003, 3004, 3005])
    ap.add_argument("--checkpoints", type=int, nargs="+", default=[20, 80, 320])
    ap.add_argument("--device", default="cpu")
    ap.add_argument("--tiny-states", type=int, default=24)
    ap.add_argument("--max-steps", type=int, default=30)
    ap.add_argument("--phase-length", type=int, default=40)
    ap.add_argument("--reference-train-episodes", type=int, default=1)
    ap.add_argument("--panel-seed-offset", type=int, default=700000)
    ap.add_argument(
        "--out-root", default=str(ROOT / "research" / "v7_fixed_panel"),
    )
    ap.add_argument("--panel-root", default=None)
    ap.add_argument("--rebuild-panels", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument(
        "--evidence-class", choices=EVIDENCE_CLASSES, default="DEVELOPMENT_EMPIRICAL",
        help="Scientific evidence class for provenance; confirmatory mode requires a frozen protocol file.",
    )
    ap.add_argument(
        "--evidence-protocol", default=None,
        help="Protocol identifier for the evidence layer. Defaults to the underlying V7 protocol.",
    )
    ap.add_argument(
        "--analyze-only", action="store_true",
        help="Do not train. Re-discover all complete cells under --out-root and rebuild cumulative V7 aggregates.",
    )
    ap.add_argument(
        "--rerun-complete", action="store_true",
        help="Re-run cells even when their existing V7 artifacts validate as complete. Default is resume/skip-complete.",
    )
    args = ap.parse_args(argv)

    if len(set(args.seeds)) != len(args.seeds):
        ap.error("--seeds must be unique")
    if len(set(args.checkpoints)) != len(args.checkpoints):
        ap.error("--checkpoints must be unique")
    if any(int(x) <= 0 for x in args.checkpoints):
        ap.error("--checkpoints must be positive")
    if args.tiny_states <= 0 or args.max_steps <= 0:
        ap.error("--tiny-states and --max-steps must be positive")
    if args.analyze_only and args.rebuild_panels:
        ap.error("--analyze-only cannot be combined with --rebuild-panels")

    out_root = Path(args.out_root).resolve()
    out_root.mkdir(parents=True, exist_ok=True)
    _validate_evidence_context(out_root, args)
    if args.panel_root is None:
        args.panel_root = str(out_root / "panels")

    existing_manifest = _load_json_if_exists(out_root / "v7_manifest.json")
    _check_manifest_compatibility(existing_manifest, args)

    initial_cells = _discover_run_cells(out_root)
    invocation_id = hashlib.sha256(
        f"{datetime.now(timezone.utc).isoformat()}:{os.getpid()}:{args.seeds}:{args.checkpoints}:{args.analyze_only}".encode()
    ).hexdigest()[:16]
    invocation = {
        "id": invocation_id,
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "started",
        "mode": "analyze_only" if args.analyze_only else "run",
        "requested_seeds": [int(x) for x in args.seeds],
        "requested_checkpoints": [int(x) for x in args.checkpoints],
        "resume_skip_complete": not bool(args.rerun_complete),
        "evidence_class": str(args.evidence_class),
        "evidence_protocol": _evidence_protocol(args),
    }
    _write_json_atomic(
        out_root / "v7_manifest.json",
        _completion_payload(out_root, args, initial_cells, invocation=invocation),
    )

    executed_cells = []
    skipped_cells = []
    try:
        if not args.analyze_only:
            panel_info = _load_json_if_exists(out_root / "v7_panels.json") or {}
            for seed in args.seeds:
                path, payload = _ensure_panel(args, int(seed))
                panel_info[str(seed)] = {
                    "path": str(path),
                    "fingerprint": payload["panel_fingerprint"],
                    "step_hashes": payload["step_hashes"],
                    "metadata": payload["metadata"],
                }
                for checkpoint in args.checkpoints:
                    run_dir = _run_dir(out_root, int(seed), int(checkpoint))
                    valid, reason, metadata = _validate_complete_run(
                        run_dir,
                        seed=int(seed),
                        checkpoint=int(checkpoint),
                        panel_fingerprint=payload["panel_fingerprint"],
                    )
                    if valid and not args.rerun_complete:
                        if not _cell_evidence_matches(run_dir, args):
                            raise RuntimeError(
                                "completed cell belongs to a different evidence layer; "
                                "do not relabel it. Use a fresh --out-root for confirmatory execution"
                            )
                        if not _completion_marker_path(run_dir).exists():
                            _write_completion_marker(run_dir, metadata, backfilled=True)
                        skipped_cells.append({"seed": int(seed), "checkpoint": int(checkpoint)})
                        print(
                            f"[V7] SKIP complete seed={seed} checkpoint={checkpoint} "
                            f"panel={payload['panel_fingerprint'][:12]}",
                            flush=True,
                        )
                        continue

                    if run_dir.exists():
                        print(
                            f"[V7] RESET incomplete/rerun seed={seed} checkpoint={checkpoint} reason={reason}",
                            flush=True,
                        )
                        shutil.rmtree(run_dir)
                    print(
                        f"[V7] RUN seed={seed} checkpoint={checkpoint} panel={payload['panel_fingerprint'][:12]}",
                        flush=True,
                    )
                    _run_checkpoint(
                        args, int(seed), int(checkpoint), path,
                        payload["panel_fingerprint"],
                    )
                    valid, reason, metadata = _validate_complete_run(
                        run_dir,
                        seed=int(seed),
                        checkpoint=int(checkpoint),
                        panel_fingerprint=payload["panel_fingerprint"],
                    )
                    if not valid:
                        raise RuntimeError(
                            f"V7 run returned but cell did not validate complete: "
                            f"seed={seed} checkpoint={checkpoint} reason={reason}"
                        )
                    _write_completion_marker(run_dir, metadata, backfilled=False)
                    executed_cells.append({"seed": int(seed), "checkpoint": int(checkpoint)})
            _write_json_atomic(out_root / "v7_panels.json", panel_info)

        cells = _discover_run_cells(out_root)
        complete_cells = _completed_cell_tuples(cells)
        if not complete_cells:
            raise RuntimeError("No complete V7 cells are available under --out-root")
        mismatched = [
            str(_run_dir(out_root, seed, checkpoint))
            for seed, checkpoint in complete_cells
            if not _cell_evidence_matches(_run_dir(out_root, seed, checkpoint), args)
        ]
        if mismatched:
            raise RuntimeError(
                "aggregate contains cells from a different evidence layer; "
                f"use a fresh output root: {mismatched[:3]}"
            )

        pair_df, state_df, summary_df = _read_cells(out_root, complete_cells)
        consistency = _assert_panel_consistency(pair_df)
        _write_json_atomic(out_root / "v7_panel_consistency.json", consistency)
        if not consistency["pass"]:
            raise RuntimeError(
                "V7 fixed-panel oracle invariance failed; do not interpret checkpoint comparisons"
            )

        seed_summary = _seed_checkpoint_summary(pair_df, state_df, summary_df)
        checkpoint_summary = _checkpoint_summary(seed_summary)
        pair_df.to_csv(out_root / "v7_pair_panel.csv", index=False)
        state_df.to_csv(out_root / "v7_state_panel.csv", index=False)
        seed_summary.to_csv(out_root / "v7_seed_checkpoint_summary.csv", index=False)
        checkpoint_summary.to_csv(out_root / "v7_checkpoint_summary.csv", index=False)
        reporting = _write_reporting_outputs(
            out_root, pair_df, state_df, checkpoint_summary,
            evidence_class=args.evidence_class, evidence_protocol=_evidence_protocol(args),
        )

        hard_gates = {
            "fixed_panel_oracle_invariance_pass": bool(consistency["pass"]),
            "local_extrema_theorem_violation_count": int(pair_df["extrema_stability_violation"].sum()),
            "capacity_q_error_bound_violation_count": int(pair_df["capacity_q_error_bound_violation"].sum()),
            "topk_q_certificate_violation_count": int(state_df["capacity_topk_q_certified_violation"].sum()),
            "topk_interval_certificate_violation_count": int(state_df["capacity_topk_interval_certified_violation"].sum()),
            "direction_sign_certificate_violation_count": int(pair_df["direction_sign_violation"].sum()),
            "capacity_head_q_range_consistency_max_abs": float(pair_df["capacity_head_q_range_consistency_abs"].max()),
            "direction_head_q_consistency_max_abs": float(pair_df["direction_head_q_consistency_abs"].max()),
            "oracle_direction_q_consistency_max_abs": float(pair_df["oracle_direction_q_consistency_abs"].max()),
            "aggregated_complete_cell_count": int(len(complete_cells)),
        }
        hard_gates["all_deterministic_checks_pass"] = bool(
            hard_gates["fixed_panel_oracle_invariance_pass"]
            and hard_gates["local_extrema_theorem_violation_count"] == 0
            and hard_gates["capacity_q_error_bound_violation_count"] == 0
            and hard_gates["topk_q_certificate_violation_count"] == 0
            and hard_gates["topk_interval_certificate_violation_count"] == 0
            and hard_gates["direction_sign_certificate_violation_count"] == 0
            and hard_gates["capacity_head_q_range_consistency_max_abs"] <= 1e-6
            and hard_gates["direction_head_q_consistency_max_abs"] <= 1e-6
            and hard_gates["oracle_direction_q_consistency_max_abs"] <= 1e-9
        )
        _write_json_atomic(out_root / "v7_hard_gates.json", hard_gates)
        if not hard_gates["all_deterministic_checks_pass"]:
            raise RuntimeError("V7 deterministic consistency gate failed")

        completed_checkpoints = sorted(int(x) for x in seed_summary["checkpoint"].unique())
        completion_manifest = _completion_payload(out_root, args, cells)
        completion_summary = {
            "evidence_protocol": _evidence_protocol(args),
            "evidence_class": str(args.evidence_class),
            "development_only": _development_only(args),
            "expected_seeds": completion_manifest["expected_seeds"],
            "expected_checkpoints": completion_manifest["expected_checkpoints"],
            "completed_checkpoints": completion_manifest["completed_checkpoints"],
            "partially_completed_checkpoints": completion_manifest["partially_completed_checkpoints"],
            "completed_cells": completion_manifest["completed_cells"],
            "incomplete_cells": completion_manifest["incomplete_cells"],
            "aggregate_contains_only_validated_complete_cells": True,
        }
        _write_json_atomic(out_root / "v7_completion_status.json", completion_summary)

        analysis = {
            "protocol": V7_PROTOCOL,
            "evidence_protocol": _evidence_protocol(args),
            "evidence_class": str(args.evidence_class),
            "report_schema": V7_REPORT_SCHEMA,
            "development_only": _development_only(args),
            "hard_gates": hard_gates,
            "completion": completion_summary,
            "reporting_outputs": reporting["report"].get("output_tables", {}),
            "seed_heterogeneity": {
                str(checkpoint): _heterogeneity(seed_summary, checkpoint)
                for checkpoint in completed_checkpoints
            },
            "interpretation_rules": [
                "lambda_C<0.5 certifies only within-relation extrema identity.",
                "Global C/TopK stability additionally depends on between-relation score margins.",
                "Checkpoint learning curves are interpretable only across hash-identical completed panel cells.",
                "Partial checkpoints remain development previews until every expected seed is complete.",
                "lambda_D<1 is a sign certificate, not a magnitude-ranking certificate.",
            ],
        }
        _write_json_atomic(out_root / "v7_analysis.json", analysis)

        final_cells = _discover_run_cells(out_root)
        final_manifest = _completion_payload(out_root, args, final_cells)
        # Preserve the in-progress invocation and mark it complete.
        current = _load_json_if_exists(out_root / "v7_manifest.json") or {}
        final_manifest["invocations"] = current.get("invocations", [])
        _write_json_atomic(out_root / "v7_manifest.json", final_manifest)
        _set_invocation_status(
            out_root,
            invocation_id,
            "success",
            finished_at_utc=datetime.now(timezone.utc).isoformat(),
            executed_cells=executed_cells,
            skipped_complete_cells=skipped_cells,
            aggregated_complete_cell_count=int(len(complete_cells)),
        )

        print("[V7] fixed-panel consistency: PASS")
        print("[V7] deterministic theorem checks: PASS")
        print(
            f"[V7] cumulative aggregate: {len(complete_cells)} complete cells; "
            f"full checkpoints={completion_summary['completed_checkpoints']}; "
            f"partial checkpoints={completion_summary['partially_completed_checkpoints']}"
        )
        print(f"[V7] results: {out_root}")
    except KeyboardInterrupt:
        cells = _discover_run_cells(out_root)
        manifest = _completion_payload(out_root, args, cells)
        current = _load_json_if_exists(out_root / "v7_manifest.json") or {}
        manifest["invocations"] = current.get("invocations", [])
        _write_json_atomic(out_root / "v7_manifest.json", manifest)
        _set_invocation_status(
            out_root,
            invocation_id,
            "interrupted",
            finished_at_utc=datetime.now(timezone.utc).isoformat(),
            executed_cells=executed_cells,
            skipped_complete_cells=skipped_cells,
        )
        raise
    except Exception as exc:
        cells = _discover_run_cells(out_root)
        manifest = _completion_payload(out_root, args, cells)
        current = _load_json_if_exists(out_root / "v7_manifest.json") or {}
        manifest["invocations"] = current.get("invocations", [])
        _write_json_atomic(out_root / "v7_manifest.json", manifest)
        _set_invocation_status(
            out_root,
            invocation_id,
            "failed",
            finished_at_utc=datetime.now(timezone.utc).isoformat(),
            error=f"{type(exc).__name__}: {exc}",
            executed_cells=executed_cells,
            skipped_complete_cells=skipped_cells,
        )
        raise


if __name__ == "__main__":
    main()
