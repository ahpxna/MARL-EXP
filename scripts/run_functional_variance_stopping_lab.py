"""Fixed-confidence Functional-C acquisition with unknown variances.

This runner replaces the scientific use of the historical fixed-budget
``C_successive`` comparison.  Deployable strategies must learn both extrema
and noise; ``C_known_sigma`` is retained only as an oracle ceiling.  The
primary endpoint is total intervention count at a valid Top-K certificate,
not plug-in C MAE.
"""
from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

import numpy as np
from scipy.stats import norm, t as student_t

from research_chains.provenance import write_artifact_with_provenance

PROTOCOL_VERSION = "functional_variance_stopping_v1"
DEPLOYABLE = ("uniform", "C_split", "C_pilot", "C_shrink", "C_anytime")
DIAGNOSTIC = ("C_known_sigma",)
VARIANTS = DEPLOYABLE + DIAGNOSTIC


def _prefix_stats(streams: np.ndarray, counts: np.ndarray, offset: int = 0):
    R, K = counts.shape
    means = np.zeros((R, K), float)
    sigmas = np.zeros((R, K), float)
    for r in range(R):
        for a in range(K):
            x = streams[r, a, offset : offset + int(counts[r, a])]
            means[r, a] = float(np.mean(x))
            sigmas[r, a] = float(np.std(x, ddof=1)) if len(x) >= 2 else float("inf")
    return means, sigmas


def _intervals(means, sigma_hat, counts, *, alpha, looks, true_sigma=None):
    cells = int(means.size)
    tail = max(1e-15, float(alpha) / (2.0 * cells * max(1, int(looks))))
    if true_sigma is not None:
        critical = float(norm.ppf(1.0 - tail))
        radius = critical * np.asarray(true_sigma, float) / np.sqrt(counts)
    else:
        critical = np.vectorize(lambda n: float(student_t.ppf(1.0 - tail, max(1, int(n) - 1))))(counts)
        radius = critical * sigma_hat / np.sqrt(counts)
    return means - radius, means + radius, radius


def _capacity_intervals(lower, upper):
    c_lo = np.maximum(0.0, np.max(lower, axis=1) - np.min(upper, axis=1))
    c_hi = np.max(upper, axis=1) - np.min(lower, axis=1)
    return c_lo, c_hi


def _certificate(means, lower, upper, k):
    scores = np.ptp(means, axis=1)
    chosen = np.argsort(-scores, kind="stable")[: int(k)]
    outside = np.asarray([j for j in range(len(scores)) if j not in set(chosen)], int)
    c_lo, c_hi = _capacity_intervals(lower, upper)
    certified = bool(outside.size == 0 or np.min(c_lo[chosen]) > np.max(c_hi[outside]))
    return chosen, certified, c_lo, c_hi


def _driver_cells(means, lower, upper, relations):
    cells = []
    for r in relations:
        # These four cells drive the outer/inner capacity interval endpoints.
        cells.extend(((r, int(np.argmax(upper[r]))), (r, int(np.argmin(lower[r]))),
                      (r, int(np.argmax(lower[r]))), (r, int(np.argmin(upper[r])))))
    return list(dict.fromkeys(cells))


def _balanced_counts(total, R, K, minimum=2):
    total = max(int(total), int(minimum) * R * K)
    q, rem = divmod(total, R * K)
    out = np.full((R, K), q, int)
    out.flat[:rem] += 1
    return out


def _allocate_batch(variant, n_add, means, sigmas, lower, upper, counts, k,
                    fixed_drivers=None, fixed_scale=None):
    R, K = counts.shape
    draw = np.zeros_like(counts)
    if variant == "uniform":
        for t in range(int(n_add)):
            draw.flat[t % (R * K)] += 1
        return draw

    if variant in {"C_pilot", "C_shrink", "C_split"}:
        drivers = fixed_drivers or [(r, a) for r in range(R) for a in range(K)]
        scale = np.asarray(fixed_scale if fixed_scale is not None else sigmas, float)
        # Keep 20% uniform exploration so every capacity interval can contract.
        explore = int(math.ceil(0.2 * int(n_add)))
        for t in range(explore):
            draw.flat[t % (R * K)] += 1
        weighted = sorted(drivers, key=lambda x: (-float(scale[x]), x))
        for t in range(int(n_add) - explore):
            draw[weighted[t % len(weighted)]] += 1
        return draw

    # Anytime policies focus on relations that can still cross the current
    # Top-K boundary, then sample the largest confidence-radius driver.
    scores = np.ptp(means, axis=1)
    chosen = np.argsort(-scores, kind="stable")[: int(k)]
    _, c_hi = _capacity_intervals(lower, upper)
    threshold = float(np.min(_capacity_intervals(lower, upper)[0][chosen]))
    candidates = [r for r in range(R) if r in set(chosen) or c_hi[r] >= threshold]
    drivers = _driver_cells(means, lower, upper, candidates)
    working = counts.copy()
    for _ in range(int(n_add)):
        cell = max(drivers, key=lambda x: (float(sigmas[x]) / math.sqrt(float(working[x])), -x[0], -x[1]))
        draw[cell] += 1
        working[cell] += 1
    return draw


def _one_variant(truth, true_sigma, streams, variant, *, k, alpha, max_n,
                 batch, pilot_fraction):
    R, K = truth.shape
    initial = 2 * R * K
    # The allocation and stopping time are data-dependent.  A Bonferroni factor
    # over only the realized checkpoint count would therefore be invalid.  We
    # cover every possible per-cell sample size 2..max_n; fixed-n Student/normal
    # intervals plus this finite union remain valid under adaptive sampling.
    covered_sample_sizes = int(max_n)
    pilot_total = min(int(max_n), max(initial, int(math.ceil(float(pilot_fraction) * int(max_n)))))
    split_offset = pilot_total // (R * K) if variant == "C_split" else 0
    counts = _balanced_counts(initial if variant in {"uniform", "C_anytime", "C_known_sigma"} else pilot_total, R, K)
    if variant == "C_split":
        selection_counts = counts.copy()
        pilot_means, pilot_sigmas = _prefix_stats(streams, selection_counts, 0)
        pilot_ci_counts = selection_counts
        counts = np.full((R, K), 2, int)
        budget_used = int(selection_counts.sum() + counts.sum())
        offset = int(np.max(selection_counts))
    else:
        pilot_means, pilot_sigmas = _prefix_stats(streams, counts, 0)
        pilot_ci_counts = counts
        budget_used = int(counts.sum())
        offset = 0

    pooled = np.sqrt(0.5 * pilot_sigmas ** 2 + 0.5 * float(np.mean(pilot_sigmas ** 2)))
    pilot_lower, pilot_upper, _ = _intervals(
        pilot_means, pilot_sigmas, np.maximum(pilot_ci_counts, 2), alpha=alpha,
        looks=covered_sample_sizes,
        true_sigma=np.broadcast_to(true_sigma, truth.shape) if variant == "C_known_sigma" else None,
    )
    pilot_scores = np.ptp(pilot_means, axis=1)
    order = np.argsort(-pilot_scores, kind="stable")
    boundary = order[: min(R, int(k) + 1)]
    fixed_drivers = _driver_cells(pilot_means, pilot_lower, pilot_upper, boundary)
    fixed_scale = pooled if variant == "C_shrink" else pilot_sigmas
    true_top = set(np.argsort(-np.ptp(truth, axis=1), kind="stable")[: int(k)])

    emitted = False
    false_safe = False
    final_width = float("inf")
    while budget_used <= int(max_n):
        means, sigma_hat = _prefix_stats(streams, counts, offset)
        sigma_for_allocation = (np.broadcast_to(true_sigma, truth.shape) if variant == "C_known_sigma"
                                else sigma_hat)
        lower, upper, radius = _intervals(
            means, sigma_hat, counts, alpha=alpha, looks=covered_sample_sizes,
            true_sigma=np.broadcast_to(true_sigma, truth.shape) if variant == "C_known_sigma" else None,
        )
        chosen, emitted, c_lo, c_hi = _certificate(means, lower, upper, k)
        final_width = float(np.mean(c_hi - c_lo))
        if emitted:
            false_safe = set(map(int, chosen)) != true_top
            break
        if budget_used >= int(max_n):
            break
        n_add = min(int(batch), int(max_n) - budget_used)
        draw = _allocate_batch(
            variant, n_add, means, sigma_for_allocation, lower, upper, counts.copy(), k,
            fixed_drivers=fixed_drivers, fixed_scale=fixed_scale,
        )
        counts += draw
        budget_used += int(draw.sum())

    return {
        "N_certificate": int(budget_used) if emitted else None,
        "censored_N_certificate": int(budget_used) if emitted else int(max_n) + 1,
        "certificate_emitted": bool(emitted),
        "false_safe": bool(false_safe) if emitted else None,
        "final_mean_capacity_interval_width": final_width,
        "pilot_fraction": float(pilot_fraction) if variant in {"C_split", "C_pilot", "C_shrink"} else 0.0,
        "known_sigma_used": bool(variant == "C_known_sigma"),
        "counts": counts.tolist(),
    }


def run(instances=200, seeds=(100, 101, 102, 103, 104), relations=5, actions=6,
        topk=2, alpha=.05, max_n=16384, batch=16, pilot_fraction=.15):
    if not 0.10 <= float(pilot_fraction) <= 0.20:
        raise ValueError("pilot_fraction must be in [0.10, 0.20]")
    if int(max_n) < 4 * int(relations) * int(actions):
        raise ValueError("max_n is too small for split selection/evaluation")
    rows = {v: [] for v in VARIANTS}
    for seed in seeds:
        rng = np.random.default_rng(int(seed))
        for _ in range(int(instances)):
            capacities = np.sort(rng.uniform(.35, 2.0, size=int(relations)))[::-1]
            # Avoid exact relation ties; the experiment studies certification cost.
            capacities -= np.arange(int(relations)) * 1e-3
            truth = np.zeros((int(relations), int(actions)), float)
            for r, cap in enumerate(capacities):
                center = float(rng.normal(scale=.3))
                truth[r] = rng.uniform(center-cap/2, center+cap/2, size=int(actions))
                truth[r, 0], truth[r, -1] = center-cap/2, center+cap/2
            sigma = rng.uniform(.15, .85, size=int(actions))
            # Common streams make strategy comparisons matched at world/seed level.
            stream_length = int(max_n) + int(math.ceil(float(pilot_fraction) * int(max_n) / (int(relations) * int(actions)))) + 8
            streams = rng.normal(
                loc=truth[:, :, None], scale=sigma[None, :, None],
                size=(int(relations), int(actions), stream_length),
            )
            for variant in VARIANTS:
                result = _one_variant(
                    truth, sigma, streams, variant, k=int(topk), alpha=float(alpha),
                    max_n=int(max_n), batch=int(batch), pilot_fraction=float(pilot_fraction),
                )
                result.update({"seed": int(seed), "variant": variant})
                rows[variant].append(result)
    summary = {}
    for variant, rr in rows.items():
        emitted = [x for x in rr if x["certificate_emitted"]]
        censored = [x["censored_N_certificate"] for x in rr]
        summary[variant] = {
            # Historical field retained for artifact compatibility.  It is a
            # median of right-censored times, not a valid tie-breaker when <50%
            # of runs emit a certificate.
            "median_N_certificate": float(np.median(censored)),
            "median_censored_N_certificate": float(np.median(censored)),
            "restricted_mean_censored_N_certificate": float(np.mean(censored)),
            "certificate_fraction": float(np.mean([x["certificate_emitted"] for x in rr])),
            "false_safe_count": int(sum(x["false_safe"] is True for x in rr)),
            "false_safe_rate_among_emitted": float(np.mean([x["false_safe"] for x in emitted])) if emitted else None,
            "mean_final_capacity_interval_width": float(np.mean([x["final_mean_capacity_interval_width"] for x in rr])),
        }
    med = {v: summary[v]["median_censored_N_certificate"] for v in DEPLOYABLE}
    best_med = min(med.values())
    tied = [v for v in DEPLOYABLE if abs(med[v] - best_med) <= 1e-12]
    # A median at max_n+1 means at least half the runs are censored.  Calling
    # the first tuple entry a "winner" in that regime was a stale-analysis bug
    # (it reported uniform simply because uniform is first in DEPLOYABLE).
    winner = tied[0] if len(tied) == 1 and best_med <= int(max_n) else None
    winner_status = "IDENTIFIED_BY_MEDIAN" if winner is not None else (
        "NO_MEDIAN_IDENTIFIED_CENSORING" if best_med > int(max_n) else "NO_MEDIAN_IDENTIFIED_TIE"
    )
    secondary_order = sorted(DEPLOYABLE, key=lambda v: (
        -summary[v]["certificate_fraction"],
        summary[v]["restricted_mean_censored_N_certificate"],
        summary[v]["mean_final_capacity_interval_width"],
        v,
    ))
    return {
        "protocol_version": PROTOCOL_VERSION,
        "development_only": True,
        "primary_endpoint": "N_certificate",
        "scientific_headline": "query/functional geometry controls certification complexity",
        "common_random_streams": True,
        "fixed_confidence": float(1.0-alpha),
        "confidence_method": "finite-horizon Bonferroni over every possible per-cell sample size; fixed-n Student t (unknown sigma) or normal (oracle known sigma)",
        "adaptive_stopping_coverage_contract": "union over n=2..max_n, not realized-look-only calibration",
        "pilot_fraction": float(pilot_fraction),
        "deployable_variants": list(DEPLOYABLE),
        "diagnostic_variants": list(DIAGNOSTIC),
        "known_sigma_policy": "oracle diagnostic ceiling only; excluded from deployable winner",
        "instances_per_seed": int(instances), "seeds": list(map(int, seeds)),
        "relations": int(relations), "actions": int(actions), "topk": int(topk),
        "max_n": int(max_n), "by_variant": summary,
        "deployable_winner_by_median_N_certificate": winner,
        "deployable_winner_status": winner_status,
        "deployable_secondary_order": secondary_order,
        "censoring_note": "do not name a median-N winner when the best median is max_n+1 or tied; certificate_fraction/RMST-like summaries are secondary diagnostics",
    }


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--instances", type=int, default=200)
    p.add_argument("--seeds", nargs="+", type=int, default=[100,101,102,103,104])
    p.add_argument("--relations", type=int, default=5)
    p.add_argument("--actions", type=int, default=6)
    p.add_argument("--topk", type=int, default=2)
    p.add_argument("--alpha", type=float, default=.05)
    p.add_argument("--max-n", type=int, default=16384)
    p.add_argument("--batch", type=int, default=16)
    p.add_argument("--pilot-fraction", type=float, default=.15)
    p.add_argument("--out", default="research/high_value_extensions/functional/variance_stopping.json")
    a = p.parse_args(argv)
    payload = run(a.instances, tuple(a.seeds), a.relations, a.actions, a.topk,
                  a.alpha, a.max_n, a.batch, a.pilot_fraction)
    write_artifact_with_provenance(Path(a.out),payload,protocol={"protocol_version":PROTOCOL_VERSION,
        "relations":a.relations,"actions":a.actions,"topk":a.topk,"alpha":a.alpha,
        "max_n":a.max_n,"batch":a.batch,"pilot_fraction":a.pilot_fraction},
        evidence_class="DEVELOPMENT_EMPIRICAL",chain="FUNCTIONAL")
    print(json.dumps(payload, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
