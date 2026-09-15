"""Fixed-confidence Functional-C acquisition, with the v3 world confound removed.

v3's generator sorted capacities descending by relation index and pinned the
minimum and maximum to actions 0 and K-1.  Two consequences made that panel
unable to support a Top-C learning claim:

* the true Top-k was ALWAYS {0, ..., k-1}, and `chosen` is taken with
  `np.argsort(-scores, kind="stable")`, whose tie-break favours low indices --
  so a policy with ZERO information already guessed the right set, and
  `false_safe = 0` was partly guaranteed by construction rather than by the
  certificate;
* argmin and argmax were known a priori, so no policy ever had to learn where
  the extrema sit.

v4 changes only the generator and the reporting, never the certificate, the
intervals, the Bonferroni contract or the allocation rules, so the v3 numbers
remain comparable as the degenerate special case `--no-permute --fixed-extrema`.

Four additions, in the order they were demanded:
  1. `--permute` (default): relations are randomly permuted, so the true Top-k
     is a random k-subset;
  2. `--random-extrema` (default): the minimising and maximising actions are
     drawn per relation, so extrema positions must be learned;
  3. `--extrema-shift F`: after the world is drawn, a fraction F of relations
     has its extrema pair resampled and the values moved accordingly, so a
     policy that locked on early extrema is wrong;
  4. TWO comparators, which answer different questions and must not be confused:
     * `C_lucb` is the SAME-INFORMATION, SAME-GUARANTEE baseline: identical
       observations, identical Bonferroni certificate, identical confidence,
       differing only in allocation.  It spends its batch on the pair that
       decides the certificate -- the weakest relation inside the current Top-k
       and the strongest outside it.  This is the standard confidence-bound
       comparator; `uniform` alone is too weak to defend a claim against the
       unknown-variance allocation literature.  It is DEPLOYABLE.
     * `C_extrema_oracle` is NOT a same-information baseline.  It is TOLD
       argmin/argmax and forms its capacity interval from those two cells only:
       strictly more information, so it is a diagnostic ceiling that isolates
       what not knowing the extrema costs.  It is DIAGNOSTIC and is excluded
       from any deployable comparison.

`zero_information_accuracy` is reported on every run.  Under v3 it is 1.0;
under v4 it must be about 1/C(R,k).  A panel whose value drifts back toward 1
has reintroduced the confound.
"""
from __future__ import annotations

import argparse
import hashlib
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

PROTOCOL_VERSION = "functional_variance_stopping_v4_permuted_random_extrema"
# Frozen confirmatory seeds (config/ieee_benchmark_protocol_v1.json).
# Admissibility is COMPUTED from the seeds actually used. It is never hard-coded.
FROZEN_CONFIRMATORY_SEEDS = (701, 709, 719, 727, 733, 743, 751, 757, 761, 769)

_ADM_NOTE = (
    "Replaces the field development_only, which was a hard-coded True in every artifact "
    "this lab produced before 2026-09-12 (v3 line 324, v4 line 479) and therefore "
    "distinguished nothing, including in runs already cited as evidence. A run that "
    "touches a frozen seed without being the full confirmatory panel is a peek and is "
    "recorded as one."
)


def admissibility_record(seeds, max_n, rng_protocol):
    used = tuple(seeds)
    touched = sorted(set(used) & set(FROZEN_CONFIRMATORY_SEEDS))
    exact = used == FROZEN_CONFIRMATORY_SEEDS
    peek = bool(touched) and not exact
    return {
        "class": ("CONFIRMATORY" if exact
                  else "DEVELOPMENT_PEEKING_AT_FROZEN_SEEDS" if peek
                  else "DEVELOPMENT"),
        "uses_exactly_the_frozen_seed_set": exact,
        "frozen_seeds_touched": touched,
        "peeks_at_frozen_seeds_without_being_confirmatory": peek,
        "seeds_used": list(used),
        "max_n": max_n,
        "rng_protocol": rng_protocol,
        "note": _ADM_NOTE,
    }
DEPLOYABLE = ("uniform", "C_lucb", "C_split", "C_pilot", "C_shrink", "C_anytime")
DIAGNOSTIC = ("C_known_sigma", "C_extrema_oracle")
VARIANTS = DEPLOYABLE + DIAGNOSTIC


def _prefix_stats(streams: np.ndarray, counts: np.ndarray, offset: int = 0):
    R, K = counts.shape
    means = np.zeros((R, K), float)
    sigmas = np.zeros((R, K), float)
    for r in range(R):
        for a in range(K):
            x = streams[r, a, offset : offset + int(counts[r, a])]
            # NumPy truncates an over-range slice silently, but counts[r,a] still
            # enters radius = c*sigma_hat/sqrt(n); a short read would shrink the
            # radius and emit an INVALID certificate with no error anywhere.
            assert len(x) == int(counts[r, a]), (
                "stream exhausted", r, a, offset, len(x), int(counts[r, a]))
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
        critical = student_t.ppf(1.0 - tail, np.maximum(np.asarray(counts, int) - 1, 1))
        radius = critical * sigma_hat / np.sqrt(counts)
    return means - radius, means + radius, radius


def _capacity_intervals(lower, upper):
    c_lo = np.maximum(0.0, np.max(lower, axis=1) - np.min(upper, axis=1))
    c_hi = np.max(upper, axis=1) - np.min(lower, axis=1)
    return c_lo, c_hi


def _certificate(means, lower, upper, k, extrema=None):
    """`extrema` is the diagnostic oracle's extra information: when supplied,
    the capacity interval is formed from the two KNOWN extremal cells instead
    of from the max/min over all cells.  Both forms bracket the true capacity;
    the oracle's is tighter only because it needs no search."""
    if extrema is None:
        scores = np.ptp(means, axis=1)
        c_lo, c_hi = _capacity_intervals(lower, upper)
    else:
        idx = np.arange(means.shape[0])
        lo_a, hi_a = extrema[:, 0], extrema[:, 1]
        scores = means[idx, hi_a] - means[idx, lo_a]
        c_lo = np.maximum(0.0, lower[idx, hi_a] - upper[idx, lo_a])
        c_hi = upper[idx, hi_a] - lower[idx, lo_a]
    chosen = np.argsort(-scores, kind="stable")[: int(k)]
    outside = np.asarray([j for j in range(len(scores)) if j not in set(chosen)], int)
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
                    fixed_drivers=None, fixed_scale=None, extrema=None):
    R, K = counts.shape
    draw = np.zeros_like(counts)
    if variant == "uniform":
        # Continue across batches; restarting at zero starves cells when batch < R*K.
        start = int(counts.sum())
        for t in range(int(n_add)):
            draw.flat[(start + t) % (R * K)] += 1
        return draw

    # Every adaptive policy reserves >=20% of each batch for the least-sampled
    # cells. A cell cannot remain at its initial count while sampling continues.
    working = counts.copy()
    explore = min(int(n_add), int(math.ceil(0.2 * int(n_add))))
    for _ in range(explore):
        cell = int(np.argmin(working))
        draw.flat[cell] += 1
        working.flat[cell] += 1

    if variant in {"C_pilot", "C_shrink", "C_split"}:
        drivers = fixed_drivers or [(r, a) for r in range(R) for a in range(K)]
        scale = np.maximum(np.asarray(fixed_scale if fixed_scale is not None else sigmas, float), 1e-12)
        # Greedily reduce sum_i sigma_i^2/n_i. The marginal gain is
        # sigma_i^2/[n_i(n_i+1)], so magnitudes affect allocation (Neyman rule).
        # Pilot and shrink use exactly the same drivers/exploration policy.
        for _ in range(int(n_add) - explore):
            cell = max(drivers, key=lambda x: (
                float(scale[x]) ** 2 / (float(working[x]) * (float(working[x]) + 1)),
                -x[0], -x[1]))
            draw[cell] += 1
            working[cell] += 1
        return draw

    if variant == "C_lucb":
        # Literature-standard confidence-bound baseline, adapted to capacities.
        # SAME observations, SAME Bonferroni certificate, SAME confidence as every
        # deployable policy -- it differs only in where it spends the batch.  It
        # targets the pair that actually decides the certificate: the weakest
        # relation inside the current Top-k and the strongest one outside it,
        # then samples the most uncertain driver cell of that pair.  This is the
        # comparator a reviewer will ask for; `uniform` is not.
        scores = np.ptp(means, axis=1)
        order = np.argsort(-scores, kind="stable")
        inside, outside = order[: int(k)], order[int(k):]
        c_lo, c_hi = _capacity_intervals(lower, upper)
        pair = [int(inside[np.argmin(c_lo[inside])])]
        if outside.size:
            pair.append(int(outside[np.argmax(c_hi[outside])]))
        drivers = _driver_cells(means, lower, upper, pair)
        for _ in range(int(n_add) - explore):
            cell = max(drivers, key=lambda x: (
                float(sigmas[x]) / math.sqrt(float(working[x])), -x[0], -x[1]))
            draw[cell] += 1
            working[cell] += 1
        return draw

    if variant == "C_extrema_oracle" and extrema is not None:
        idx = np.arange(R)
        lo_a, hi_a = extrema[:, 0], extrema[:, 1]
        scores = means[idx, hi_a] - means[idx, lo_a]
        c_lo = np.maximum(0.0, lower[idx, hi_a] - upper[idx, lo_a])
        c_hi = upper[idx, hi_a] - lower[idx, lo_a]
    else:
        scores = np.ptp(means, axis=1)
        c_lo, c_hi = _capacity_intervals(lower, upper)
    chosen = np.argsort(-scores, kind="stable")[: int(k)]
    threshold = float(np.min(c_lo[chosen]))
    candidates = [r for r in range(R) if r in set(chosen) or c_hi[r] >= threshold]
    if variant == "C_extrema_oracle" and extrema is not None:
        drivers = list(dict.fromkeys(
            [(r, int(extrema[r, 0])) for r in candidates]
            + [(r, int(extrema[r, 1])) for r in candidates]))
    else:
        drivers = _driver_cells(means, lower, upper, candidates)
    for _ in range(int(n_add) - explore):
        cell = max(drivers, key=lambda x: (float(sigmas[x]) / math.sqrt(float(working[x])), -x[0], -x[1]))
        draw[cell] += 1
        working[cell] += 1
    return draw


def _one_variant(truth, true_sigma, streams, variant, *, k, alpha, max_n,
                 batch, pilot_fraction, extrema=None):
    R, K = truth.shape
    initial = 2 * R * K
    # The allocation and stopping time are data-dependent.  A Bonferroni factor
    # over only the realized checkpoint count would therefore be invalid.  We
    # cover every possible per-cell sample size 2..max_n; fixed-n Student/normal
    # intervals plus this finite union remain valid under adaptive sampling.
    covered_sample_sizes = int(max_n)
    pilot_total = min(int(max_n), max(initial, int(math.ceil(float(pilot_fraction) * int(max_n)))))
    split_offset = pilot_total // (R * K) if variant == "C_split" else 0
    counts = _balanced_counts(initial if variant in {"uniform", "C_anytime", "C_known_sigma", "C_extrema_oracle", "C_lucb"} else pilot_total, R, K)
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

    initial_counts = counts.copy()
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
        oracle_extrema = extrema if variant == "C_extrema_oracle" else None
        chosen, emitted, c_lo, c_hi = _certificate(means, lower, upper, k, oracle_extrema)
        final_width = float(np.mean(c_hi - c_lo))
        if emitted:
            false_safe = set(map(int, chosen)) != true_top
            break
        if budget_used >= int(max_n):
            break
        n_add = min(int(batch), int(max_n) - budget_used)
        draw = _allocate_batch(
            variant, n_add, means, sigma_for_allocation, lower, upper, counts.copy(), k,
            fixed_drivers=fixed_drivers, fixed_scale=fixed_scale, extrema=oracle_extrema,
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
        "known_extrema_used": bool(variant == "C_extrema_oracle"),
        "counts": counts.tolist(),
        "initial_counts": initial_counts.tolist(),
        "minimum_cell_samples": int(counts.min()),
        "cells_at_initial_count": int(np.sum(counts == initial_counts)),
        "true_topk_gap": float(np.sort(np.ptp(truth, axis=1))[::-1][k-1] - np.sort(np.ptp(truth, axis=1))[::-1][k]),
        "final_capacity_lower": c_lo.tolist(),
        "final_capacity_upper": c_hi.tolist(),
        "final_certificate_margin": float(np.min(c_lo[chosen]) - np.max(c_hi[[r for r in range(R) if r not in set(chosen)]])),
    }


def _draw_world(rng, relations, actions, permute=True, random_extrema=True,
                extrema_shift=0.0):
    """Draw a world.  `permute` randomises which relations are in the true
    Top-k; `random_extrema` randomises where the extrema sit; `extrema_shift`
    resamples the extrema of a fraction of relations after the fact."""
    capacities = np.sort(rng.uniform(.35, 2.0, size=relations))[::-1]
    capacities -= np.arange(relations) * 1e-3
    truth = np.zeros((relations, actions), float)
    extrema = np.zeros((relations, 2), int)
    centers = np.zeros(relations, float)
    for r, cap in enumerate(capacities):
        center = float(rng.normal(scale=.3))
        centers[r] = center
        truth[r] = rng.uniform(center-cap/2, center+cap/2, size=actions)
        if random_extrema:
            lo, hi = (int(x) for x in rng.choice(actions, size=2, replace=False))
        else:
            lo, hi = 0, actions - 1
        truth[r, lo], truth[r, hi] = center-cap/2, center+cap/2
        extrema[r] = (lo, hi)
    # Move the extrema of a fraction of relations, keeping each capacity fixed.
    n_shift = int(round(float(extrema_shift) * relations))
    if n_shift > 0:
        for r in rng.choice(relations, size=n_shift, replace=False):
            cap = capacities[r]; center = centers[r]
            truth[r] = rng.uniform(center-cap/2, center+cap/2, size=actions)
            lo, hi = (int(x) for x in rng.choice(actions, size=2, replace=False))
            truth[r, lo], truth[r, hi] = center-cap/2, center+cap/2
            extrema[r] = (lo, hi)
    perm = rng.permutation(relations) if permute else np.arange(relations)
    truth = truth[perm]
    extrema = extrema[perm]
    return truth, rng.uniform(.15, .85, size=actions), perm, extrema


def _instance_data(seed, instance_id, relations, actions, stream_length,
                   rng_protocol, legacy_rng=None, permute=True, random_extrema=True,
                   extrema_shift=0.0):
    """Separate world/cell RNGs make every horizon share the same noise prefixes.

    The legacy option reproduces old artifacts; its world RNG depends on how
    many noise samples preceding instances consumed, so cross-horizon pairing
    by (seed, instance_id) is invalid under that option.
    """
    if rng_protocol == "legacy_sequential":
        if legacy_rng is None:
            raise ValueError("legacy protocol requires its sequential RNG")
        truth, sigma, perm, extrema = _draw_world(legacy_rng, relations, actions,
            permute, random_extrema, extrema_shift)
        streams = legacy_rng.normal(truth[:, :, None], sigma[None, :, None],
                                    size=(relations, actions, stream_length))
    elif rng_protocol == "instance_cell_v1":
        truth_rng = np.random.default_rng(np.random.SeedSequence([seed, instance_id, 0]))
        truth, sigma, perm, extrema = _draw_world(truth_rng, relations, actions,
            permute, random_extrema, extrema_shift)
        streams = np.empty((relations, actions, stream_length))
        for r in range(relations):
            for a in range(actions):
                noise_rng = np.random.default_rng(np.random.SeedSequence([seed, instance_id, 1, r, a]))
                streams[r, a] = noise_rng.normal(truth[r, a], sigma[a], size=stream_length)
    else:
        raise ValueError(f"unknown RNG protocol: {rng_protocol}")
    digest = hashlib.sha256(truth.astype("<f8").tobytes() + sigma.astype("<f8").tobytes()).hexdigest()
    return truth, sigma, streams, digest, perm, extrema


def run(instances=200, seeds=(100, 101, 102, 103, 104), relations=5, actions=6,
        topk=2, alpha=.05, max_n=16384, batch=16, pilot_fraction=.15,
        rng_protocol="legacy_sequential", permute=True, random_extrema=True,
        extrema_shift=0.0):
    if int(batch) < 1 or int(instances) < 1 or not seeds:
        raise ValueError("positive batch/instances and nonempty seeds are required")
    if not 1 <= int(topk) < int(relations):
        raise ValueError("topk must satisfy 1 <= topk < relations")
    if not 0.10 <= float(pilot_fraction) <= 0.20:
        raise ValueError("pilot_fraction must be in [0.10, 0.20]")
    if int(max_n) < 4 * int(relations) * int(actions):
        raise ValueError("max_n is too small for split selection/evaluation")
    if not 0.0 <= float(extrema_shift) <= 1.0:
        raise ValueError("extrema_shift must be in [0, 1]")
    rows = {v: [] for v in VARIANTS}
    worlds = []
    for seed in seeds:
        rng = np.random.default_rng(int(seed))
        for instance_id in range(int(instances)):
            stream_length = int(max_n) + int(math.ceil(float(pilot_fraction) * int(max_n) / (int(relations) * int(actions)))) + 8
            truth, sigma, streams, world_sha, perm, extrema = _instance_data(
                int(seed), instance_id, int(relations), int(actions), stream_length,
                rng_protocol, rng, permute, random_extrema, extrema_shift)
            caps = np.ptp(truth, axis=1)
            true_top = sorted(int(i) for i in np.argsort(-caps, kind="stable")[: int(topk)])
            extrema_list = [[int(a), int(b)] for a, b in extrema]
            worlds.append({
                "seed": int(seed), "instance_id": instance_id,
                "world_sha256": world_sha,
                "true_topk": true_top,
                "relation_permutation": [int(x) for x in perm],
                "extrema_positions": extrema_list,
                "topk_is_leading_block": bool(true_top == list(range(int(topk)))),
                "extrema_at_endpoints": bool(all(
                    set(e) == {0, int(actions) - 1} for e in extrema_list)),
            })
            for variant in VARIANTS:
                result = _one_variant(
                    truth, sigma, streams, variant, k=int(topk), alpha=float(alpha),
                    max_n=int(max_n), batch=int(batch), pilot_fraction=float(pilot_fraction),
                    extrema=extrema,
                )
                result.update({"seed": int(seed), "instance_id": instance_id, "variant": variant,
                               "world_sha256": world_sha, "true_topk": true_top,
                               "relation_permutation": [int(x) for x in perm],
                               "extrema_positions": extrema_list})
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
    import math as _math
    n_worlds = len(worlds)
    naive_hits = sum(1 for w in worlds if w["topk_is_leading_block"])
    endpoint_hits = sum(1 for w in worlds if w["extrema_at_endpoints"])
    expected_naive = 1.0/_math.comb(int(relations), int(topk))
    world_audit = {
        "instances": n_worlds,
        # A policy with NO information guesses {0,...,k-1}; under v3's generator
        # that was right every time.  This is the number that must stay near
        # 1/C(R,k), and it is the guard against reintroducing the confound.
        "zero_information_accuracy": naive_hits/n_worlds if n_worlds else None,
        "zero_information_accuracy_expected_if_unbiased": expected_naive,
        "extrema_always_at_endpoints_fraction": endpoint_hits/n_worlds if n_worlds else None,
        "distinct_true_topk_sets": len({tuple(w["true_topk"]) for w in worlds}),
        "distinct_topk_sets_possible": _math.comb(int(relations), int(topk)),
        "permute_relations": bool(permute),
        "random_extrema": bool(random_extrema),
        "extrema_shift": float(extrema_shift),
        "confound_removed": bool(permute and random_extrema),
        "note": ("v3 reported zero_information_accuracy 1.0 and "
                 "extrema_always_at_endpoints_fraction 1.0; its Top-k claims are "
                 "therefore not supported by that panel."),
    }
    return {
        "protocol_version": PROTOCOL_VERSION,
        "admissibility": admissibility_record(seeds, max_n, rng_protocol),
        "development_only": tuple(seeds) != FROZEN_CONFIRMATORY_SEEDS,
        "world_audit": world_audit,
        "worlds": worlds,
        "primary_endpoint": "N_certificate",
        "scientific_headline": "query/functional geometry controls certification complexity",
        "common_random_streams": True,
        "rng_protocol": rng_protocol,
        "cross_horizon_common_world_and_cell_prefixes": rng_protocol == "instance_cell_v1",
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
        "runs_by_variant": rows,
        "allocation_policy": "uniform round-robin; >=20% least-sampled exploration for every adaptive policy; fixed-driver exploitation maximizes sigma^2/[n(n+1)]",
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
    p.add_argument("--no-permute", action="store_true",
                   help="reproduce v3: true Top-k is always the leading block")
    p.add_argument("--fixed-extrema", action="store_true",
                   help="reproduce v3: extrema pinned to actions 0 and K-1")
    p.add_argument("--extrema-shift", type=float, default=0.0,
                   help="fraction of relations whose extrema are resampled after the draw")
    p.add_argument("--rng-protocol", choices=("legacy_sequential", "instance_cell_v1"),
                   default="instance_cell_v1",
                   help="use instance_cell_v1 for matched cross-horizon experiments; legacy reproduces old runs")
    p.add_argument("--allow-frozen-seed-peek", action="store_true",
                    help="record, rather than refuse, a non-confirmatory run that touches frozen seeds")
    p.add_argument("--out", default="research/high_value_extensions/functional/variance_stopping.json")
    a = p.parse_args(argv)
    _adm = admissibility_record(tuple(a.seeds), a.max_n, getattr(a, "rng_protocol", None))
    if _adm["peeks_at_frozen_seeds_without_being_confirmatory"] and not a.allow_frozen_seed_peek:
        raise SystemExit(
            "refusing: seeds %s are frozen confirmatory seeds, but this run is not the full "
            "confirmatory panel. This is exactly the look-before-freeze failure of 2026-09-11. "
            "Use non-frozen seeds, or pass --allow-frozen-seed-peek to record the peek in the "
            "artifact." % (_adm["frozen_seeds_touched"],))
    payload = run(a.instances, tuple(a.seeds), a.relations, a.actions, a.topk,
                  a.alpha, a.max_n, a.batch, a.pilot_fraction, a.rng_protocol,
                  permute=not a.no_permute, random_extrema=not a.fixed_extrema,
                  extrema_shift=a.extrema_shift)
    write_artifact_with_provenance(Path(a.out),payload,protocol={"protocol_version":PROTOCOL_VERSION,
        "relations":a.relations,"actions":a.actions,"topk":a.topk,"alpha":a.alpha,
        "max_n":a.max_n,"batch":a.batch,"pilot_fraction":a.pilot_fraction,"rng_protocol":a.rng_protocol,
        "permute":not a.no_permute,"random_extrema":not a.fixed_extrema,"extrema_shift":a.extrema_shift},
        evidence_class="DEVELOPMENT_EMPIRICAL",chain="FUNCTIONAL")
    print(json.dumps({k: v for k, v in payload.items()
                      if k not in ("runs_by_variant", "worlds")}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
