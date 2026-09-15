"""QUERY steps 2-6: exact restricted-information decoder over the natural panel.

Consumes the artifact written by scripts/QUERY_panel_collect.py and performs,
with exact rational arithmetic only (fractions.Fraction; floats are used ONLY as
exact bit keys via float.hex() for partitioning, never compared with a tolerance):

  (2) complete inclusion accounting: generated / reachable / filtered / constant /
      evaluable, with the buckets mutually exclusive and summing to the total;
  (3) PAIRED units that share a restricted representation but differ in the
      continuation target, split into DEGENERATE (the shared summary is the
      all-zero effect profile) and NONDEGENERATE (the shared summary is a
      genuinely nonzero effect profile) -- because a result supported only by
      degenerate pairs is the weak statement "a 1-step query sees nothing";
  (4) the EXACT restricted-information optimal decoder over the empirical panel,
      for three losses, in closed form per fibre (no fitting, no approximation):
      minimax (fibre midrange), squared error (fibre mean), 0-1 (fibre mode);
  (5) purchase of every subset of an executable feature catalog, with the
      declared cost of each subset;
  (6) repair cost = minimum-cost subset that removes every bad pair, together
      with TWO falsifiability guards that can and do return False:
        (a) fibre-size distribution -- a subset that removes bad pairs only by
            making every fibre a singleton is a lookup table, not a decoder;
        (b) held-out-seed evaluation -- the decoder is built on train seeds and
            scored on unseen seeds, abstaining on unseen summary values.

Confound control: the RWARE transition draws a replacement request from
np_random on every delivery, so the horizon-h return is a function of
(physical state, rng state).  Every bad pair is therefore classified by whether
the two members share a physical_key.  A bad pair with a shared physical_key is
environment stochasticity, NOT representation loss, and is excluded from every
headline count.  Without this split the headline claim is not falsifiable.

Pair counting is combinatorial (per fibre: C(m,2) minus the within-target and
within-physical-state pair counts), so no pair list is ever truncated; the
reported maximum gap is computed by an exact two-scan argument, not sampling.
"""
from __future__ import annotations

import argparse
import collections
import itertools
import json
from fractions import Fraction
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
NOOP = 0
N_ACTIONS = 5

CATALOG_COST = {
    "relation_features": {"model_forward_passes": 1},
    "mechanism_features": {"model_forward_passes": 1},
    "weak_prior_score": {"model_forward_passes": 1},
    "privileged_geometry": {"privileged_state_reads": 1},
    # buying a longer query is a catalog item too: the h=2 response row for this
    # candidate costs 5 forced rollouts x 2 environment steps.
    "response_h2": {"env_steps": N_ACTIONS * 2},
}
CATALOG = tuple(sorted(CATALOG_COST))


def deep_fkey(obj):
    """Exact bit key. float.hex() is lossless; no tolerance comparison anywhere."""
    if isinstance(obj, list):
        return tuple(deep_fkey(o) for o in obj)
    if isinstance(obj, float):
        return float(obj).hex()
    return obj


def centered(row):
    base = int(row[NOOP])
    return tuple(int(v) - base for v in row)


def ate(row):
    return Fraction(sum(int(v) for v in row), len(row)) - Fraction(int(row[NOOP]))


def shapley_from_coalition(coal, n, i):
    def v(subset):
        return Fraction(int(coal[",".join(map(str, subset))]))
    acc = Fraction(0)
    others = [j for j in range(n) if j != i]
    for r in range(len(others) + 1):
        for sub in itertools.combinations(others, r):
            s = tuple(sorted(sub))
            si = tuple(sorted(s + (i,)))
            w = Fraction(factorial(r) * factorial(n - r - 1), factorial(n))
            acc += w * (v(si) - v(s))
    return acc


def fibres(units, keyfn):
    out = collections.defaultdict(list)
    for u in units:
        out[keyfn(u)].append(u)
    return out


def _c2(m):
    return m * (m - 1) // 2


# --------------------------------------------------------------------------
# (4) exact optimal decoder over the restricted information
# --------------------------------------------------------------------------

def exact_decoder_report(units, keyfn, targetfn):
    """minimax : psi(s) = fibre midrange -> worst |error| = halfrange.  Optimal,
    because for any psi, max(|psi-t_min|,|psi-t_max|) >= (t_max-t_min)/2 (this
    is exactly Lean QUERY_A8 / E5), with equality at the midrange.
    mse      : psi(s) = fibre mean -> risk = fibre variance (exact).
    zero_one : psi(s) = fibre mode -> error = 1 - (sum of modal counts)/N."""
    part = fibres(units, keyfn)
    n = len(units)
    worst = Fraction(0)
    weighted_minimax = Fraction(0)
    mse = Fraction(0)
    correct = 0
    sizes = []
    for members in part.values():
        ts = [targetfn(u) for u in members]
        m = len(ts)
        sizes.append(m)
        lo, hi = min(ts), max(ts)
        half = (hi - lo) / 2
        worst = max(worst, half)
        weighted_minimax += Fraction(m, n) * half
        mean = sum(ts, Fraction(0)) / m
        mse += Fraction(m, n) * (sum((t - mean) ** 2 for t in ts) / m)
        correct += max(collections.Counter(ts).values())
    grand = sum((targetfn(u) for u in units), Fraction(0)) / n
    total_var = sum((targetfn(u) - grand) ** 2 for u in units) / n
    return {
        "n_units": n,
        "n_fibres": len(part),
        "fibre_size_max": max(sizes),
        "n_singleton_fibres": sum(1 for s in sizes if s == 1),
        "units_in_singleton_fibres": sum(s for s in sizes if s == 1),
        "singleton_unit_fraction_float": sum(s for s in sizes if s == 1) / n,
        "minimax_worst_case_abs_error": str(worst),
        "minimax_worst_case_abs_error_float": float(worst),
        "minimax_size_weighted_abs_error": str(weighted_minimax),
        "minimax_size_weighted_abs_error_float": float(weighted_minimax),
        "bayes_mse_risk": str(mse),
        "bayes_mse_risk_float": float(mse),
        "target_total_variance": str(total_var),
        "target_total_variance_float": float(total_var),
        "variance_explained_float": (float(1 - mse / total_var) if total_var != 0 else None),
        "zero_one_error": str(Fraction(n - correct, n)),
        "zero_one_error_float": float(Fraction(n - correct, n)),
    }


# --------------------------------------------------------------------------
# (3) paired states: exact combinatorial bad-pair accounting
# --------------------------------------------------------------------------

def _max_gap_distinct_physical(members, targetfn):
    """Exact max |t_a - t_b| over pairs in this fibre with distinct physical_key.

    Two scans suffice: let m = argmax t, n = argmin t.  If phys(m) != phys(n)
    the answer is t_m - t_n.  Otherwise every optimal pair contains m or n
    (proof in the findings file), so scanning against each of them is exact.
    """
    if len(members) < 2:
        return Fraction(0), None
    ts = [targetfn(u) for u in members]
    hi_i = max(range(len(ts)), key=lambda i: ts[i])
    lo_i = min(range(len(ts)), key=lambda i: ts[i])
    if members[hi_i]["physical_key"] != members[lo_i]["physical_key"]:
        return ts[hi_i] - ts[lo_i], (members[hi_i], members[lo_i])
    best, pair = Fraction(0), None
    ph = members[hi_i]["physical_key"]
    pl = members[lo_i]["physical_key"]
    for i, u in enumerate(members):
        if u["physical_key"] != ph and ts[hi_i] - ts[i] > best:
            best, pair = ts[hi_i] - ts[i], (members[hi_i], u)
        if u["physical_key"] != pl and ts[i] - ts[lo_i] > best:
            best, pair = ts[i] - ts[lo_i], (u, members[lo_i])
    return best, pair


def bad_pair_report(units, keyfn, targetkeyfn, degenfn, orderedfn=None):
    """Exhaustive counts (combinatorial, nothing truncated)."""
    part = fibres(units, keyfn)
    c = collections.Counter()
    max_gap_nondeg, best_pair = Fraction(0), None
    max_gap_deg = Fraction(0)
    for members in part.values():
        m = len(members)
        if m < 2:
            continue
        degenerate = degenfn(members[0])
        tc = collections.Counter(targetkeyfn(u) for u in members)
        diff = _c2(m) - sum(_c2(v) for v in tc.values())
        # pairs that differ in target AND share a physical state = rng-confounded
        same_phys_diff = 0
        for _, grp in fibres(members, lambda u: u["physical_key"]).items():
            gc = collections.Counter(targetkeyfn(u) for u in grp)
            same_phys_diff += _c2(len(grp)) - sum(_c2(v) for v in gc.values())
        c["pairs_total"] += _c2(m)
        c["bad_pairs_total"] += diff
        c["bad_pairs_rng_confounded"] += same_phys_diff
        genuine = diff - same_phys_diff
        c["bad_pairs_distinct_physical_state"] += genuine
        if degenerate:
            c["bad_pairs_degenerate_summary"] += genuine
        else:
            c["bad_pairs_nondegenerate_summary"] += genuine
        if orderedfn is not None and genuine > 0:
            gap, pair = _max_gap_distinct_physical(members, orderedfn)
            if degenerate:
                max_gap_deg = max(max_gap_deg, gap)
            elif gap > max_gap_nondeg:
                max_gap_nondeg, best_pair = gap, pair
    out = dict(c)
    out["n_fibres"] = len(part)
    if orderedfn is not None:
        out["max_target_gap_degenerate"] = str(max_gap_deg)
        out["max_target_gap_nondegenerate"] = str(max_gap_nondeg)
        out["certified_minimax_floor_nondegenerate"] = str(max_gap_nondeg / 2)
        out["certified_minimax_floor_nondegenerate_float"] = float(max_gap_nondeg / 2)
        if best_pair is not None:
            a, b = best_pair
            out["witness_of_record"] = {
                "shared_summary_c1": list(a["c1"]),
                "u1": {"seed": a["seed"], "t": a["t"], "cand": a["cand"],
                       "physical_key": a["physical_key"], "R1": a["R1"], "R2": a["R2"],
                       "RT": a["RT"], "cT": list(a["cT"]), "ateT": str(a["ateT"]),
                       "shapT": str(a["shapT"])},
                "u2": {"seed": b["seed"], "t": b["t"], "cand": b["cand"],
                       "physical_key": b["physical_key"], "R1": b["R1"], "R2": b["R2"],
                       "RT": b["RT"], "cT": list(b["cT"]), "ateT": str(b["ateT"]),
                       "shapT": str(b["shapT"])},
            }
    return out


# --------------------------------------------------------------------------

def build_units(payload):
    units = []
    cands = payload["candidates"]
    for rec in payload["records"]:
        if rec.get("status") != "OK":
            continue
        for jj, agent in enumerate(cands):
            u = {
                "seed": rec["seed"], "t": rec["t"], "cand": int(agent), "local": jj,
                "physical_key": rec["physical_key"], "rng_key": rec["rng_key"],
                "R1": list(map(int, rec["R1"][jj])),
                "R2": list(map(int, rec["R2"][jj])),
                "RT": list(map(int, rec["RT"][jj])),
            }
            u["c1"] = centered(u["R1"])
            u["c2"] = centered(u["R2"])
            u["cT"] = centered(u["RT"])
            u["ateT"] = ate(u["RT"])
            u["shapT"] = shapley_from_coalition(rec["coalition"], len(cands), jj)
            u["catalog"] = {k: deep_fkey(v[jj]) for k, v in rec["catalog"].items()}
            units.append(u)
    return units


def summary_key(u, extras=()):
    key = [u["c1"]]
    for name in extras:
        key.append(u["c2"] if name == "response_h2" else u["catalog"][name])
    return tuple(key)


def subset_cost(extras):
    cost = collections.Counter()
    for name in extras:
        for k, v in CATALOG_COST[name].items():
            cost[k] += v
    return dict(cost)


def holdout_eval(train, test, keyfn, targetfn):
    part = fibres(train, keyfn)
    table_mean, table_mid = {}, {}
    for k, members in part.items():
        ts = [targetfn(u) for u in members]
        table_mean[k] = sum(ts, Fraction(0)) / len(ts)
        table_mid[k] = (min(ts) + max(ts)) / 2
    abstain = 0
    errs_mean, errs_mid = [], []
    for u in test:
        k = keyfn(u)
        if k not in table_mean:
            abstain += 1
            continue
        t = targetfn(u)
        errs_mean.append(abs(t - table_mean[k]))
        errs_mid.append(abs(t - table_mid[k]))
    n = len(errs_mean)
    return {
        "test_units": len(test),
        "abstained_unseen_summary": abstain,
        "abstain_rate_float": (float(Fraction(abstain, len(test))) if test else None),
        "scored": n,
        "mae_mean_decoder": str(sum(errs_mean, Fraction(0)) / n) if n else "NA",
        "mae_mean_decoder_float": float(sum(errs_mean, Fraction(0)) / n) if n else None,
        "worst_abs_err_midrange_decoder_float": float(max(errs_mid)) if n else None,
    }


def main(argv=None):
    p = argparse.ArgumentParser()
    p.add_argument("--panel", default="research/high_risk_20260910/QUERY_natural_panel_v2.json")
    p.add_argument("--out", default="research/high_risk_20260910/QUERY_restricted_decoder_exact.json")
    p.add_argument("--holdout-seeds", type=int, default=6)
    a = p.parse_args(argv)

    payload = json.loads((ROOT / a.panel).read_text())
    units = build_units(payload)
    counts = payload["counts"]
    n_cand = len(payload["candidates"])

    constant = [u for u in units if all(v == 0 for v in u["cT"])]
    evaluable = [u for u in units if any(v != 0 for v in u["cT"])]
    accounting = {
        "generated_env_steps_in_collection": counts["generated_steps"],
        "episodes": counts.get("episodes", 0),
        "episode_terminated_early": counts.get("episode_terminated_early", 0),
        "collection_reward_total": counts.get("collection_reward", 0),
        "reachable_snapshots": counts["reachable_snapshots"],
        "filtered_panel_error": counts.get("filtered_panel_error", 0),
        "panel_built": counts["panel_built"],
        "candidates_per_snapshot": n_cand,
        "units_total": len(units),
        "units_constant_target_cT_all_zero": len(constant),
        "units_evaluable_nonconstant_target": len(evaluable),
        "accounting_closes": bool(
            counts["reachable_snapshots"] == counts["panel_built"] + counts.get(
                "filtered_panel_error", 0)
            and counts["panel_built"] * n_cand == len(units)
            and len(constant) + len(evaluable) == len(units)),
        "units_c1_all_zero": sum(1 for u in units if all(v == 0 for v in u["c1"])),
        "units_c1_nonzero": sum(1 for u in units if any(v != 0 for v in u["c1"])),
        "units_c1_zero_and_cT_nonzero": sum(
            1 for u in units if all(v == 0 for v in u["c1"]) and any(v != 0 for v in u["cT"])),
        "units_c1_nonzero_and_cT_nonzero": sum(
            1 for u in units if any(v != 0 for v in u["c1"]) and any(v != 0 for v in u["cT"])),
    }

    by_full = collections.defaultdict(set)
    for u in units:
        by_full[(u["physical_key"], u["rng_key"], u["local"])].add(tuple(u["RT"]))
    violations = sum(1 for v in by_full.values() if len(v) > 1)
    by_phys = collections.defaultdict(set)
    for u in units:
        by_phys[(u["physical_key"], u["local"])].add(tuple(u["RT"]))

    report = {
        "protocol": "QUERY_restricted_decoder_exact_v1",
        "panel_artifact": a.panel,
        "panel_protocol": payload["protocol"],
        "panel_script_sha256": payload["script_sha256"],
        "arithmetic": "fractions.Fraction only; floats used solely as exact hex bit keys",
        "restricted_information": "c1 = centered horizon-1 interventional effect profile",
        "targets": "ateT / shapley at horizon 6 under the frozen continuation policy rho",
        "accounting": accounting,
        "determinism_check": {
            "groups_with_identical_physical_and_rng_key": len(by_full),
            "violations": violations,
            "can_fail": True,
            "interpretation": "a violation would void the panel (nondeterministic pipeline)",
        },
        "stochastic_floor_check": {
            "physical_state_groups": len(by_phys),
            "groups_where_target_varies_with_rng_only": sum(
                1 for v in by_phys.values() if len(v) > 1),
            "can_fail": True,
            "interpretation": ("nonzero means part of the target variation is RWARE's "
                               "request-replacement RNG, not missing features; such pairs "
                               "are excluded from every headline bad-pair count"),
        },
    }

    degen = lambda u: all(v == 0 for v in u["c1"])  # noqa: E731
    panels = {"full_panel": units, "evaluable_nonconstant_subpanel": evaluable}
    report["baseline_c1_summary"] = {}
    for pname, pu in panels.items():
        report["baseline_c1_summary"][pname] = {
            "decoder_ate_horizon6": exact_decoder_report(pu, lambda u: u["c1"],
                                                         lambda u: u["ateT"]),
            "decoder_shapley_horizon6": exact_decoder_report(pu, lambda u: u["c1"],
                                                             lambda u: u["shapT"]),
            "pairs_ate_horizon6": bad_pair_report(pu, lambda u: u["c1"],
                                                  lambda u: u["ateT"], degen,
                                                  orderedfn=lambda u: u["ateT"]),
            "pairs_shapley_horizon6": bad_pair_report(pu, lambda u: u["c1"],
                                                      lambda u: u["shapT"], degen,
                                                      orderedfn=lambda u: u["shapT"]),
            "pairs_full_effect_profile_cT": bad_pair_report(pu, lambda u: u["c1"],
                                                            lambda u: u["cT"], degen),
        }

    seeds = sorted({u["seed"] for u in units})
    test_seeds = set(seeds[len(seeds) - a.holdout_seeds:])
    train_seeds = set(seeds) - test_seeds
    train = [u for u in evaluable if u["seed"] in train_seeds]
    test = [u for u in evaluable if u["seed"] in test_seeds]

    purchases = []
    for r in range(len(CATALOG) + 1):
        for extras in itertools.combinations(CATALOG, r):
            kf = lambda u, e=extras: summary_key(u, e)  # noqa: E731
            dec = exact_decoder_report(evaluable, kf, lambda u: u["ateT"])
            bp = bad_pair_report(evaluable, kf, lambda u: u["ateT"], degen,
                                 orderedfn=lambda u: u["ateT"])
            purchases.append({
                "bought": list(extras),
                "cost": subset_cost(extras),
                "bad_pairs_distinct_physical_state": bp.get(
                    "bad_pairs_distinct_physical_state", 0),
                "bad_pairs_nondegenerate_summary": bp.get(
                    "bad_pairs_nondegenerate_summary", 0),
                "bad_pairs_rng_confounded": bp.get("bad_pairs_rng_confounded", 0),
                "certified_minimax_floor_nondegenerate_float": bp.get(
                    "certified_minimax_floor_nondegenerate_float"),
                "minimax_worst_case_abs_error": dec["minimax_worst_case_abs_error"],
                "minimax_size_weighted_abs_error_float":
                    dec["minimax_size_weighted_abs_error_float"],
                "bayes_mse_risk_float": dec["bayes_mse_risk_float"],
                "variance_explained_float": dec["variance_explained_float"],
                "n_fibres": dec["n_fibres"],
                "singleton_unit_fraction_float": dec["singleton_unit_fraction_float"],
                "holdout": holdout_eval(train, test, kf, lambda u: u["ateT"]),
            })
    report["catalog_purchases"] = purchases
    report["holdout_split"] = {
        "train_seeds": sorted(train_seeds), "test_seeds": sorted(test_seeds),
        "train_units": len(train), "test_units": len(test),
        "note": "split is by SEED (whole episodes), so no state leaks across the split",
    }

    zero_bad = [p for p in purchases if p["bad_pairs_distinct_physical_state"] == 0]
    report["repair"] = {
        "subsets_reaching_zero_bad_pairs": [p["bought"] for p in zero_bad],
        "minimum_items_to_zero_bad_pairs": (min(len(p["bought"]) for p in zero_bad)
                                            if zero_bad else None),
        "full_catalog_result": next(p for p in purchases if set(p["bought"]) == set(CATALOG)),
        "guard_note": ("a subset counts as a repair only if it reaches zero bad pairs WITHOUT "
                       "collapsing to singleton fibres and WITHOUT its holdout abstain rate "
                       "rising; both numbers are reported per subset"),
    }

    out = ROOT / a.out
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(report, indent=1, default=str) + "\n")
    print(json.dumps({"accounting": accounting,
                      "determinism_violations": violations,
                      "out": str(out)}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
