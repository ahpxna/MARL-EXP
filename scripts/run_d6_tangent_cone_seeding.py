#!/usr/bin/env python3
"""Seed the exact LP ascent by SOLVING for the departure direction at a tie point.

Addendum C Section 108 recorded the failure that motivates this file: the exact
LP ascent climbs well but is local, and neither random starts nor random
perturbations of a tie point reach the extremal basin -- even standing on the
CORRECT tie point, random directions gave 0.79 against 1.19993 for the correct
one. The obstruction is the direction, and directions cannot be sampled: the
good ones are measure zero.

They do not have to be sampled. At a tie point F0 write F(t) = F0 + t d. As
t -> 0+ every delta_square and every loss l_T is continuous, but the Top-C
SELECTION is not: coordinates tied in oscillation are separated by the
first-order term eps_i c_i(d), where c_i = F(e_i) - F(0) and eps_i = sign c_i(F0).
Hence

    lim_{t->0+} 2D / ((m-1) delta_square)
        = 2 ( l_{S(d)}(F0) - min_T l_T(F0) ) / ( (m-1) delta_square(F0) )

and the right-hand side depends on d ONLY through the selection S(d). The limit
therefore takes finitely many values, one per achievable top-k set, and the best
one is found by enumeration over the tied group -- no search, no LP.

A direction realising a chosen S is then written down explicitly: put
d(e_i) = +eps_i for i in S cap G, -eps_i for i in G \ S, and 0 everywhere else
(G = the tied group). This moves only m of the 2^m values, so the seed keeps
small denominators.

Usage:
  python3 scripts/run_d6_tangent_cone_seeding.py --m 6 --tie-world ART.json
  python3 scripts/run_d6_tangent_cone_seeding.py --m 6 --starts 4      # find ties
"""
from __future__ import annotations
import argparse, itertools, json, random, sys, time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
from research_chains.provenance import write_artifact_with_provenance  # noqa: E402
from run_d6_binary_exact_lp_ascent import (  # noqa: E402
    build, evaluate_exact, ascend, normalize)

PROTOCOL_VERSION = "d6_tangent_cone_seeding_v1"
EVIDENCE_CLASS = "EXACT_RATIONAL_COUNTEREXAMPLE_INDEPENDENTLY_RECOMPUTED"


def losses_and_delta(P, x):
    m = P["m"]
    losses = {T: (max(P["G"][T] @ x) - min(P["G"][T] @ x)) / 2 for T in P["subsets"]}
    delta = max((max(P["rho"][i] @ x) - min(P["rho"][i] @ x)) for i in range(m))
    return losses, delta


def achievable_selections(P, x):
    """Every top-k set reachable by breaking the oscillation ties at x."""
    m, k = P["m"], P["k"]
    c = [P["comp"][i] @ x for i in range(m)]
    osc = [v if v >= 0 else -v for v in c]
    levels = sorted(set(osc), reverse=True)
    out, forced, budget = [], [], k
    for v in levels:
        grp = [i for i in range(m) if osc[i] == v]
        if len(grp) <= budget:
            forced += grp; budget -= len(grp)
            if budget == 0:
                break
        else:
            for pick in itertools.combinations(grp, budget):
                out.append((tuple(sorted(forced + list(pick))), tuple(grp), v))
            budget = 0
            break
    if not out:
        out = [(tuple(sorted(forced)), (), None)]
    return out, osc, c


def limit_ratios(P, x):
    """Exact limiting ratio for every achievable selection at the tie point x."""
    m = P["m"]
    losses, delta = losses_and_delta(P, x)
    lo = min(losses.values())
    sels, osc, c = achievable_selections(P, x)
    rows = []
    for S, grp, level in sels:
        r = None if delta == 0 else 2 * (losses[S] - lo) / ((m - 1) * delta)
        rows.append({"selected": list(S), "tied_group": list(grp),
                     "limit_ratio": None if r is None else str(r),
                     "limit_ratio_float": None if r is None else float(r),
                     "loss_selected": str(losses[S])})
    rows.sort(key=lambda d: (d["limit_ratio_float"] is not None,
                             d["limit_ratio_float"] or 0), reverse=True)
    return rows, osc, c, losses, delta


def direction_for(P, x, S, grp, c):
    """Explicit d realising the selection S: touch only the m corner values."""
    d = [F(0)] * P["N"]
    for i in grp:
        eps = F(1) if c[i] >= 0 else F(-1)
        d[1 << i] = eps if i in S else -eps
    return np.asarray(d, dtype=object)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--tie-world", type=str, default=None,
                    help="artifact with a 'world' or 'integer_world' to use as tie point")
    ap.add_argument("--starts", type=int, default=4,
                    help="random starts driven to tie points when --tie-world is absent")
    ap.add_argument("--rounds", type=int, default=30)
    ap.add_argument("--margin", type=str, default="1/1000")
    ap.add_argument("--t", type=str, default="1/64", help="step off the tie point")
    ap.add_argument("--seed", type=int, default=5)
    ap.add_argument("--top-selections", type=int, default=3,
                    help="run the exact ascent only on this many best selections; the "
                         "limit-ratio spectrum itself is enumerated for all of them and is "
                         "the scientific content, the ascent only refines the best")
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args(argv)

    t0 = time.time()
    P = build(args.m); N = P["N"]; margin = F(args.margin); step = F(args.t)
    rng = random.Random(args.seed)

    ties = []
    if args.tie_world:
        d = json.load(open(args.tie_world))
        if "integer_world" in d:
            vec = [F(int(v)) for v in d["integer_world"]]
        else:
            # Accept every shape the ledger instruments emit.  run_d6_tie_locus_lp
            # writes the tie point under "tie_world"; the ascent writes "world";
            # sweep artifacts nest it under strict_top_c_witness.world.
            entries = (d.get("tie_world") or d.get("world")
                       or (d.get("seed_off_tie") or {}).get("world")
                       or (d.get("strict_top_c_witness") or {}).get("world"))
            if entries is None:
                raise SystemExit(
                    "tie-world artifact has none of: integer_world, tie_world, world, "
                    f"seed_off_tie.world, strict_top_c_witness.world (keys: {sorted(d)})")
            w = {tuple(e["action"]): F(e["value"]) for e in entries}
            vec = [w[tuple((a >> i) & 1 for i in range(args.m))] for a in range(N)]
        # round to the integer tie point the ascent converges to
        y = normalize(P, vec)
        ties.append(("artifact", np.asarray([F(round(float(v))) for v in y], dtype=object)))
    else:
        for s in range(args.starts):
            x0 = [F(rng.randint(-40, 40), rng.randint(1, 9)) for _ in range(N)]
            tie, tev, _ = ascend(P, x0, margin=F(0), rounds=args.rounds)
            if tie is None:
                continue
            ties.append((f"random_{s}", np.asarray([F(round(float(v))) for v in tie],
                                                   dtype=object)))

    records, best = [], None
    for name, tie in ties:
        ev0 = evaluate_exact(P, tie)
        rows, osc, c, losses, delta = limit_ratios(P, tie)
        rec = {"tie_point": name,
               "ratio_at_tie": None if ev0["ratio"] is None else float(ev0["ratio"]),
               "oscillations": [str(v) for v in osc],
               "delta_square": str(delta),
               "achievable_selections": rows}
        ascended = 0
        for row in rows:
            if row["limit_ratio_float"] is None:
                continue
            if ascended >= args.top_selections:
                row["seed_status"] = "NOT_ASCENDED_RANK_BELOW_CUTOFF"
                continue
            S = tuple(row["selected"]); grp = tuple(row["tied_group"])
            if not grp:
                continue
            d = direction_for(P, tie, S, grp, c)
            seed = normalize(P, [tie[a] + step * d[a] for a in range(N)])
            if seed is None:
                continue
            evs = evaluate_exact(P, seed)
            row["seed_ratio_float"] = float(evs["ratio"]) if evs["ratio"] is not None else None
            row["seed_strict_top_c"] = bool(evs["strict_top_c"])
            row["seed_margin_relative"] = (None if evs["margin_relative"] is None
                                           else float(evs["margin_relative"]))
            if not evs["strict_top_c"] or evs["margin_relative"] < margin:
                row["seed_status"] = "FAILS_GATE"; continue
            xb, eb, hist = ascend(P, seed, margin=margin, rounds=args.rounds)
            if eb is None:
                row["seed_status"] = "ASCENT_DEGENERATE"; continue
            row["ascent_ratio"] = str(eb["ratio"])
            row["ascent_ratio_float"] = float(eb["ratio"])
            row["ascent_strict_violation"] = bool(eb["ratio"] > 1)
            row["ascent_max_denominator"] = max(v.denominator for v in xb)
            row["seed_status"] = "OK"
            ascended += 1
            if best is None or eb["ratio"] > best[0]:
                best = (eb["ratio"], xb, eb, name, S)
        records.append(rec)

    result = {
        "protocol_version": PROTOCOL_VERSION, "development_only": True,
        "evidence_class": EVIDENCE_CLASS, "m": args.m, "alphabet": 2,
        "reference": "corner (all-zero)",
        "hypothesis": "none -- raw rank one is vacuous at K=2",
        "method": "tangent-cone seeding: the limiting ratio off a tie point depends on the "
                  "direction only through the induced Top-C selection, so the achievable "
                  "selections are enumerated exactly and the best one is realised by an "
                  "explicit direction touching only the m corner values",
        "step_off_tie": str(step), "strict_top_c_margin": str(margin),
        "tie_points": records,
        "conjecture_under_test": "the bound fails iff m is even, with sharp constant "
                                 "2k/(m-1), k = floor(m/2)",
        "derived_prediction": str(F(2 * (args.m // 2), args.m - 1)),
        "derived_prediction_float": float(F(2 * (args.m // 2), args.m - 1)),
        "predicts_violation": bool(F(2 * (args.m // 2), args.m - 1) > 1),
        "m_over_m_minus_1": str(F(args.m, args.m - 1)),
        "m_over_m_minus_1_float": float(F(args.m, args.m - 1)),
    }
    if best is not None:
        ratio, xb, eb, name, S = best
        result.update({
            "status": "KILLED" if ratio > 1 else "NO_VIOLATION_FOUND",
            "best_exact_ratio": str(ratio), "best_exact_ratio_float": float(ratio),
            "best_strict_violation": bool(ratio > 1),
            "best_from_tie_point": name, "best_selected": list(S),
            "best_max_denominator": max(v.denominator for v in xb),
            "best_top_c_margin_relative_float": float(eb["margin_relative"]),
            "best_delta_square": str(eb["delta"]),
            "best_doubled_decision_gap": str(eb["twoD"]),
            "fraction_of_conjectured_sup": float(ratio) / float(F(args.m, args.m - 1)),
            "world": [{"action": [(a >> i) & 1 for i in range(args.m)], "value": str(xb[a])}
                      for a in range(P["N"])]})
    else:
        result["status"] = "NO_ADMISSIBLE_SEED"
    result["wall_clock_seconds"] = round(time.time() - t0, 3)

    out = Path(args.out) if args.out else (
        ROOT / "research/d6_contrast_rank_falsification"
        / f"TangentSeed_m{args.m}_K2_s{args.seed}.json")
    if out.exists():
        raise SystemExit(f"refusing to overwrite existing ledger artifact: {out}")
    write_artifact_with_provenance(
        out, result,
        protocol={"protocol_version": PROTOCOL_VERSION, "m": args.m, "step": str(step),
                  "margin": str(margin)},
        seed=args.seed, evidence_class=EVIDENCE_CLASS, chain="D6")
    print(json.dumps({k: result[k] for k in
                      ("m", "status", "best_exact_ratio", "best_exact_ratio_float",
                       "best_strict_violation", "derived_prediction",
                       "derived_prediction_float", "predicts_violation",
                       "fraction_of_conjectured_sup", "best_max_denominator",
                       "wall_clock_seconds") if k in result} | {"out": str(out)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
