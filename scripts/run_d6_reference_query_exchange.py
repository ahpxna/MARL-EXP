#!/usr/bin/env python3
"""D6: price a reference change in the SAME unit as a query.

Two ways to buy information about the hidden set, priced against each other:

  QUERY     reveal h = |A cap T| to the decision maker before it acts.
            Its value is the duality gap  V - V_h,  where
              V   = minimax value (simultaneous move)      = the floor
              V_h = max_h min_d Rbar(h,d) (decision moves second)
            The reduction of min_d to d in {0,k} is LICENSED by the machine-
            checked `dominance_gen` / `dominance_one` of
            LeanD6ReferencePhaseValueV1, not assumed.

  REFERENCE move t -> t*, spending budget  d_tau = k*(t* - t).

The exchange rate is the d_tau at which the reference purchase buys exactly
what the query buys:  V(t*) = V_h(t).  Reported as a CERTIFIED BRACKET
[t_lo, t_hi] with V(t_lo) > V_h >= V(t_hi), both endpoints exact rationals.
Nothing here is a fitted root.

Also reported is the derivation's own quantity, the A-vs-B slope gap
c(t) = (1-t)^(2k-2), at both ends of the purchase.
"""
import argparse, hashlib, json, math, os, sys
from fractions import Fraction as F

PROTOCOL_VERSION = "d6_reference_query_exchange_v1"
BISECTION_STEPS = 100

def pos(x): return x if x > 0 else F(0)

def pieces(k, t, rho):
    c = (1 - t) ** (2 * k - 2)
    a, b = c * (1 + (k - 2) * t), c * (k - 2) * t
    return a, b, a - b, rho - 2 * b, 2 * a - rho, min(a, 2 * b)

def in_regime(k, t, rho):
    return (k - 2) * pieces(k, t, rho)[1] >= 1

def Rbar(h, d, k, p, cg, a, b, e, r):
    lin = (p * d - 2 * cg * F(h * d, k) + max(e, r * h)) / 2
    ec = e if d == 0 else (b * F(k - h, k) if d == 1 else F(0))
    return lin - ec / 2

def V(k, t, rho):
    a, b, cg, p, r, e = pieces(k, t, rho)
    return pos(k * r - e) * (p * (k - 1) + pos(e - r)) / (4 * cg * (k - 1))

def V_query(k, t, rho):
    a, b, cg, p, r, e = pieces(k, t, rho)
    return max(min(Rbar(h, 0, k, p, cg, a, b, e, r), Rbar(h, k, k, p, cg, a, b, e, r))
               for h in range(1, k + 1))

def tau_crit(rho):
    lo, hi = 0.0, 10.0
    for _ in range(300):
        m = (lo + hi) / 2
        if 2 * (1 + m) * math.exp(-2 * m) > rho: lo = m
        else: hi = m
    return (lo + hi) / 2

def price_cell(k, t, rho, t_max):
    a, b, cg, p, r, e = pieces(k, t, rho)
    cell = {"k": k, "t": str(t), "rho": str(rho), "budget_tau": float(k * t),
            "tau_crit": tau_crit(float(rho)), "slope_gap_c": float((1 - t) ** (2 * k - 2))}
    if not in_regime(k, t, rho):
        cell["status"] = "OUT_OF_REGIME"; return cell
    v, vh = V(k, t, rho), V_query(k, t, rho)
    cell.update({"V_floor": str(v), "V_floor_f": float(v),
                 "V_after_query": str(vh), "V_after_query_f": float(vh),
                 "query_value_duality_gap": float(v - vh)})
    if vh > v:
        cell["status"] = "FAILED_maxmin_exceeds_minimax"; return cell
    if v == 0:
        cell["status"] = "FLOOR_ALREADY_DEAD"; return cell
    if v == vh:
        cell["status"] = "QUERY_WORTHLESS"; return cell
    if V(k, t_max, rho) > vh:
        cell["status"] = "NO_REFERENCE_PURCHASE_IN_RANGE"; return cell
    lo, hi = t, t_max
    for _ in range(BISECTION_STEPS):
        m = (lo + hi) / 2
        if V(k, m, rho) <= vh: hi = m
        else: lo = m
    assert V(k, lo, rho) > vh >= V(k, hi, rho), "bracket invariant broken"
    cell.update({"status": "PRICED",
                 "t_star_bracket": [str(lo), str(hi)],
                 "t_star_f": float(hi),
                 "V_at_t_lo": float(V(k, lo, rho)), "V_at_t_hi": float(V(k, hi, rho)),
                 "delta_tau_one_query": float(k * (hi - t)),
                 "slope_gap_c_at_t_star": float((1 - hi) ** (2 * k - 2)),
                 "slope_gap_change": float((1 - hi) ** (2 * k - 2) - (1 - t) ** (2 * k - 2)),
                 "budget_headroom_to_boundary": tau_crit(float(rho)) - float(k * t)})
    return cell

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--ks", default="10,12,16,24,32")
    ap.add_argument("--ts", default="1/64,1/56,1/48,1/40,1/32,1/24")
    ap.add_argument("--rhos", default="1,9/8,5/4,3/2")
    ap.add_argument("--t-max", default="1/4")
    a = ap.parse_args()
    if os.path.exists(a.out) and not a.overwrite:
        sys.exit(f"refusing to overwrite {a.out} (append-only ledger); pass --overwrite or pick a new path")
    ks = [int(x) for x in a.ks.split(",")]
    ts = [F(x) for x in a.ts.split(",")]
    rhos = [F(x) for x in a.rhos.split(",")]
    tmax = F(a.t_max)
    cells = [price_cell(k, t, rho, tmax) for k in ks for t in ts for rho in rhos]
    priced = [c for c in cells if c["status"] == "PRICED"]
    failed = [c for c in cells if c["status"].startswith("FAILED")]
    by_status = {}
    for c in cells: by_status[c["status"]] = by_status.get(c["status"], 0) + 1

    out = {"protocol_version": PROTOCOL_VERSION,
           "claim": "a reference change and a query are priced in one unit: the reference budget "
                    "d_tau = k*(t*-t) whose floor reduction equals the query's duality gap V - V_h",
           "arithmetic": "exact Fraction; t* reported as a certified bracket, not a fitted root",
           "licensed_by": "min over d reduced to d in {0,k} by dominance_gen / dominance_one "
                          "(LeanD6ReferencePhaseValueV1, machine-checked)",
           "not_proved_here": "the three reference slopes are numerically exact only; "
                              "see LeanD6BernoulliReferenceBridgeV1 / LeanD6BernoulliTailV1",
           "bisection_steps": BISECTION_STEPS,
           "grid": {"ks": ks, "ts": [str(x) for x in ts], "rhos": [str(x) for x in rhos],
                    "t_max": str(tmax)},
           "counts": {"cells": len(cells), "priced": len(priced), "failed": len(failed),
                      "by_status": by_status},
           "cells": cells}
    with open(a.out, "w") as f: json.dump(out, f, indent=1, sort_keys=True)
    h = hashlib.sha256(open(a.out, "rb").read()).hexdigest()
    with open(a.out + ".manifest.json", "w") as f:
        json.dump({"protocol_version": PROTOCOL_VERSION, "artifact": os.path.basename(a.out),
                   "sha256": h, "bytes": os.path.getsize(a.out), "counts": out["counts"]}, f, indent=1)
    print(f"cells {len(cells)}  PRICED {len(priced)}  FAILED {len(failed)}")
    print("  " + "  ".join(f"{k}={v}" for k, v in sorted(by_status.items())))
    if priced:
        print(f"\n{'k':>3} {'t':>6} {'rho':>5} {'tau':>7} {'headroom':>9} {'V':>9} {'V_h':>9} "
              f"{'query gap':>10} {'d_tau/query':>12} {'c(t)':>8} {'c(t*)':>8}")
        for c in priced:
            print(f"{c['k']:>3} {c['t']:>6} {c['rho']:>5} {c['budget_tau']:>7.4f} "
                  f"{c['budget_headroom_to_boundary']:>9.4f} {c['V_floor_f']:>9.5f} "
                  f"{c['V_after_query_f']:>9.5f} {c['query_value_duality_gap']:>10.5f} "
                  f"{c['delta_tau_one_query']:>12.6f} {c['slope_gap_c']:>8.5f} "
                  f"{c['slope_gap_c_at_t_star']:>8.5f}")
    print(f"\nsha256 {h}")
    if failed: sys.exit(1)

if __name__ == "__main__":
    main()
