#!/usr/bin/env python3
"""MASTER: regret floor of evidence A (the response Q) and the price of
evidence B (the reference scale t) that destroys it.

Every number is exact rational arithmetic. Nothing here is a fit, a solve, or a
numerical LP: each cell carries a primal/dual certificate checked by equality.

Evidence class emitted per cell:
  CERTIFIED_EXACT   all five certificates hold as rational identities
  OUT_OF_REGIME     the sufficient condition (k-2)*b >= 1 fails; the finite
                    formula is NOT asserted there and the cell is not counted
"""
import argparse, hashlib, json, math, os, sys
from fractions import Fraction as F

PROTOCOL_VERSION = "master_reference_phase_certificates_v1"

def pos(x): return x if x > 0 else F(0)

def slopes(k, t):
    """a, b, c from the gate's Bernoulli product sums (2k coords, |A|=k, |B|=k-1).
    Checked exactly against the Lean `gate` definition for k=3,4,5."""
    c = (1 - t) ** (2 * k - 2)
    return c * (1 + (k - 2) * t), c * (k - 2) * t, c

def pieces(k, t, rho):
    a, b, c = slopes(k, t)
    return a, b, a - b, rho - 2 * b, 2 * a - rho, min(a, 2 * b)

def Rbar(h, d, k, p, cg, a, b, e, r):
    lin = (p * d - 2 * cg * F(h * d, k) + max(e, r * h)) / 2
    ec = e if d == 0 else (b * F(k - h, k) if d == 1 else F(0))
    return lin - ec / 2

def V_formula(k, p, cg, e, r):
    return pos(k * r - e) * (p * (k - 1) + pos(e - r)) / (4 * cg * (k - 1))

def certify(k, t, rho):
    a, b, cg, p, r, e = pieces(k, t, rho)
    cell = {"k": k, "t": str(t), "rho": str(rho),
            "a": str(a), "b": str(b), "c_gap": str(cg),
            "p": str(p), "r": str(r), "e": str(e),
            "sufficient_condition_(k-2)b>=1": bool((k - 2) * b >= 1)}
    if (k - 2) * b < 1:
        cell["evidence_class"] = "OUT_OF_REGIME"
        return cell
    fails = {}
    # L1 two-action dominance: no pure d beats the {0,k} mixture
    bad = [(h, d) for h in range(1, k + 1) for d in range(0, k + 1)
           if Rbar(h, d, k, p, cg, a, b, e, r)
           < (1 - F(d, k)) * Rbar(h, 0, k, p, cg, a, b, e, r)
           + F(d, k) * Rbar(h, k, k, p, cg, a, b, e, r)]
    if bad: fails["L1_two_action_dominance"] = bad[:4]
    V = V_formula(k, p, cg, e, r)
    cell["V"] = str(V); cell["V_over_k"] = float(V) / k
    cell["active_(kr>e)"] = bool(k * r > e)
    if k * r <= e:
        if V != 0: fails["inactive_value_not_zero"] = str(V)
        bad0 = [h for h in range(1, k + 1) if Rbar(h, 0, k, p, cg, a, b, e, r) != 0]
        if bad0: fails["inactive_d0_not_zero"] = bad0[:4]
        cell["floor_alive"] = False
    else:
        cell["floor_alive"] = True
        u0, v, U = pos(r - e) / 2, (p * (k - 1) + pos(e - r)) / 2, (k * r - e) / 2
        for nm, (hh, dd, val) in {"h1d0": (1, 0, u0), "h1dk": (1, k, v),
                                  "hkd0": (k, 0, U), "hkdk": (k, k, F(0))}.items():
            if Rbar(hh, dd, k, p, cg, a, b, e, r) != val:
                fails.setdefault("matrix_entry", []).append(nm)
        den = U - u0 + v
        if den != cg * (k - 1): fails["denominator"] = [str(den), str(cg * (k - 1))]
        q, s = v / den, (v - u0) / den
        if not (0 <= q <= 1 and 0 <= s <= 1): fails["weights"] = [str(q), str(s)]
        for nm, val in {"primal_h1": q * u0 + (1 - q) * v, "primal_hk": q * U,
                        "dual_d0": (1 - s) * u0 + s * U, "dual_dk": (1 - s) * v}.items():
            if val != V: fails.setdefault("equalizer", []).append(nm)
        # L2 endpoint-in-h: primal mixture never exceeds V at any interior h
        bad2 = [h for h in range(1, k + 1)
                if q * Rbar(h, 0, k, p, cg, a, b, e, r)
                + (1 - q) * Rbar(h, k, k, p, cg, a, b, e, r) > V]
        if bad2: fails["L2_endpoint_in_h"] = bad2[:4]
        # L3 dual is a genuine lower bound against EVERY pure decision, not just 0 and k
        bad3 = [d for d in range(0, k + 1)
                if (1 - s) * Rbar(1, d, k, p, cg, a, b, e, r)
                + s * Rbar(k, d, k, p, cg, a, b, e, r) < V]
        if bad3: fails["L3_dual_lower_bound"] = bad3[:4]
        cell["primal_weight_d0"] = str(q); cell["dual_weight_hk"] = str(s)
    cell["evidence_class"] = "CERTIFIED_EXACT" if not fails else "FAILED"
    if fails: cell["failures"] = fails
    return cell

def V_limit(tau, rho):
    E = math.exp(-2 * tau); ai, bi = (1 + tau) * E, tau * E
    return max(0.0, (rho - 2 * bi)) * max(0.0, (2 * ai - rho)) / (4 * E) \
        if (rho - 2 * bi) > 0 and (2 * ai - rho) > 0 else 0.0

def tau_crit(rho):
    lo, hi = 0.0, 10.0
    for _ in range(300):
        m = (lo + hi) / 2
        if 2 * (1 + m) * math.exp(-2 * m) > rho: lo = m
        else: hi = m
    return (lo + hi) / 2

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--overwrite", action="store_true")
    ap.add_argument("--ks", default="6,8,10,12,16,24,32,64")
    ap.add_argument("--ts", default="1/64,1/32,1/16,1/12,1/10,1/8,3/20,1/5,1/4")
    ap.add_argument("--rhos", default="1,9/8,5/4,3/2,7/4,15/8,2")
    a = ap.parse_args()
    if os.path.exists(a.out) and not a.overwrite:
        sys.exit(f"refusing to overwrite {a.out} (append-only ledger); pass --overwrite or pick a new path")

    ks = [int(x) for x in a.ks.split(",")]
    ts = [F(x) for x in a.ts.split(",")]
    rhos = [F(x) for x in a.rhos.split(",")]
    cells = [certify(k, t, rho) for k in ks for t in ts for rho in rhos]
    cert = [c for c in cells if c["evidence_class"] == "CERTIFIED_EXACT"]
    failed = [c for c in cells if c["evidence_class"] == "FAILED"]

    # MASTER framing: for each (k, rho), the cheapest reference scale in the grid
    # that kills the floor. This is the price of evidence B.
    price = []
    for k in ks:
        for rho in rhos:
            alive = [t for t in ts if (lambda c: c["evidence_class"] == "CERTIFIED_EXACT"
                                       and c.get("floor_alive"))(certify(k, t, rho))]
            dead = [t for t in ts if (lambda c: c["evidence_class"] == "CERTIFIED_EXACT"
                                      and c.get("floor_alive") is False)(certify(k, t, rho))]
            price.append({"k": k, "rho": str(rho),
                          "t_with_floor_alive": [str(x) for x in alive],
                          "cheapest_t_that_kills_floor": str(min(dead)) if dead else None,
                          "in_regime_cells": len(alive) + len(dead)})

    # asymptotic law under t = tau/k
    asym = []
    for tau in [F(1, 8), F(1, 4), F(1, 2), F(1)]:
        for rho in [F(1), F(3, 2)]:
            row = {"tau": str(tau), "rho": str(rho), "limit": V_limit(float(tau), float(rho)), "k": {}}
            for k in [64, 256, 1024, 4096, 16384]:
                t = tau / k
                _a, _b, cg, p, r, e = pieces(k, t, rho)
                row["k"][str(k)] = {"V_over_k": float(V_formula(k, p, cg, e, r)) / k,
                                    "in_regime": bool((k - 2) * _b >= 1)}
            row["abs_error_at_k16384"] = abs(row["k"]["16384"]["V_over_k"] - row["limit"])
            asym.append(row)

    boundary = [{"rho": str(rh), "tau_crit": tau_crit(float(rh)),
                 "residual_2(1+t)exp(-2t)-rho": 2 * (1 + tau_crit(float(rh)))
                 * math.exp(-2 * tau_crit(float(rh))) - float(rh)}
                for rh in [F(1), F(5, 4), F(3, 2), F(15, 8), F(2)]]

    out = {"protocol_version": PROTOCOL_VERSION,
           "claim": "evidence A = the response Q; its regret floor is V_k(t,rho). "
                    "evidence B = the reference scale t; buying enough of it drives the floor to zero.",
           "arithmetic": "exact Fraction; no floating-point in any certificate",
           "slopes_source": "Bernoulli product sums over the gate of LeanD6ThresholdConstructionV1, "
                            "checked exactly at k=3,4,5 and t in {0,1/8,1/4,1/3,1/2}",
           "lean_status": {
               "algebraic_game": "LeanD6ReferencePhaseValueV1 (two-action dominance, endpoint, 2x2 value with correction)",
               "reference_bridge": "LeanD6BernoulliReferenceBridgeV1 + LeanD6BernoulliTailV1",
               "three_slopes": "NOT machine-proved; numerically exact only"},
           "grid": {"ks": ks, "ts": [str(x) for x in ts], "rhos": [str(x) for x in rhos]},
           "counts": {"cells": len(cells), "certified_exact": len(cert),
                      "out_of_regime": len(cells) - len(cert) - len(failed),
                      "failed": len(failed),
                      "floor_alive": sum(1 for c in cert if c.get("floor_alive")),
                      "floor_dead": sum(1 for c in cert if c.get("floor_alive") is False)},
           "price_of_evidence_B": price,
           "asymptotic_law": asym,
           "phase_boundary_2(1+tau)exp(-2tau)=rho": boundary,
           "cells": cells}
    with open(a.out, "w") as f: json.dump(out, f, indent=1, sort_keys=True)
    h = hashlib.sha256(open(a.out, "rb").read()).hexdigest()
    with open(a.out + ".manifest.json", "w") as f:
        json.dump({"protocol_version": PROTOCOL_VERSION, "artifact": os.path.basename(a.out),
                   "sha256": h, "bytes": os.path.getsize(a.out),
                   "counts": out["counts"]}, f, indent=1)
    c = out["counts"]
    print(f"cells {c['cells']}  certified_exact {c['certified_exact']}  out_of_regime {c['out_of_regime']}  FAILED {c['failed']}")
    print(f"floor alive {c['floor_alive']}   floor dead {c['floor_dead']}")
    for rr in boundary: print(f"  rho={rr['rho']:>5}  tau_crit={rr['tau_crit']:.8f}  residual={rr['residual_2(1+t)exp(-2t)-rho']:+.2e}")
    for rw in asym: print(f"  tau={rw['tau']:>5} rho={rw['rho']:>5}  V/k(k=16384)={rw['k']['16384']['V_over_k']:.8f}  limit={rw['limit']:.8f}  err={rw['abs_error_at_k16384']:.2e}")
    print(f"sha256 {h}")
    if c["failed"]: sys.exit(1)

if __name__ == "__main__":
    main()
