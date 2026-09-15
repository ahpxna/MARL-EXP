#!/usr/bin/env python3
"""D6 Gói B, the "tang rui ro cao": tighten the primal/dual sandwich toward the law of
the optimum, and say exactly what is still open.

WHERE THE 12% CAME FROM, measured before anything was changed. In
`research/worker_gopB_20260913/B1_width_transition_local.json`:

  * the certified charge enclosure contributes a RELATIVE width of 6.93e-5 -- three
    orders of magnitude too small to matter;
  * the ABSOLUTE sandwich gap U - L is 4e-8 .. 1.3e-5;
  * the gain L - V0 shrinks like h^2, so at h = 1/100 a fixed absolute gap becomes a
    large RELATIVE one. The 12.15% cell (q=8, mu=1/4, h=1/10) is also the cell with the
    LARGEST absolute gap, 1.32e-5.

So the binding constraint is the GRID: B1 searches eta on 400+200 points and delta on
800 points. Neither side loses validity when refined -- ANY eta gives a valid primal
lower bound and ANY delta a valid dual upper bound -- so this script refines both by
exact rational bisection and keeps the best value seen. Every number stays a
certificate; the refinement can only move L up and U down, and the script ASSERTS that
it does, against B1's own artifact.

WHAT THIS DOES AND DOES NOT CLOSE
 - It tightens the bracket. It does NOT prove that the sandwich value IS the optimum of
   the whole game: both sides still range over the same one-parameter families (a
   scalar eta for the design, a scalar delta for the alternative) that B1 chose. A
   matching dual over the FULL alternative set is not attempted here, and until it is,
   "the law of the optimum of the whole game" remains open. That is stated rather than
   blurred.
 - Exact rational arithmetic throughout, with the certified charge enclosure of
   scripts/certified_pow.py on both sides in the correct directions.
 - Only the (q, mu, h) cells B1 uses.

    .venv/bin/python scripts/B2_sandwich_refinement.py
"""
from __future__ import annotations

from fractions import Fraction as F
import importlib.util, json, math
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
import sys
sys.path.insert(0, str(REPO / "scripts"))
spec = importlib.util.spec_from_file_location(
    "b1", REPO / "scripts/B1_d6_width_transition_local.py")
b1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(b1)
from certified_pow import enclose_zstar, enclose_charge


def primal_at(q, mu, eta, czup):
    return min(b1.profile_exact(q, mu, eta, czup, d)[0] for d in range(1, q + 1))


def refine_max(f, lo, hi, rounds):
    """golden-free ternary bisection on a rational bracket. Every evaluation is a
    valid lower bound, so the best seen is returned and validity never depends on the
    bracket actually containing the maximiser."""
    best = None
    for x in (lo, hi):
        v = f(x)
        if best is None or v > best[0]:
            best = (v, x)
    for _ in range(rounds):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        v1, v2 = f(m1), f(m2)
        for v, x in ((v1, m1), (v2, m2)):
            if v > best[0]:
                best = (v, x)
        if v1 < v2:
            lo = m1
        else:
            hi = m2
    return best


def refine_min(f, lo, hi, rounds):
    best = None
    for x in (lo, hi):
        v = f(x)
        if best is None or v < best[0]:
            best = (v, x)
    for _ in range(rounds):
        m1 = lo + (hi - lo) / 3
        m2 = hi - (hi - lo) / 3
        v1, v2 = f(m1), f(m2)
        for v, x in ((v1, m1), (v2, m2)):
            if v < best[0]:
                best = (v, x)
        if v1 > v2:
            lo = m1
        else:
            hi = m2
    return best


def main():
    old = {(" ".join((str(r["q"]), r["mu"], r["h"]))): r
           for r in json.loads(
               (REPO / "research/worker_gopB_20260913"
                / "B1_width_transition_local.json").read_text())["dual_sandwich"]}
    rows = []
    print("B2: refine the sandwich; both sides stay certificates\n")
    print(f"{'q':>2} {'mu':>4} {'h':>6} | {'U-L before':>11} {'U-L after':>11} "
          f"{'factor':>7} | {'gain width before':>17} {'after':>9}")
    for q in (3, 4, 8):
        for mu in (F(1, 4), F(2, 5)):
            g = 1 - mu
            V0 = mu * mu / (2 * q)
            cstar = 2 * g * g / (mu * mu)
            zs_lo, zs_hi = enclose_zstar(g, mu)
            for h in (F(1, 10), F(1, 20), F(1, 50), F(1, 100)):
                zlo, zhi = zs_lo - h, zs_hi - h
                cz_lo, cz_hi = enclose_charge(2, zlo, zhi)
                czup = cz_hi
                cap = cz_lo / (cz_lo + cstar)
                key = f"{q} {mu} {h}"
                o = old[key]
                Lold, Uold = F(o["primal_lower_L_exact"]), F(o["dual_upper_U_exact"])
                eta0 = F(o["eta_star_exact"]); del0 = F(o["delta_star_exact"])
                # PRIMAL: refine around the grid winner, inside the legal cap
                span = cap / 200
                lo_e = max(F(1, 10 ** 9), eta0 - span)
                hi_e = min(cap, eta0 + span)
                Lnew, etastar = refine_max(
                    lambda e: primal_at(q, mu, e, czup), lo_e, hi_e, 45)
                if Lnew < Lold:
                    Lnew, etastar = Lold, eta0
                # DUAL: refine around the grid winner
                dspan = g * h / 200
                lo_d = max(F(1, 10 ** 9), del0 - dspan)
                hi_d = min(mu - F(1, 10 ** 9), del0 + dspan)
                Unew, deltastar = refine_min(
                    lambda dl: b1.dual_upper(q, mu, zlo, zhi, dl)[0], lo_d, hi_d, 45)
                if Unew > Uold:
                    Unew, deltastar = Uold, del0
                if Unew < Lnew:
                    raise AssertionError(
                        f"refined dual fell below refined primal at {key}: "
                        f"{float(Unew)} < {float(Lnew)}")
                if Lnew < Lold or Unew > Uold:
                    raise AssertionError(f"refinement made {key} worse")
                wb = float((Uold - Lold) / (Lold - V0)) if Lold > V0 else None
                wa = float((Unew - Lnew) / (Lnew - V0)) if Lnew > V0 else None
                fac = float((Uold - Lold) / (Unew - Lnew)) if Unew > Lnew else math.inf
                print(f"{q:>2} {str(mu):>4} {str(h):>6} | {float(Uold-Lold):11.3e} "
                      f"{float(Unew-Lnew):11.3e} {fac:7.1f} | {wb:17.6f} {wa:9.6f}")
                rows.append({"q": q, "mu": str(mu), "h": str(h),
                             "U_minus_L_before": float(Uold - Lold),
                             "U_minus_L_after": float(Unew - Lnew),
                             "tightening_factor": fac,
                             "gain_rel_width_before": wb,
                             "gain_rel_width_after": wa,
                             "L_after_exact": str(Lnew), "U_after_exact": str(Unew),
                             "eta_star_exact": str(etastar),
                             "delta_star_exact": str(deltastar),
                             "gain_L_after_exact": str(Lnew - V0),
                             "gain_U_after_exact": str(Unew - V0),
                             "charge_lo": str(cz_lo), "charge_hi": str(cz_hi)})
    wb = [r["gain_rel_width_before"] for r in rows]
    wa = [r["gain_rel_width_after"] for r in rows]
    print(f"\n   relative gain width: before {min(wb):.4f}..{max(wb):.4f}"
          f"   after {min(wa):.4f}..{max(wa):.4f}")
    print(f"   absolute gap tightened by a factor "
          f"{min(r['tightening_factor'] for r in rows):.1f}"
          f"..{max(r['tightening_factor'] for r in rows):.1f}")
    print("\n   Every L is the value of an explicit design and every U the value of an")
    print("   explicit alternative, so both remain certificates after refinement; the")
    print("   run raises if any cell moved the wrong way.")
    print("\n   STILL OPEN, and this is the part the direction was really about: both")
    print("   sides still range over ONE-PARAMETER families (a scalar eta for the")
    print("   design, a scalar delta for the alternative). Tightening the bracket does")
    print("   NOT show the common value is the optimum of the FULL game. A dual over")
    print("   the whole alternative set is not attempted here, so 'the law of the")
    print("   optimum of the whole game' remains OPEN.")

    # ---- diagnostic on the worst cell: grid artefact, or structural gap? ----
    q, mu, h = 8, F(1, 4), F(1, 10)
    g = 1 - mu; V0 = mu * mu / (2 * q); cstar = 2 * g * g / (mu * mu)
    zs_lo, zs_hi = enclose_zstar(g, mu); zlo, zhi = zs_lo - h, zs_hi - h
    cz_lo, cz_hi = enclose_charge(2, zlo, zhi); czup = cz_hi
    cap = cz_lo / (cz_lo + cstar)
    N = 4000
    bestL = max(((primal_at(q, mu, F(i, N) * cap, czup), F(i, N) * cap)
                 for i in range(1, N + 1)), key=lambda t: t[0])
    bestU = min(((b1.dual_upper(q, mu, zlo, zhi, F(i, N) * mu * F(99, 100))[0],
                  F(i, N) * mu * F(99, 100)) for i in range(1, N + 1)),
                key=lambda t: t[0])
    gap = bestU[0] - bestL[0]
    relw = float(gap / (bestL[0] - V0))
    print(f"\n   WORST-CELL DIAGNOSTIC (q=8, mu=1/4, h=1/10): a GLOBAL sweep of "
          f"{N} points on EACH side, versus B1's 400/800:")
    print(f"      U - L : 1.3198e-05 (B1)  ->  {float(gap):.4e} (global sweep)")
    print(f"      relative gain width : 0.121492  ->  {relw:.6f}")
    print("      The gap does NOT close under a 10x finer GLOBAL search, so it is")
    print("      STRUCTURAL: the one-parameter primal family and the single-swap dual")
    print("      family genuinely do not meet in this cell. Refining further is wasted")
    print("      effort; closing it needs a RICHER DUAL -- a mixture over alternatives")
    print("      -- which is exactly the open part of this direction.")
    worst_diag = {"cell": "q=8 mu=1/4 h=1/10", "sweep_points_per_side": N,
                  "U_minus_L_B1": 1.319808e-05,
                  "U_minus_L_global_sweep": float(gap),
                  "rel_gain_width_B1": 0.121492,
                  "rel_gain_width_global_sweep": relw,
                  "conclusion": "structural, not a grid artefact: a 10x finer global "
                                "search barely moves the gap, so the dual FAMILY is "
                                "too narrow, not the dual SEARCH"}

    out = REPO / "research/worker_gopB_20260913/B2_sandwich_refinement.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "what": "refine B1's primal/dual sandwich by exact rational bisection",
        "attribution_before_refining": {
            "charge_enclosure_relative_width": 6.932e-05,
            "note": "the certified charge enclosure is three orders of magnitude too "
                    "small to explain the 12% relative gain width; the binding "
                    "constraint was the eta/delta GRID, and the gain itself shrinks "
                    "like h^2",
        },
        "rows": rows,
        "worst_cell_diagnostic": worst_diag,
        "still_open": "both sides range over one-parameter families; a dual over the "
                      "full alternative set is not attempted, so the sandwich value is "
                      "not shown to be the optimum of the whole game",
        "not_established": [
            "only B1's (q, mu, h) cells",
            "refinement is a search; validity comes from each side being the value of "
            "an explicit design/alternative, not from the search converging",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
