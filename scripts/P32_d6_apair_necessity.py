#!/usr/bin/env python3
"""P32 -- harness contract E-D: is the A-pair REQUIRED, or merely present?

`P7` showed the A-pair `(2,0,0)` appears in the optimal support above a threshold in t.
Being in a support is not the same as being necessary: a class can sit at a positive
weight and still be replaceable at no cost.  The contract asks for an oracle that
EXCLUDES the A-pair and certifies the difference.

The certificate is directional, and the direction matters:

  L_full   -- the exact value of ONE full design, so a LOWER bound on Gamma_full;
  U_noA    -- a dual certificate valid for EVERY design whose support omits the
              A-pair, with charges at their certified LOWER end (which can only raise
              the bound);

and `L_full > U_noA` therefore proves `Gamma_full > Gamma_{no A-pair}` strictly: no
design without the A-pair can match the full one.  That is necessity, not presence.

`U_full` is reported alongside for the primal/dual bracket of the full game.  A cell
where `L_full <= U_noA` is reported UNDECIDED, never as "the A-pair is unnecessary":
`L_full` is only a lower bound.
"""
from __future__ import annotations
import argparse, json, os, sys, time
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from P7_d6_full_design import (all_classes, dual_upper, enclose_zstar,
                               enclose_charge, charge2, coarsen)
from P18_d6_full_vs_two import solve_tracked, lam_from

REPO = Path(__file__).resolve().parents[1]
APAIR = ("query", 2, 0, 0)


def costs_for(q, mu, t):
    g = 1 - mu
    h = t / q
    zs_lo, zs_hi = enclose_zstar(g, mu)
    zlo, zhi = coarsen(zs_lo - h, False), coarsen(zs_hi - h, True)
    cl, ch = charge2(g, mu, h)
    classes = all_classes(q)
    hi, lo = [], []
    for lab, r in classes:
        if r == 1:
            hi.append(F(1)); lo.append(F(1))
        elif r == 2:
            hi.append(ch); lo.append(cl)
        else:
            a, bb = enclose_charge(r, zlo, zhi, 12)
            hi.append(bb); lo.append(a)
    return classes, hi, lo


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    out = Path(args.out or (REPO / "research/worker_P32_d6_apair_20260915"
                            / "P32_d6_apair_necessity.json"))
    if out.exists():
        raise SystemExit(f"Refusing to overwrite {out}")
    t0 = time.time()
    cells = []
    for mu in (F(1, 4), F(2, 5)):
        for q in (8, 16):
            for t in (F(1), F(3, 2), F(2), F(5, 2), F(3)):
                classes, hi, lo = costs_for(q, mu, t)
                full = solve_tracked(q, mu, hi, classes)
                if full is None:
                    print(f"   mu={mu} q={q} t={t}: full LP failed; skipped")
                    continue
                U_full, _ = dual_upper(q, mu, lam_from(full), classes, lo)
                # --- the restricted family: every class EXCEPT the A-pair
                keep = [i for i, (lab, _r) in enumerate(classes) if lab != APAIR]
                clsN = [classes[i] for i in keep]
                noA = solve_tracked(q, mu, [hi[i] for i in keep], clsN)
                if noA is None:
                    print(f"   mu={mu} q={q} t={t}: restricted LP failed; skipped")
                    continue
                U_noA, argN = dual_upper(q, mu, lam_from(noA), clsN,
                                         [lo[i] for i in keep])
                strict = full["L"] > U_noA
                apair_w = next((w for (lab, _r), w in zip(classes, full["w"])
                                if lab == APAIR), F(0))
                cells.append({
                    "mu": str(mu), "q": q, "t": str(t),
                    "L_full": str(full["L"]), "U_full": str(U_full),
                    "L_noApair": str(noA["L"]), "U_noApair": str(U_noA),
                    "apair_weight_in_full_support": str(apair_w),
                    "apair_present": bool(apair_w > 0),
                    "apair_NECESSARY_L_full_gt_U_noA": bool(strict),
                    "necessity_ratio": float(full["L"] / U_noA),
                    "full_bracket_relative_gap": float((U_full - full["L"]) / full["L"]),
                    "converged_full": full["converged"],
                    "converged_noA": noA["converged"],
                    "dual_argmax_noA": list(map(str, argN)),
                })
                verdict = ("NECESSARY" if strict
                           else ("UNDECIDED" if apair_w > 0 else "absent"))
                print(f"   mu={mu} q={q:3d} t={t}: L_full={float(full['L']):.6e}  "
                      f"U_noA={float(U_noA):.6e}  ratio={float(full['L']/U_noA):.6f}  "
                      f"w_Apair={float(apair_w):.4f}  {verdict}", flush=True)

    nnec = sum(1 for c in cells if c["apair_NECESSARY_L_full_gt_U_noA"])
    npres = sum(1 for c in cells if c["apair_present"])
    out_obj = {
        "script": "P32_d6_apair_necessity.py", "contract": "E-D",
        "question": "is the A-pair (2,0,0) REQUIRED, or merely present in a support?",
        "certificate": "L_full (the exact value of one full design, a LOWER bound on "
                       "Gamma_full) versus U_noA (a dual bound valid for EVERY design "
                       "omitting the A-pair, charges at their certified LOWER end).  "
                       "L_full > U_noA proves Gamma_full > Gamma_{no A-pair} strictly.",
        "cells_apair_present": npres, "cells_apair_necessary": nnec,
        "cells_total": len(cells), "cells": cells,
        "wall_seconds": round(time.time() - t0, 1),
        "not_established": [
            "A cell with L_full <= U_noA is UNDECIDED, never 'the A-pair is "
            "unnecessary': L_full is only a lower bound on Gamma_full.",
            "Presence in a numerically-found support is not necessity; only the "
            "directional certificate above is.",
            "The alternative family is (d, x) and the symmetry orbits, as elsewhere in "
            "the D6 chain.",
            "No phase boundary is certified here.",
        ],
        "lean": "LeanD6ScalarInformationV1.dual_over_all_queries is the certificate "
                "SHAPE; the numbers here are not a Lean theorem",
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("x") as f:
        json.dump(out_obj, f, indent=1)
        f.write("\n")
    print(f"\nA-pair present in {npres}/{len(cells)} cells, "
          f"certified NECESSARY in {nnec}/{len(cells)}")
    print(f"artifact: {out}")


if __name__ == "__main__":
    main()
