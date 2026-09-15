#!/usr/bin/env python3
"""D6: the blind phase boundary in closed form, tested against the LP sweep.

The assignment proposes reducing the blind game to two curves -- the ordinary
scalar and the width-q off-query -- and locating the boundary where the scalar
class first enters the optimal blind design. With m = 2q+1,

    K_q = q(q^2+1) / (2(2q+1)),   B_q = (q+1) / (2(2q+1)),   c_q = B_q/K_q,

the joint-only branch is optimal until, writing z = mu/(1-mu),

    z^2 + c_q z + (q/2) c_q^2  =  ((q+1)/2) (1 - c_q/2).            (*)

That is a QUADRATIC, so the boundary is a closed-form root instead of a
bisection. This probe solves (*) exactly in rationals-plus-one-square-root and
then asks the blind LP whether the support really changes there: it runs the
design just below and just above the predicted mu*, at several distances.

The LP is the same one as `D1_blind_allocation_threshold.py` (same cutting-plane
loop, same alternative set), so this is a prediction being checked against an
independent computation, not a curve fitted to it.

    .venv/bin/python scripts/D3_blind_phase_boundary.py
"""
from fractions import Fraction as F
import importlib.util, json, math
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "d1", REPO / "scripts" / "D1_blind_allocation_threshold.py")
d1 = importlib.util.module_from_spec(spec); spec.loader.exec_module(d1)


def boundary(q):
    """The root of (*) in (0,1), and the constants it is built from."""
    K = F(q * (q * q + 1), 2 * (2 * q + 1))
    B = F(q + 1, 2 * (2 * q + 1))
    c = B / K                                   # = (q+1)/(q(q^2+1))
    # z^2 + c z + (q/2)c^2 - ((q+1)/2)(1 - c/2) = 0
    const = F(q, 2) * c * c - F(q + 1, 2) * (1 - c / 2)
    disc = c * c - 4 * const                    # exact rational
    if disc < 0:
        return None
    z = (-float(c) + math.sqrt(float(disc))) / 2
    if z <= 0:
        return None
    return {"K_q": K, "B_q": B, "c_q": c, "discriminant": disc,
            "z_star": z, "mu_star": z / (1 + z)}


def main():
    g = d1.load_game()
    rows = []
    for q in (3, 4, 5):
        bd = boundary(q)
        if bd is None:
            print(f"q={q}: no root in range"); continue
        mu_star = bd["mu_star"]
        print(f"\nq={q}:  c_q = {bd['c_q']}  ->  predicted boundary "
              f"mu* = {mu_star:.6f}")
        obs = []
        for delta in (0.05, 0.02, 0.005):
            for side, mu in (("below", mu_star - delta), ("above", mu_star + delta)):
                if not (0 < mu < 1):
                    continue
                try:
                    gam, _, _, _, _ = d1.solve_value(g, q, mu, 0.0, False)
                    vb, _, _, classes, mvec = d1.solve_value(g, q, mu, 0.0, True)
                except Exception as e:
                    print(f"   mu={mu:.6f} ({side}): LP failed {type(e).__name__}")
                    continue
                sup = sorted(str(c) for c, v in zip(classes, mvec) if v > 1e-9)
                scalar_in = any("'s'" in s for s in sup)
                obs.append({"delta": delta, "side": side, "mu": mu,
                            "zeta_blind": 1 - vb / gam,
                            "support": sup, "scalar_present": scalar_in})
                print(f"   mu={mu:.6f} ({side:5s}): zeta={1-vb/gam:.6f}  "
                      f"scalar in support = {scalar_in}   {'  '.join(sup)}")
        # the prediction: scalar absent below, present above
        below = [o for o in obs if o["side"] == "below"]
        above = [o for o in obs if o["side"] == "above"]
        ok = (all(not o["scalar_present"] for o in below)
              and all(o["scalar_present"] for o in above) and below and above)
        print(f"   PREDICTION {'CONFIRMED' if ok else 'NOT confirmed'}: "
              f"scalar absent below mu*, present above")
        rows.append({"q": q, "c_q": str(bd["c_q"]), "K_q": str(bd["K_q"]),
                     "B_q": str(bd["B_q"]), "mu_star": mu_star,
                     "prediction_confirmed": bool(ok), "observations": obs})
    out = REPO / "research/worker_D_blind_20260914/D3_blind_phase_boundary.json"
    out.write_text(json.dumps({
        "claim": "the blind design is joint-only until z = mu/(1-mu) solves "
                 "z^2 + c_q z + (q/2)c_q^2 = ((q+1)/2)(1 - c_q/2), c_q = (q+1)/(q(q^2+1))",
        "method": "closed-form root, then the SAME blind LP as D1 asked whether the "
                  "support changes across it; the LP never sees the prediction",
        "rows": rows,
        "scope": "q in {3,4,5}, eps=0, shell=0. The two-curve reduction itself "
                 "(that ordinary scalar and width-q off-query dominate every other "
                 "class after group averaging) is NOT proved here -- it is the "
                 "hypothesis this boundary is derived from, and the agreement below "
                 "is evidence for it, not a proof.",
    }, indent=2, default=str) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
