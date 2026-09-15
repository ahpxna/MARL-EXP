#!/usr/bin/env python3
"""D07 probe 1: is c = a - b = (1-t)^(2q) an EXACT algebraic identity?

Definitions taken verbatim from the Lean corpus:
  LeanD6ReferenceResponseJoinV1.lean
    tailFactor t B = (1-t)^|B| + |B| * t * (1-t)^(|B|-1)
    gateMass   t A j = (1-t)^|A| * tailFactor t (others A j)
  LeanD6ReferenceCenteredCompensatedV1.lean
    slopeBval  t A j = (|others A j| - 1) * t * (1-t)^(|A| + |others A j| - 1)

In the reference instance |A| = k = q+1, |others A j| = q, q >= 2.
NOTE the Lean exponents use NATURAL subtraction; with q >= 2 and
|A|+|B|-1 = 2q >= 4 no truncation occurs, so Fraction arithmetic is faithful.

Two independent checks:
  (A) sympy symbolic simplification in (q, t) with q symbolic,
  (B) exact Fraction arithmetic on a (q, t) grid, with q a literal integer,
      evaluating the Lean formulas term by term (no algebraic shortcut).
"""
import json
import sys
from fractions import Fraction as F

OUT = "/Users/phanan/cig-amf-main/research/high_risk_20260910/D07_exact_identity_20260912.json"


def tail_factor(t, nB):
    # (1-t)^nB + nB * t * (1-t)^(nB-1)      [nB >= 1 so no Nat-truncation]
    return (1 - t) ** nB + F(nB) * t * (1 - t) ** (nB - 1)


def gate_mass(t, nA, nB):
    return (1 - t) ** nA * tail_factor(t, nB)


def slope_bval(t, nA, nB):
    # (nB - 1) * t * (1-t)^(nA + nB - 1)
    return F(nB - 1) * t * (1 - t) ** (nA + nB - 1)


def main():
    res = {"probe": "D07_exact_slope_identity", "checks": []}

    # ---------- (A) symbolic ----------
    sym_ok = None
    sym_note = ""
    try:
        import sympy as sp
        t = sp.Symbol("t")
        q = sp.Symbol("q", integer=True, positive=True)
        nA = q + 1
        nB = q
        tf = (1 - t) ** nB + nB * t * (1 - t) ** (nB - 1)
        a = (1 - t) ** nA * tf
        b = (nB - 1) * t * (1 - t) ** (nA + nB - 1)
        diff = sp.simplify(sp.powsimp(sp.expand(a - b - (1 - t) ** (2 * q)), force=True))
        sym_ok = bool(diff == 0)
        sym_note = "sympy simplify(a - b - (1-t)^(2q)) == %s" % sp.srepr(diff)[:120]
        # also the task's closed forms
        a_task = (1 - t) ** (2 * q + 1) + q * t * (1 - t) ** (2 * q)
        b_task = (q - 1) * t * (1 - t) ** (2 * q)
        da = sp.simplify(sp.powsimp(sp.expand(a - a_task), force=True))
        db = sp.simplify(sp.expand(b - b_task))
        sym_ok = sym_ok and bool(da == 0) and bool(db == 0)
        sym_note += " ; a-a_task=%s ; b-b_task=%s" % (da, db)
    except Exception as exc:  # sympy absent or failed
        sym_note = "sympy unavailable/failed: %r" % (exc,)
    res["symbolic"] = {"sympy_identity_holds": sym_ok, "note": sym_note}

    # ---------- (B) exact Fraction grid ----------
    qs = list(range(2, 41)) + [50, 64, 80, 100, 128, 200, 256, 400, 500, 1000]
    ts = [F(0), F(1), F(1, 2), F(1, 3), F(2, 3), F(1, 4), F(3, 4), F(1, 8), F(7, 8),
          F(1, 25), F(1, 17), F(1, 10), F(1, 100), F(1, 1000), F(37818, 1000000),
          F(99, 100), F(1, 7), F(5, 13), F(11, 23)]
    fails = []
    n = 0
    for qq in qs:
        nA, nB = qq + 1, qq
        for tt in ts:
            a = gate_mass(tt, nA, nB)
            b = slope_bval(tt, nA, nB)
            c_pred = (1 - tt) ** (2 * qq)
            n += 1
            if a - b != c_pred:
                fails.append({"q": qq, "t": str(tt), "a_minus_b": str(a - b),
                              "pred": str(c_pred)})
            # task closed forms
            a_task = (1 - tt) ** (2 * qq + 1) + F(qq) * tt * (1 - tt) ** (2 * qq)
            b_task = F(qq - 1) * tt * (1 - tt) ** (2 * qq)
            if a != a_task or b != b_task:
                fails.append({"q": qq, "t": str(tt), "closed_form_mismatch": True})
    res["fraction_grid"] = {"cells": n, "failures": len(fails), "examples": fails[:5],
                            "q_values": [qs[0], qs[-1]], "n_q": len(qs), "n_t": len(ts)}

    # ---------- (C) the Lean theorem already on record ----------
    res["lean_status"] = {
        "theorem": "CIGAMF.P13.D6ReferenceFullCountLoss.slope_gap",
        "statement": "gateMass t A j - slopeBval t A j = (1-t)^(A.card + (others A j).card - 1)",
        "hypothesis": "2 <= (others A j).card  (i.e. q >= 2)",
        "module": "LeanD6ReferenceFullCountLossV1",
        "receipt": "LeanD6ReferenceFullCountLossV1.compile.receipt.json (lean_exit 0)",
        "axioms": "[propext, Classical.choice, Quot.sound]",
        "note": "with |A|=q+1, |others|=q the exponent is 2q, so c=(1-t)^(2q) is PROVED in Lean.",
    }
    res["verdict"] = ("CONFIRMED" if (len(fails) == 0 and sym_ok is not False) else "REFUTED")
    with open(OUT, "w") as fh:
        json.dump(res, fh, indent=2)
    print(json.dumps(res, indent=2))
    return 0 if res["verdict"] == "CONFIRMED" else 1


if __name__ == "__main__":
    sys.exit(main())
