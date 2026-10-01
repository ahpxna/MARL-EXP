#!/usr/bin/env python3
"""Paper C, step C5: what the breakpoint conjecture still owes, and what is now paid.

The conjecture is

    eta*_m = 1 (m odd),   (m-2)/(2(m-1)) (m even),

and calling it exact requires TWO proofs:

    (O1)  V_m(eta*) = V_m^free,
    (O2)  eta < eta*  implies  V_m(eta) > V_m^free.

This script settles as much of each as can be settled without a general-m proof, and says
precisely what is left.

(O2) IS PARTLY PROVED, NOT MERELY SOLVED.  The odd-m lower bound proved in
`LeanUnifiedStructuralRelaxedV1`,

    V_m(eta) >= (m + 3 - (m+1) eta) / (m (m+4)),

already exceeds the free value `2/((m+4)(m-1))` exactly when

    eta < (m^2 - 3) / (m^2 - 1).

So (O2) holds on that whole range as a consequence of a Lean theorem, with no solver in the
loop.  What remains is the window `[(m^2-3)/(m^2-1), 1)`, which shrinks like `2/m^2` but is
never empty.  The script computes the window and confirms the implication.

(O1) IS CERTIFIED EXACTLY at each tested size, not by reading a floating-point optimum: a
rational flow is extracted at `eta = eta*`, and its feasibility and objective are verified in
exact `Fraction` arithmetic against the free value.  That turns "the LP said so" into "here
is a feasible plan achieving it".  It still is not a proof for general `m`.
"""

import json
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, "scripts")
from EXP_paperC_flow_lp import (WEIGHTS, baseline, caps, edges_of, prefix_sum,
                                solve_flow, states)

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def free_value(m):
    return Fr(2, (m + 4) * (m - 1))


def proved_bound(m, eta):
    """The Lean-proved odd-m lower bound, as an exact rational."""
    return (Fr(m + 3) - Fr(m + 1) * eta) / Fr(m * (m + 4))


def window_edge(m):
    """Where the proved bound stops beating the free value: (m^2-3)/(m^2-1)."""
    return Fr(m * m - 3, m * m - 1)


def exact_flow_certificate(m, eta):
    """Solve the flow LP, then round the flow to exact rationals and verify
    feasibility and objective without any floating point."""
    byk, c = states(m)
    b = baseline(m)
    E = edges_of(m)
    nE = len(E)
    D = m + 4
    root = (0, 0, 0, 0)

    out_of, in_to = {}, {}
    for i, (v, t, w) in enumerate(E):
        out_of.setdefault(v, []).append(i)
        in_to.setdefault(w, []).append(i)

    nv = nE + 1
    cost = np.zeros(nv); cost[-1] = 1.0
    A_eq, b_eq = [], []
    r = np.zeros(nv)
    for i in out_of.get(root, []):
        r[i] = 1.0
    A_eq.append(r); b_eq.append(1.0)
    for k in range(1, m):
        for v in byk[k]:
            r = np.zeros(nv)
            for i in in_to.get(v, []):
                r[i] += 1.0
            for i in out_of.get(v, []):
                r[i] -= 1.0
            A_eq.append(r); b_eq.append(0.0)

    def occ_row(v):
        r = np.zeros(nv)
        for i in in_to.get(v, []):
            r[i] += 1.0
        return r

    A_ub, b_ub = [], []
    for k in range(1, m):
        r = np.zeros(nv)
        for v in byk[k]:
            r += float(Fr(abs(prefix_sum(v)) - b[k], D)) * occ_row(v)
        r[-1] = -1.0
        A_ub.append(r); b_ub.append(0.0)
    for tau in range(4):
        N = c[tau]
        if N == 0:
            continue
        for k in range(1, m):
            r = np.zeros(nv)
            for v in byk[k]:
                r += (v[tau] / N) * occ_row(v)
            A_ub.append(r.copy()); b_ub.append(float(Fr(k, m) + eta / Fr(m)))
            A_ub.append(-r); b_ub.append(-float(Fr(k, m) - eta / Fr(m)))

    res = linprog(cost, A_ub=np.array(A_ub), b_ub=np.array(b_ub),
                  A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                  bounds=[(0, None)] * nE + [(None, None)], method="highs")
    if not res.success:
        return None
    x = res.x[:nE]

    # round the flow to rationals with a modest denominator, then verify exactly
    for den in (m, 2 * m, m * (m - 1), 2 * m * (m - 1), 4 * m * (m - 1),
                m * (m - 1) * (m - 2) if m > 2 else m):
        xf = [Fr(round(v * den), den) for v in x]
        if any(v < 0 for v in xf):
            continue
        # conservation
        ok = sum(xf[i] for i in out_of.get(root, [])) == 1
        if ok:
            for k in range(1, m):
                for v in byk[k]:
                    if (sum(xf[i] for i in in_to.get(v, []))
                            != sum(xf[i] for i in out_of.get(v, []))):
                        ok = False
                        break
                if not ok:
                    break
        if not ok:
            continue
        # occupancy and the two families of constraints
        def occ(v):
            return sum(xf[i] for i in in_to.get(v, []))

        val = Fr(0)
        for k in range(1, m):
            ek = sum(occ(v) * Fr(abs(prefix_sum(v)) - b[k], D) for v in byk[k])
            val = max(val, ek)
        band_ok = True
        for tau in range(4):
            N = c[tau]
            if N == 0:
                continue
            for k in range(1, m):
                marg = sum(occ(v) * Fr(v[tau], N) for v in byk[k])
                if not (Fr(k, m) - eta / Fr(m) <= marg <= Fr(k, m) + eta / Fr(m)):
                    band_ok = False
                    break
            if not band_ok:
                break
        if band_ok:
            return {"denominator": den, "value": val}
    return None


def main():
    print("=" * 78)
    print("Paper C / C5: the two obligations behind the breakpoint")
    print("=" * 78)

    odd = [5, 7, 9, 11, 13, 15]

    # ---------------- O2, on the range the Lean bound already covers
    print("\n  (O2) where the PROVED bound already forces V(eta) > V^free")
    print("  " + "-" * 70)
    o2_ok, rows = True, []
    for m in odd:
        w = window_edge(m)
        fv = free_value(m)
        # the implication, checked exactly just below the edge and just above
        below = proved_bound(m, w - Fr(1, 10000)) > fv
        at_edge = proved_bound(m, w) == fv
        rows.append({"m": m, "proved_up_to": str(w), "gap_to_1": str(1 - w)})
        if not (below and at_edge):
            o2_ok = False
        print(f"      m={m:3d}: proved for eta < {w} = {float(w):.6f}"
              f"   unproved window [{float(w):.6f}, 1),  width {float(1-w):.6f}")
    check("the proved bound beats the free value exactly below (m^2-3)/(m^2-1)", o2_ok)
    check("so (O2) holds on that range with no solver in the loop", o2_ok)
    check("and the remaining window shrinks like 2/m^2 but is never empty",
          all(Fr(1) - window_edge(m) > 0 for m in odd)
          and (1 - window_edge(odd[-1])) < (1 - window_edge(odd[0])),
          f"width {float(1-window_edge(odd[0])):.4f} at m=5 down to "
          f"{float(1-window_edge(odd[-1])):.4f} at m={odd[-1]}")

    # ---------------- O1, certified exactly
    print("\n  (O1) an exact rational flow at eta = eta*, achieving the free value")
    print("  " + "-" * 70)
    o1_ok, o1rows = True, []
    for m in [5, 6, 7, 8, 9, 10, 11]:
        eta = Fr(1) if m % 2 else Fr(m - 2, 2 * (m - 1))
        cert = exact_flow_certificate(m, eta)
        fv = free_value(m)
        if cert is None:
            o1_ok = False
            print(f"      m={m:3d}: NO exact certificate found")
            continue
        ok = cert["value"] == fv
        o1_ok = o1_ok and ok
        o1rows.append({"m": m, "eta_star": str(eta), "value": str(cert["value"]),
                       "free": str(fv), "denominator": cert["denominator"],
                       "match": ok})
        print(f"      m={m:3d}: eta*={eta}  exact flow value = {cert['value']}"
              f"   free = {fv}   {'match' if ok else 'MISMATCH'}")
    check("an exactly-rational band-feasible flow attains the free value at eta*",
          o1_ok, "so (O1) is certified at every tested size")

    # ---------------- the honest summary
    print("\n  what remains open")
    print("  " + "-" * 70)
    print("      (O1) certified at m = 5..11 by exhibited rational flows;")
    print("           NOT proved for general m.")
    print("      (O2) PROVED for eta < (m^2-3)/(m^2-1) from a Lean theorem;")
    print("           the window up to eta* = 1 is solved, not proved.")
    check("the breakpoint is therefore still a conjecture, and is labelled one",
          True, "partial closure recorded, not upgraded to a theorem")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperC_breakpoint_certs.py").read_bytes()).hexdigest(),"O2_window": rows, "O1_certificates": o1rows,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperC_breakpoint_certs.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
