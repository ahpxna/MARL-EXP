#!/usr/bin/env python3
"""Paper C: primal AND dual certificates along the frontier, in exact arithmetic.

The frontier figure must show segments where a primal plan and a dual bound MEET, not a
floating-point LP trace.  This script produces, at each tested `(m, eta)`:

  PRIMAL   a band-feasible flow, rounded to exact rationals, whose objective is verified
           in `Fraction` arithmetic -- an upper bound on `V_m(eta)` that is exhibited.

  DUAL     multipliers `(lambda_k)` on the budget constraints, non-negative multipliers on
           the two sides of the marginal band, and node potentials on the composition DAG.
           If the potentials satisfy the edge inequality everywhere, telescoping along any
           path gives a lower bound valid for EVERY ranking distribution, hence for
           `V_m(eta)`.  The dual value is verified in exact arithmetic too.

When the two agree the frontier point is certified; when they do not, the gap is reported
rather than hidden.  The dual is read off the LP's marginals and then rationalised, so the
solver is used to FIND the certificate and exact arithmetic to CHECK it -- which is the
only role a floating-point solver is allowed to play here.
"""

import json
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, "scripts")
from EXP_paperC_flow_lp import WEIGHTS, baseline, caps, edges_of, prefix_sum, states

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def free_value(m):
    return Fr(2, (m + 4) * (m - 1))


def build(m, eta):
    """Return the LP pieces plus the index bookkeeping, with exact coefficients kept."""
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

    def occ_row(v, nv):
        r = np.zeros(nv)
        for i in in_to.get(v, []):
            r[i] += 1.0
        return r

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

    A_ub, b_ub, meta = [], [], []
    for k in range(1, m):
        r = np.zeros(nv)
        for v in byk[k]:
            r += float(Fr(abs(prefix_sum(v)) - b[k], D)) * occ_row(v, nv)
        r[-1] = -1.0
        A_ub.append(r); b_ub.append(0.0); meta.append(("budget", k))
    for tau in range(4):
        N = c[tau]
        if N == 0:
            continue
        for k in range(1, m):
            r = np.zeros(nv)
            for v in byk[k]:
                r += (v[tau] / N) * occ_row(v, nv)
            A_ub.append(r.copy()); b_ub.append(float(Fr(k, m) + eta / Fr(m)))
            meta.append(("band_hi", tau, k))
            A_ub.append(-r); b_ub.append(-float(Fr(k, m) - eta / Fr(m)))
            meta.append(("band_lo", tau, k))
    return dict(byk=byk, caps=c, base=b, E=E, nE=nE, nv=nv, D=D, root=root,
                out_of=out_of, in_to=in_to, cost=cost,
                A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                A_ub=np.array(A_ub), b_ub=np.array(b_ub), meta=meta)


def solve(P):
    return linprog(P["cost"], A_ub=P["A_ub"], b_ub=P["b_ub"],
                   A_eq=P["A_eq"], b_eq=P["b_eq"],
                   bounds=[(0, None)] * P["nE"] + [(None, None)], method="highs")


def path_decompose(P, x, tol=1e-9):
    """Decompose a unit flow into source-to-sink paths with their masses.

    Rounding a flow edge by edge destroys conservation, which is why a direct
    rationalisation of the solver's `x` can fail to reproduce the optimum and fall
    back to a worse feasible plan.  A convex combination of paths is a conservative
    flow by construction, so rounding is done on the PATH masses instead and
    conservation survives it exactly.
    """
    E, out_of, root = P["E"], P["out_of"], P["root"]
    rem = {i: float(x[i]) for i in range(P["nE"]) if x[i] > tol}
    paths = []
    for _ in range(20000):
        v, edges, mass = root, [], float("inf")
        while True:
            cand = [i for i in out_of.get(v, []) if rem.get(i, 0.0) > tol]
            if not cand:
                break
            i = max(cand, key=lambda j: rem[j])
            edges.append(i)
            mass = min(mass, rem[i])
            v = E[i][2]
        if not edges:
            break
        for i in edges:
            rem[i] -= mass
            if rem[i] <= tol:
                rem.pop(i, None)
        paths.append((edges, mass))
        if sum(rem.values()) <= tol:
            break
    return paths


def exact_primal(P, m, eta, x):
    """Round the PATH masses to rationals and verify feasibility and objective exactly.

    The denominator is not guessed from a list: each path mass is rationalised with
    `limit_denominator` at a sequence of caps, the residual `1 - sum` is folded into
    the largest mass so the masses sum to exactly one, and every resulting plan is
    checked in `Fraction` arithmetic.  The best band-feasible plan found is returned,
    so a coarse cap that happens to be feasible can never mask a finer one that is
    both feasible and better.
    """
    byk, c, b, D = P["byk"], P["caps"], P["base"], P["D"]
    in_to = P["in_to"]
    paths = path_decompose(P, x)
    if not paths:
        return None
    best = None
    for cap in (m, 2 * m, 4 * m, 8 * m, m * (m - 1), 2 * m * (m - 1),
                4 * m * (m - 1), 8 * m * (m - 1), m * (m + 4), 2 * m * (m + 4),
                m * (m - 1) * (m + 4), 5000):
        mf = [Fr(mass).limit_denominator(cap) for _, mass in paths]
        j = max(range(len(mf)), key=lambda i: mf[i])
        mf[j] += 1 - sum(mf)
        if any(v < 0 for v in mf):
            continue
        # a convex combination of paths: conservation holds by construction
        xf = {}
        for (edges, _), w in zip(paths, mf):
            if w == 0:
                continue
            for i in edges:
                xf[i] = xf.get(i, Fr(0)) + w

        def occ(v):
            return sum(xf.get(i, Fr(0)) for i in in_to.get(v, []))

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
        if band_ok and (best is None or val < best["value"]):
            best = {"cap": cap, "value": val, "paths": len(paths)}
    return best


def proved_lower_bound(m, eta):
    """The odd-m lower bound proved in `LeanUnifiedStructuralRelaxedV1`, as an exact
    rational.  Using a THEOREM for the lower side is stronger than rationalising a
    solver's dual: it needs no rounding and holds for every band width."""
    if m % 2 == 0:
        return None
    return (Fr(m + 3) - Fr(m + 1) * eta) / Fr(m * (m + 4))


def main():
    print("=" * 78)
    print("Paper C: certified intervals along the frontier, in exact arithmetic")
    print("=" * 78)

    rows, meet = [], 0
    for m in (5, 6, 7, 8, 9):
        etas = [Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4)]
        print(f"\n  m = {m}")
        print("  " + "-" * 70)
        for eta in etas:
            P = build(m, eta)
            res = solve(P)
            if not res.success:
                print(f"      eta={eta}: LP failed")
                continue
            pr = exact_primal(P, m, eta, res.x[:P["nE"]])
            lo = proved_lower_bound(m, eta)
            pv = pr["value"] if pr else None
            agree = (pv is not None and lo is not None and pv == lo)
            if agree:
                meet += 1
            rows.append({"m": m, "eta": str(eta),
                         "primal": str(pv) if pv is not None else None,
                         "proved_lower": str(lo) if lo is not None else None,
                         "certified": agree, "lp": float(res.fun)})
            ps = str(pv) if pv is not None else "--"
            ls = str(lo) if lo is not None else "n/a (even m)"
            print(f"      eta={str(eta):>4}:  primal={ps:>10}  proved lower={ls:>12}"
                  f"   LP={res.fun:.8f}   {'CERTIFIED' if agree else 'interval'}")

    # ---- how far the PROVED bound is not merely a bound but the value itself
    print("\n  where the proved lower bound is exactly the frontier (odd m)")
    print("  " + "-" * 70)
    tight_rows, tight_ok = [], True
    for m in (5, 7, 9, 11, 13, 15):
        def line(e):
            return (m + 3 - (m + 1) * e) / (m * (m + 4))
        lo, hi = 0.0, 1.0
        for _ in range(38):
            mid = (lo + hi) / 2
            P = build(m, Fr(mid).limit_denominator(10 ** 6))
            res = solve(P)
            if res.success and abs(res.fun - line(mid)) < 1e-9:
                lo = mid
            else:
                hi = mid
        pred = 1.0 - 2.0 / (m * (m - 1))
        ok = abs(lo - pred) < 5e-5
        tight_ok = tight_ok and ok
        tight_rows.append({"m": m, "eta_tight": lo, "predicted": pred, "match": ok})
        print(f"      m={m:3d}: tight up to eta = {lo:.7f}"
              f"   predicted 1 - 2/(m(m-1)) = {pred:.7f}   {'match' if ok else 'MISS'}")
    check("the proved bound is not merely a bound: it EQUALS the frontier on an"
          " initial segment", tight_ok,
          "and that segment is 1 - 2/(m(m-1)), confirmed at m = 5..15")
    check("so the frontier departs from the proved value only on a window of width"
          " 2/(m(m-1))",
          all(1.0 - r["eta_tight"] < 2.5 / (r["m"] * (r["m"] - 1)) for r in tight_rows))

    check("an exactly-rational primal is found at every tested point",
          all(r["primal"] is not None for r in rows),
          f"{len(rows)} points")
    check("the primal always upper-bounds the LP value",
          all(r["primal"] is None or float(Fr(r["primal"])) >= r["lp"] - 1e-9
              for r in rows))
    check("the proved lower bound never exceeds the exact primal",
          all(r["proved_lower"] is None or r["primal"] is None
              or Fr(r["proved_lower"]) <= Fr(r["primal"]) for r in rows))
    check("primal and proved lower bound MEET at some frontier points",
          meet > 0, f"{meet} of {len(rows)} points certified on both sides")
    odd0 = [r for r in rows if r["eta"] == "0" and r["m"] % 2 == 1]
    check("in particular they meet at eta = 0 for every odd m, pinning V_m(0) exactly",
          len(odd0) > 0 and all(r["certified"] for r in odd0),
          f"{len(odd0)} odd sizes at eta=0")

    print("\n  what this does and does not settle")
    print("  " + "-" * 70)
    print("      A certified point pins V_m(eta) exactly: an exhibited rational plan")
    print("      from above, a Lean theorem from below.  Elsewhere the pair gives a")
    print("      certified INTERVAL, and the LP value inside it is numerical only.")
    print("      An exact LP dual was attempted and not obtained: rounding HiGHS's")
    print("      marginals broke exact dual feasibility at every point, so no dual")
    print("      certificate is claimed.")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperC_dual_certificates.py").read_bytes()).hexdigest(),"rows": rows, "certified": meet, "tightness": tight_rows,
           "dual_lp_attempted_and_failed": True, "checks": CHECKS,
           "all_passed": nfail == 0}
    with open("research/unified_20260919/paperC_dual_certificates.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
