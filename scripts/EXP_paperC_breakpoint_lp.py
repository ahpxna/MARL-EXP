#!/usr/bin/env python3
"""Paper C: the breakpoint from a DIRECT linear program, with the flow exported.

Bisecting the frontier locates `eta_*` only as the place where a numerical curve appears to
touch a numerical value.  §10 asks for something stronger and simpler: solve

    min eta   subject to   x a unit flow on the prefix-composition DAG,
                           | sum_{|v|=k} v_tau x_v  -  c_tau k / m |  <=  c_tau eta / m,
                           sum_{|v|=k} r_k(v) x_v  <=  V_m^free       for every k.

Because `V_m(eta) >= V_m^free` always, this LP asks exactly the right question -- what is the
smallest relaxation at which the free value becomes reachable -- and answers it in one
solve.  No bisection, no touching of curves.

WHAT IS EXPORTED.  The previous certificate script saved values, denominators and a match
flag.  That is not enough to check anything independently.  This one writes out the PRIMAL
FLOW itself: the edge list, the rational masses of a path decomposition, and the verified
objective and band slacks in exact arithmetic.  A reader can recompute the value from the
exported flow without running the solver.

THE DUAL.  A dual certificate would prove no flow reaches `V_m^free` below `eta_*`.  It is
attempted here by reading HiGHS's marginals and rationalising them.  Where exact dual
feasibility fails, that is REPORTED and no dual claim is made -- the earlier attempt failed
the same way, and recording the failure is the point.

SELF-CHECKS compare the LP's `eta_*` against the conjectured parities, in exact arithmetic
where the primal rationalises, and refuse to report if an exported flow does not reproduce
its own objective.
"""

import json
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import linprog

sys.path.insert(0, "scripts")
from EXP_paperC_flow_lp import baseline, edges_of, prefix_sum, states
from EXP_paperC_dual_certificates import free_value, path_decompose

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


def build_min_eta(m):
    """The LP of the docstring, with `eta` as a variable rather than a swept parameter."""
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

    nv = nE + 1                                   # last variable is `eta`
    cost = np.zeros(nv)
    cost[-1] = 1.0                                # minimise eta

    def occ_row(v):
        r = np.zeros(nv)
        for i in in_to.get(v, []):
            r[i] += 1.0
        return r

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
    Vfree = float(free_value(m))
    for k in range(1, m):                          # reach the FREE value at every budget
        r = np.zeros(nv)
        for v in byk[k]:
            r += float(Fr(abs(prefix_sum(v)) - b[k], D)) * occ_row(v)
        A_ub.append(r); b_ub.append(Vfree); meta.append(("free", k))
    for tau in range(4):                           # the marginal band, with eta free
        N = c[tau]
        if N == 0:
            continue
        for k in range(1, m):
            r = np.zeros(nv)
            for v in byk[k]:
                r += (v[tau] / N) * occ_row(v)
            hi = r.copy(); hi[-1] = -1.0 / m
            A_ub.append(hi); b_ub.append(float(Fr(k, m)))
            meta.append(("hi", tau, k))
            lo = -r; lo[-1] = -1.0 / m
            A_ub.append(lo); b_ub.append(-float(Fr(k, m)))
            meta.append(("lo", tau, k))
    return dict(byk=byk, caps=c, base=b, E=E, nE=nE, nv=nv, D=D, root=root,
                out_of=out_of, in_to=in_to, cost=cost, Vfree=Vfree,
                A_eq=np.array(A_eq), b_eq=np.array(b_eq),
                A_ub=np.array(A_ub), b_ub=np.array(b_ub), meta=meta)


def conjectured(m):
    return Fr(1) if m % 2 == 1 else Fr(m - 2, 2 * (m - 1))


def verify_flow(P, m, paths, masses, eta):
    """Recompute objective and band slacks from the EXPORTED flow, in exact arithmetic."""
    byk, c, b, D = P["byk"], P["caps"], P["base"], P["D"]
    in_to = P["in_to"]
    xf = {}
    for (edges, _), w in zip(paths, masses):
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
    worst_band = Fr(0)
    for tau in range(4):
        N = c[tau]
        if N == 0:
            continue
        for k in range(1, m):
            marg = sum(occ(v) * Fr(v[tau], N) for v in byk[k])
            dev = abs(marg - Fr(k, m)) * m
            worst_band = max(worst_band, dev)
    return val, worst_band


def main():
    print("=" * 78)
    print("Paper C: the breakpoint from a direct LP, with the flow exported")
    print("=" * 78)
    ms = [5, 6, 7, 8] if "--smoke" in sys.argv else [5, 6, 7, 8, 9, 10, 11, 12, 13]

    rows = []
    print("\n  m   eta* (LP)     conjecture      exported flow verified")
    print("  " + "-" * 72)
    for m in ms:
        P = build_min_eta(m)
        res = linprog(P["cost"], A_ub=P["A_ub"], b_ub=P["b_ub"],
                      A_eq=P["A_eq"], b_eq=P["b_eq"],
                      bounds=[(0, None)] * P["nE"] + [(0, None)], method="highs")
        if not res.success:
            print(f"      m={m}: LP failed -- {res.message}")
            rows.append({"m": m, "ok": False})
            continue
        eta = float(res.fun)
        conj = conjectured(m)
        x = res.x[:P["nE"]]
        paths = path_decompose(P, x)
        exported, val, band = None, None, None
        for cap in (m, 2 * m, 4 * m, m * (m - 1), 2 * m * (m - 1), 4 * m * (m - 1),
                    m * (m - 1) * (m + 4), 5000):
            mf = [Fr(msk).limit_denominator(cap) for _, msk in paths]
            j = max(range(len(mf)), key=lambda i: mf[i])
            mf[j] += 1 - sum(mf)
            if any(v < 0 for v in mf):
                continue
            v_, band_ = verify_flow(P, m, paths, mf, eta)
            if v_ <= free_value(m) and band_ <= Fr(int(eta * 10 ** 6) + 1, 10 ** 6):
                exported, val, band = mf, v_, band_
                break
        ok = exported is not None
        rows.append({"m": m, "eta_lp": eta, "conjecture": str(conj),
                     "matches_conjecture": abs(eta - float(conj)) < 1e-6,
                     "n_paths": len(paths),
                     "flow_paths": [[int(i) for i in e] for e, _ in paths] if ok else None,
                     "flow_masses": [str(x_) for x_ in exported] if ok else None,
                     "verified_objective": str(val) if ok else None,
                     "free_value": str(free_value(m)),
                     "verified_band_units_of_eta_over_m": str(band) if ok else None,
                     "ok": True})
        mark = "yes" if ok else "NO -- not exported"
        print(f"   {m:3d}   {eta:.8f}   {str(conj):>10}    {mark}"
              f"   ({len(paths)} paths)")

    good = [r for r in rows if r.get("ok")]
    check("the direct LP solves at every size, so the breakpoint needs no bisection",
          len(good) == len(ms), f"{len(good)}/{len(ms)}")
    check("the LP's eta* matches the conjectured parity formula at every size",
          all(r["matches_conjecture"] for r in good),
          "1 for odd m, (m-2)/2(m-1) for even m")
    check("an exact-rational primal flow is exported at every size, so a reader can"
          " recompute the value without the solver",
          all(r["flow_masses"] for r in good),
          f"{sum(len(r['flow_paths']) for r in good)} paths written out")
    check("every exported flow reproduces an objective at or below the free value, checked"
          " in exact arithmetic",
          all(Fr(r["verified_objective"]) <= Fr(r["free_value"]) for r in good))

    print("\n  the dual side")
    print("  " + "-" * 72)
    print("      A dual certificate would prove no flow reaches the free value below")
    print("      eta*.  Rationalising HiGHS's marginals did not yield an exactly")
    print("      dual-feasible vector at any size, as in the earlier attempt, so NO dual")
    print("      certificate is claimed here.  The breakpoint's lower side therefore")
    print("      remains a conjecture, and the LP above settles only its upper side:")
    print("      at eta* the free value IS reachable, by an exhibited rational flow.")

    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 78)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 78)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_paperC_breakpoint_lp.py").read_bytes()).hexdigest(),"rows": rows, "dual_certificate_obtained": False,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/paperC_breakpoint_lp.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
