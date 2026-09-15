#!/usr/bin/env python3
"""Maximise the loss spread ON the Top-C tie locus, exactly, by linear programming.

Where this sits.  Three obstructions have been peeled off in order:

  * the stochastic countersearch misses violations that exist in the space it
    sweeps (addendum C Section 105);
  * the exact LP ascent climbs but is local, and the departure DIRECTION at a tie
    point cannot be sampled (Section 108) -- solved by enumerating the finitely
    many achievable Top-C selections (run_d6_tangent_cone_seeding.py);
  * what remains is WHICH tie point.  The limiting ratio off a tie point is
    2 (l_S - l_min) / ((m-1) delta_square) evaluated AT that point, so the whole
    question is now: over the tie locus, how large can the loss spread be?

Why this one is an LP and the earlier ones were not.  On the tie locus we WANT
the ties, so the strict-Top-C margin that made the ascent degenerate is simply
absent.  "All oscillations equal" is a linear EQUALITY, eps_i c_i = eps_j c_j
with c_i = F(e_i) - F(0).  And delta_square <= 1 is a convex constraint needing
no cell pattern at all: introduce u_i, l_i with l_i <= rho_i(z) <= u_i for every
context z and u_i - l_i <= 1.  Only the two compression losses need a pattern,
namely one argmax/argmin pair each, and those are refined to a fixed point.

Objective.  2 l_S - 2 l_{T*} with T* fixed to the complement of S, the structure
observed at the m=6 extremum.  Since min_T l_T <= l_{T*}, the value returned is a
LOWER bound on the true limiting ratio, so the construction can only understate
itself; the exact evaluator decides the real value afterwards.

The LP fixes combinatorics in floating point; the vertex is recovered exactly
over Q from the active set and every reported number is computed by the
independent exact evaluator.
"""
from __future__ import annotations
import argparse, itertools, json, sys, time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(ROOT / "scripts"))
from research_chains.provenance import write_artifact_with_provenance  # noqa: E402
from run_d6_binary_exact_lp_ascent import build, evaluate_exact, normalize  # noqa: E402
from run_d6_tangent_cone_seeding import limit_ratios, direction_for  # noqa: E402

PROTOCOL_VERSION = "d6_tie_locus_lp_v1"
EVIDENCE_CLASS = "EXACT_RATIONAL_COUNTEREXAMPLE_INDEPENDENTLY_RECOMPUTED"


def solve_cell(P, S, Tst, aSp, aSm, aTp, aTm, eps, box):
    """One LP on the tie locus.  Variables: F (N), u_i, l_i (2m), p, q (2)."""
    from scipy.optimize import linprog
    m, N = P["m"], P["N"]
    nv = N + 2 * m + 2
    iu = lambda i: N + i
    il = lambda i: N + m + i
    ip, iq = N + 2 * m, N + 2 * m + 1

    A, b, Aeq, beq = [], [], [], []

    def row(vec_on_F=None):
        r = np.zeros(nv)
        if vec_on_F is not None:
            r[:N] = vec_on_F
        return r

    # delta_square <= 1, with no cell pattern: l_i <= rho_i(z) <= u_i, u_i - l_i <= 1
    for i in range(m):
        R = P["rho"][i]
        for t in range(R.shape[0]):
            r = row(R[t]); r[iu(i)] = -1.0; A.append(r); b.append(0.0)   # rho <= u_i
            r = row(-R[t]); r[il(i)] = 1.0; A.append(r); b.append(0.0)   # l_i <= rho
        r = np.zeros(nv); r[iu(i)] = 1.0; r[il(i)] = -1.0
        A.append(r); b.append(1.0)

    # competitor loss: q <= G_{T*}(a) <= p for every a; objective subtracts (p - q)
    GT = P["G"][Tst]
    for a in range(N):
        r = row(GT[a]); r[ip] = -1.0; A.append(r); b.append(0.0)
        r = row(-GT[a]); r[iq] = 1.0; A.append(r); b.append(0.0)

    # selected loss pattern: the recorded pair must really be the extremes
    GS = P["G"][S]
    for a in range(N):
        A.append(row(GS[a] - GS[aSp])); b.append(0.0)
        A.append(row(GS[aSm] - GS[a])); b.append(0.0)

    # tie locus: eps_i c_i all equal and nonnegative
    c = [P["comp"][i] for i in range(m)]
    for i in range(1, m):
        Aeq.append(row(eps[0] * c[0] - eps[i] * c[i])); beq.append(0.0)
    for i in range(m):
        A.append(row(-eps[i] * c[i])); b.append(0.0)

    Aeq.append(row(np.eye(N)[0])); beq.append(0.0)            # gauge F(0) = 0

    obj = row(GS[aSp] - GS[aSm]); obj[ip] = -1.0; obj[iq] = 1.0
    bounds = [(-box, box)] * N + [(-box, box)] * (2 * m) + [(-box, box)] * 2
    r = linprog(-obj, A_ub=np.asarray(A), b_ub=np.asarray(b),
                A_eq=np.asarray(Aeq), b_eq=np.asarray(beq),
                bounds=bounds, method="highs")
    return r, np.asarray(A), np.asarray(b), np.asarray(Aeq), np.asarray(beq), obj


def exact_from_active(A, b, Aeq, beq, xf, N, tol=1e-7):
    """Recover the F-block of the vertex exactly over Q from the active set."""
    nv = A.shape[1]
    piv, rows = [], [(np.rint(Aeq[t]).astype(np.int64), F(int(round(beq[t]))))
                     for t in range(len(beq))]
    res = A @ xf - b
    order = np.argsort(np.abs(res))

    def add(vec, rhs):
        r = [F(int(v)) for v in vec] + [rhs]
        for pc, pr in piv:
            if r[pc] != 0:
                f = r[pc] / pr[pc]
                r = [u - f * w for u, w in zip(r, pr)]
        nz = next((cc for cc, v in enumerate(r[:nv]) if v != 0), None)
        if nz is None:
            return False
        piv.append((nz, r)); return True

    for vec, rhs in rows:
        add(vec, rhs)
    for t in order:
        if len(piv) >= nv:
            break
        if abs(res[t]) > tol:
            break
        add(np.rint(A[t]).astype(np.int64), F(int(round(b[t]))))
    if len(piv) < nv:
        return None
    x = [F(0)] * nv
    for pc, pr in reversed(piv):
        s = pr[nv]
        for cc in range(nv):
            if cc != pc and pr[cc] != 0:
                s -= pr[cc] * x[cc]
        x[pc] = s / pr[pc]
    return np.asarray(x[:N], dtype=object)


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--rounds", type=int, default=8)
    ap.add_argument("--box", type=float, default=12.0)
    ap.add_argument("--t", type=str, default="1/64")
    ap.add_argument("--seed", type=int, default=5)
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args(argv)

    t0 = time.time()
    P = build(args.m); N, m, k = P["N"], P["m"], P["k"]
    S = tuple(range(k)); Tst = tuple(range(k, m))
    if Tst not in P["G"]:
        Tst = min((T for T in P["subsets"] if T != S))
    eps = [1] * m
    # start from a generic point to read an initial argmax/argmin pattern
    rng = np.random.default_rng(args.seed)
    x = np.asarray([F(int(v), 7) for v in rng.integers(-20, 21, N)], dtype=object)
    x[0] = F(0)
    hist, best = [], None
    for rd in range(args.rounds):
        vS = P["G"][S] @ x; vT = P["G"][Tst] @ x
        aSp = int(max(range(N), key=lambda a: vS[a])); aSm = int(min(range(N), key=lambda a: vS[a]))
        aTp = int(max(range(N), key=lambda a: vT[a])); aTm = int(min(range(N), key=lambda a: vT[a]))
        r, A, b, Aeq, beq, obj = solve_cell(P, S, Tst, aSp, aSm, aTp, aTm, eps, args.box)
        entry = {"round": rd, "lp_status": int(r.status)}
        if r.status != 0 or r.x is None:
            entry["outcome"] = "LP_INFEASIBLE_OR_UNBOUNDED"; hist.append(entry); break
        entry["lp_objective"] = float(-r.fun)
        entry["lp_limit_ratio"] = float(-r.fun) / (m - 1)
        xv = exact_from_active(A, b, Aeq, beq, r.x, N)
        if xv is None:
            entry["outcome"] = "DEGENERATE_ACTIVE_SET"; hist.append(entry); break
        y = normalize(P, xv)
        if y is None:
            entry["outcome"] = "ZERO_DELTA"; hist.append(entry); break
        rows, osc, cc, losses, delta = limit_ratios(P, y)
        entry["all_oscillations_equal"] = len(set(osc)) == 1
        entry["best_limit_ratio"] = rows[0]["limit_ratio"]
        entry["best_limit_ratio_float"] = rows[0]["limit_ratio_float"]
        entry["loss_spectrum"] = sorted({rw["loss_selected"] for rw in rows})
        hist.append(entry)
        if best is None or (rows[0]["limit_ratio_float"] or 0) > best[0]:
            best = (rows[0]["limit_ratio_float"], y, rows, osc, cc, delta)
        x = y

    result = {"protocol_version": PROTOCOL_VERSION, "development_only": True,
              "evidence_class": EVIDENCE_CLASS, "m": m, "alphabet": 2,
              "reference": "corner (all-zero)", "selected": list(S), "competitor": list(Tst),
              "method": "LP on the Top-C tie locus: tie equalities are linear, delta_square <= 1 "
                        "is convex and needs no cell pattern, only the two loss argmax/argmin "
                        "pairs are refined to a fixed point; vertex recovered exactly over Q",
              "derived_prediction_2k_over_m_minus_1": str(F(2 * k, m - 1)),
              "derived_prediction_float": float(F(2 * k, m - 1)),
              "history": hist}
    if best is not None:
        ratio, y, rows, osc, cc, delta = best
        S2 = tuple(rows[0]["selected"]); grp = tuple(rows[0]["tied_group"])
        result.update({
            "status": "TIE_POINT_FOUND",
            "best_limit_ratio": rows[0]["limit_ratio"],
            "best_limit_ratio_float": ratio,
            "predicts_violation": bool(ratio is not None and ratio > 1),
            "oscillations": [str(v) for v in osc], "delta_square": str(delta),
            "loss_spectrum": sorted({rw["loss_selected"] for rw in rows}),
            "achievable_selections": rows[:12],
            "tie_world": [{"action": [(a >> i) & 1 for i in range(m)], "value": str(y[a])}
                          for a in range(N)]})
        if grp:
            d = direction_for(P, y, S2, grp, cc)
            step = F(args.t)
            seed = normalize(P, [y[a] + step * d[a] for a in range(N)])
            if seed is not None:
                ev = evaluate_exact(P, seed)
                result["seed_off_tie"] = {
                    "t": str(step), "exact_ratio": str(ev["ratio"]),
                    "exact_ratio_float": float(ev["ratio"]),
                    "strict_violation": bool(ev["ratio"] > 1),
                    "strict_top_c": bool(ev["strict_top_c"]),
                    "margin_relative_float": float(ev["margin_relative"]),
                    "max_denominator": max(v.denominator for v in seed),
                    "world": [{"action": [(a >> i) & 1 for i in range(m)], "value": str(seed[a])}
                              for a in range(N)]}
    else:
        result["status"] = "NO_TIE_POINT"
    result["wall_clock_seconds"] = round(time.time() - t0, 3)

    out = Path(args.out) if args.out else (
        ROOT / "research/d6_contrast_rank_falsification" / f"TieLP_m{m}_K2_s{args.seed}.json")
    if out.exists():
        raise SystemExit(f"refusing to overwrite existing ledger artifact: {out}")
    write_artifact_with_provenance(
        out, result, protocol={"protocol_version": PROTOCOL_VERSION, "m": m,
                               "rounds": args.rounds, "box": args.box},
        seed=args.seed, evidence_class=EVIDENCE_CLASS, chain="D6")
    print(json.dumps({kk: result[kk] for kk in
                      ("m", "status", "best_limit_ratio", "best_limit_ratio_float",
                       "derived_prediction_2k_over_m_minus_1", "predicts_violation",
                       "loss_spectrum", "wall_clock_seconds") if kk in result}
                     | {"seed_ratio": (result.get("seed_off_tie") or {}).get("exact_ratio_float"),
                        "seed_maxden": (result.get("seed_off_tie") or {}).get("max_denominator"),
                        "out": str(out)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
