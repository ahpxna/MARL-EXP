#!/usr/bin/env python3
"""Certified lower bounds on c*(m) = sup 2D/delta_square by face enumeration.

The programme.  D6's (m-1) law is closed: PROVED FALSE in Lean, unconditionally,
on the binary cube.  What is open is the SHARP CONSTANT

    c*(m) = sup { 2D(F) / delta_square(F) : F : {0,1}^m -> R, StrictTopC }.

Every ingredient is a max or a min of linear forms in F, so the problem is
piecewise linear:  fix the combinatorics and it becomes a linear program.  The
correct object is therefore a FINITE FAMILY OF RATIONAL LPs, one per face, and
c* is the max over the family.

What this file does and does not do.  Full enumeration of
(S, T, a_S^+, a_S^-, a_T^+, a_T^-) is 20 * 19 * 64^4 ~ 6.4e9 cells at m = 6 and
2e13 at m = 8: not runnable.  The dimension that the earlier tie-locus LP wrongly
froze to a single choice is (S, T), and that one IS enumerable -- 380 pairs at
m = 6.  So (S, T) is enumerated exhaustively and the four extremal points are
obtained by pattern iteration from several starts.  The value returned is
therefore a CERTIFIED LOWER BOUND on c*(m) over the faces actually visited, never
c* itself.  Reporting it as c* would be the same error as reading a
countersearch's silence as proof.

Formulation notes, in the order they matter.

* `delta_square <= 1` needs no cell pattern: it is convex.  Introduce u_i, l_i
  with l_i <= rho_i(z) <= u_i for every context and u_i - l_i <= 1.
* the competitor loss is bounded ABOVE by aux p, q with q <= G_T(a) <= p, and the
  objective subtracts (p - q).  The optimiser drives p - q down to exactly
  2*l_T, so this direction is safe.  Bounding l_T from BELOW by a variable y with
  y <= L_T and maximising L_S - y is NOT safe: the optimiser pushes y down and
  the formulation is wrong.  That trap is why the competitor is enumerated
  instead of minimised.
* T must be the true argmin, so `p - q <= G_U(a_U^+) - G_U(a_U^-)` is imposed for
  every other U at its recorded extremal pair.  The right-hand side is at most
  2*l_U, so this really does force l_T <= l_U.
* StrictTopC enters as an explicit margin on the ordering, not as a tie.

The LP fixes combinatorics in floating point; the vertex is recovered exactly
over Q from the active set and every reported number comes from an independent
exact evaluator.
"""
from __future__ import annotations
import argparse, itertools, json, random, sys, time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT)); sys.path.insert(0, str(ROOT / "scripts"))
from research_chains.provenance import write_artifact_with_provenance  # noqa: E402
from run_d6_binary_exact_lp_ascent import build, evaluate_exact, normalize, STEPS  # noqa: E402
from run_d6_tie_locus_lp import exact_from_active  # noqa: E402

PROTOCOL_VERSION = "d6_face_enumeration_lp_v1"
EVIDENCE_CLASS = "EXACT_RATIONAL_LOWER_BOUND_ON_SHARP_CONSTANT"


def solve_face(P, S, T, pat, margin, box):
    from scipy.optimize import linprog
    m, N = P["m"], P["N"]
    nv = N + 2 * m + 2
    iu = lambda i: N + i
    il = lambda i: N + m + i
    ip, iq = N + 2 * m, N + 2 * m + 1
    A, b, Aeq, beq = [], [], [], []

    def row(v=None):
        r = np.zeros(nv)
        if v is not None:
            r[:N] = v
        return r

    for i in range(m):                                   # delta_square <= 1, convex
        R = P["rho"][i]
        for t in range(R.shape[0]):
            r = row(R[t]); r[iu(i)] = -1.0; A.append(r); b.append(0.0)
            r = row(-R[t]); r[il(i)] = 1.0; A.append(r); b.append(0.0)
        r = np.zeros(nv); r[iu(i)] = 1.0; r[il(i)] = -1.0; A.append(r); b.append(1.0)

    GT = P["G"][T]
    for a in range(N):                                   # q <= G_T(a) <= p
        r = row(GT[a]); r[ip] = -1.0; A.append(r); b.append(0.0)
        r = row(-GT[a]); r[iq] = 1.0; A.append(r); b.append(0.0)

    GS = P["G"][S]
    aSp, aSm = pat["S"]
    for a in range(N):                                   # the recorded S-extrema are real
        A.append(row(GS[a] - GS[aSp])); b.append(0.0)
        A.append(row(GS[aSm] - GS[a])); b.append(0.0)

    for U in P["subsets"]:                               # T is the cheapest subset
        if U == T:
            continue
        aUp, aUm = pat["ext"][U]
        r = row(-(P["G"][U][aUp] - P["G"][U][aUm])); r[ip] = 1.0; r[iq] = -1.0
        A.append(r); b.append(0.0)

    c = [P["comp"][i] for i in range(m)]                  # StrictTopC with a margin
    eps = pat["sgn"]
    for i in range(m):
        A.append(row(-eps[i] * c[i])); b.append(0.0)
    for i in S:
        for j in range(m):
            if j not in S:
                A.append(row(-(eps[i] * c[i] - eps[j] * c[j]))); b.append(-float(margin))

    Aeq.append(row(np.eye(N)[0])); beq.append(0.0)        # gauge F(0) = 0

    # The box must live in A_ub, not in linprog's `bounds`.  A variable resting on
    # a bound IS an active constraint, and the exact vertex is recovered from the
    # active set; bounds passed separately are invisible to that recovery, which
    # then cannot reach full rank.  That defect accounted for ten of thirty faces
    # reported DEGENERATE_ACTIVE_SET at m = 4.
    for v in range(nv):
        e = np.zeros(nv); e[v] = 1.0
        A.append(e.copy()); b.append(box)
        A.append(-e); b.append(box)

    obj = row(GS[aSp] - GS[aSm]); obj[ip] = -1.0; obj[iq] = 1.0
    r = linprog(-obj, A_ub=np.asarray(A), b_ub=np.asarray(b),
                A_eq=np.asarray(Aeq), b_eq=np.asarray(beq),
                bounds=[(None, None)] * nv, method="highs")
    return r, np.asarray(A), np.asarray(b), np.asarray(Aeq), np.asarray(beq)


def pattern_at(P, x, S, T):
    m, N = P["m"], P["N"]
    ext = {}
    for U in P["subsets"]:
        v = P["G"][U] @ x
        ext[U] = (int(max(range(N), key=lambda a: v[a])), int(min(range(N), key=lambda a: v[a])))
    sc = [P["comp"][i] @ x for i in range(m)]
    return {"S": ext[S], "T": ext[T], "ext": ext,
            "sgn": [1 if v >= 0 else -1 for v in sc]}


def run_pair(P, S, T, starts, rounds, margin, box, rng, seed_world=None):
    """Iterate the extremal pattern to a fixed point; ACCEPT only admissible points.

    Iterating and accepting are separate.  The first version aborted the whole
    start as soon as one iterate missed the StrictTopC gate, which threw away the
    trajectory before it had converged and left 28 of 30 faces looking infeasible
    at m = 4.  The LP iterate always becomes the next point; it is recorded only
    when the exact evaluator says it is admissible.
    """
    best, why = None, None
    for si in range(starts):
        if seed_world is not None and si == 0:
            x = seed_world.copy()
        else:
            x = np.asarray([F(int(v), 7) for v in rng.integers(-20, 21, P["N"])], dtype=object)
            x[0] = F(0)
        for _ in range(rounds):
            pat = pattern_at(P, np.asarray([float(v) for v in x]), S, T)
            r, A, b, Aeq, beq = solve_face(P, S, T, pat, margin, box)
            if r.status != 0 or r.x is None:
                why = "LP_INFEASIBLE_OR_UNBOUNDED"; break
            xv = exact_from_active(A, b, Aeq, beq, r.x, P["N"])
            if xv is None:
                why = "DEGENERATE_ACTIVE_SET"; break
            # An LP optimum sits on a vertex, where the pattern is maximally
            # degenerate and the Top-C tie-break can pick a different S; the face
            # the LP linearised is then no longer the face the point is in.  Step
            # only part of the way, exactly as in the ascent, where taking the
            # vertex itself was what made the first version lose to random starts.
            cand = None
            for t in STEPS:
                yt = normalize(P, [(1 - t) * x[a] + t * xv[a] for a in range(P["N"])])
                if yt is None:
                    continue
                evt = evaluate_exact(P, yt)
                if evt["ratio"] is None or evt["margin_relative"] is None:
                    continue
                if evt["margin_relative"] < margin or evt["selected"] != S:
                    continue
                if cand is None or evt["ratio"] > cand[1]["ratio"]:
                    cand = (yt, evt)
            if cand is None:
                why = "NO_ADMISSIBLE_STEP"
                y = normalize(P, xv)
                if y is None:
                    break
                x = y
                continue
            y, ev = cand
            x = y
            if best is None or ev["ratio"] > best[0]:
                best = (ev["ratio"], y, ev)
    return best, why


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--starts", type=int, default=2)
    ap.add_argument("--rounds", type=int, default=5)
    ap.add_argument("--margin", type=str, default="1/1000")
    ap.add_argument("--box", type=float, default=12.0)
    ap.add_argument("--pairs-limit", type=int, default=0, help="0 = all (S,T) pairs")
    ap.add_argument("--seed", type=int, default=5)
    ap.add_argument("--seed-world", type=str, default=None,
                    help="ledger artifact whose world seeds every face instead of random "
                         "starts; the one thing the ascent was reliably good at was "
                         "IMPROVING a known point, so this is the honest use of the LP")
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args(argv)

    t0 = time.time()
    P = build(args.m); m, k = P["m"], P["k"]
    margin = F(args.margin)
    rng = np.random.default_rng(args.seed)
    pairs = [(S, T) for S in P["subsets"] for T in P["subsets"] if S != T]
    if args.pairs_limit and args.pairs_limit < len(pairs):
        idx = random.Random(args.seed).sample(range(len(pairs)), args.pairs_limit)
        pairs = [pairs[i] for i in idx]

    seedw = None
    if args.seed_world:
        dd = json.load(open(args.seed_world))
        # Artifacts store the witness in different places: the LP/ascent files at top
        # level, the sweep files under one of the witness records.  Try them in order
        # of specificity rather than assuming a single key.
        rec = None
        for key in ("world", "binary_world", "tie_world"):
            if key in dd:
                rec = dd[key]; break
        if rec is None:
            for holder in ("counterexample", "strict_top_c_witness", "tightness_witness"):
                if holder in dd and dd[holder] and "world" in dd[holder]:
                    rec = dd[holder]["world"]; break
        if rec is None:
            raise SystemExit(f"no world found in {args.seed_world}; "
                             f"top-level keys: {sorted(dd)[:20]}")
        w = {tuple(e["action"]): F(e["value"]) for e in rec}
        if any(len(a) != m or max(a) > 1 for a in w):
            raise SystemExit("seed world is not on the binary cube")
        seedw = np.asarray([w[tuple((a >> i) & 1 for i in range(m))] for a in range(P["N"])],
                           dtype=object)

    rows, best = [], None
    for S, T in pairs:
        res, why = run_pair(P, S, T, args.starts, args.rounds, margin, args.box, rng, seedw)
        if res is None:
            rows.append({"selected": list(S), "competitor": list(T),
                         "status": "NO_FEASIBLE", "reason": why})
            continue
        ratio, y, ev = res
        rows.append({"selected": list(S), "competitor": list(T), "status": "OK",
                     "ratio": str(ratio), "ratio_float": float(ratio),
                     "strict_violation": bool(ratio > 1),
                     "margin_relative": float(ev["margin_relative"]),
                     "max_denominator": max(v.denominator for v in y),
                     "is_complement": list(T) == sorted(set(range(m)) - set(S))})
        if best is None or ratio > best[0]:
            best = (ratio, y, ev, S, T)

    ok = [r for r in rows if r["status"] == "OK"]
    ok.sort(key=lambda r: -r["ratio_float"])
    result = {
        "protocol_version": PROTOCOL_VERSION, "development_only": True,
        "evidence_class": EVIDENCE_CLASS, "m": m, "alphabet": 2,
        "reference": "corner (all-zero)", "k": k,
        "hypothesis": "none -- raw rank one is vacuous at K=2; the (m-1) law is PROVED FALSE",
        "target": "c*(m) = sup 2D/delta_square over StrictTopC worlds on the binary cube",
        "what_is_reported": "a CERTIFIED LOWER BOUND over the (S,T) faces actually visited, "
                            "not c* itself",
        "strict_top_c_margin": str(margin),
        "pairs_total": len([1 for S in P["subsets"] for T in P["subsets"] if S != T]),
        "pairs_visited": len(pairs), "pairs_feasible": len(ok),
        "starts_per_pair": args.starts, "rounds_per_start": args.rounds,
        "derived_reference_2k_over_m_minus_1": str(F(2 * k, m - 1)),
        "derived_reference_float": float(F(2 * k, m - 1)),
        "top_faces": ok[:20],
        "all_faces": rows,
        "wall_clock_seconds": round(time.time() - t0, 3),
    }
    if best is not None:
        ratio, y, ev, S, T = best
        result.update({
            "status": "LOWER_BOUND_ESTABLISHED",
            "best_ratio": str(ratio), "best_ratio_float": float(ratio),
            "best_strict_violation": bool(ratio > 1),
            "best_selected": list(S), "best_competitor": list(T),
            "best_competitor_is_complement": list(T) == sorted(set(range(m)) - set(S)),
            "best_margin_relative": float(ev["margin_relative"]),
            "best_delta_square": str(ev["delta"]),
            "best_doubled_decision_gap": str(ev["twoD"]),
            "best_max_denominator": max(v.denominator for v in y),
            "world": [{"action": [(a >> i) & 1 for i in range(m)], "value": str(y[a])}
                      for a in range(P["N"])]})
    else:
        result["status"] = "NO_FEASIBLE_FACE"

    out = Path(args.out) if args.out else (
        ROOT / "research/d6_contrast_rank_falsification" / f"FaceLP_m{m}_K2_s{args.seed}.json")
    if out.exists():
        raise SystemExit(f"refusing to overwrite existing ledger artifact: {out}")
    write_artifact_with_provenance(
        out, result, protocol={"protocol_version": PROTOCOL_VERSION, "m": m,
                               "starts": args.starts, "rounds": args.rounds,
                               "margin": str(margin), "pairs_limit": args.pairs_limit},
        seed=args.seed, evidence_class=EVIDENCE_CLASS, chain="D6")
    print(json.dumps({kk: result[kk] for kk in
        ("m","status","best_ratio","best_ratio_float","best_strict_violation",
         "best_selected","best_competitor","best_competitor_is_complement",
         "derived_reference_2k_over_m_minus_1","best_max_denominator",
         "pairs_visited","pairs_feasible","wall_clock_seconds") if kk in result}
        | {"out": str(out)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
