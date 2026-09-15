#!/usr/bin/env python3
"""Exact rational LP ascent for 2D / ((m-1) delta_square) on the binary cube.

Motivation.  At K=2 the raw rank-one hypothesis is vacuous, so the object is the
plain functional on F : {0,1}^m -> R with corner reference at the all-zero point:

    rho_i(z)   = F(z[i<-1]) - F(z[i<-0])          (discrete derivative)
    delta_sq   = max_i ( max_z rho_i(z) - min_z rho_i(z) )
    comp_i     = F(e_i) - F(0)          score_i = |comp_i|
    G_S(a)     = F(a) - sum_{i in S, a_i = 1} comp_i
    loss_T     = (max_a G_T(a) - min_a G_T(a)) / 2
    S          = top-k coordinates by score_i, k = m // 2
    2D         = 2 (loss_S - min_T loss_T)

Every one of these is a max or a min of LINEAR forms in F.  Fix the combinatorial
pattern -- which z attains each derivative extreme, which coordinate attains
delta_square, the score ordering that selects S, the argmax/argmin of the
selected and competitor losses, and which T is the competitor -- and both 2D and
delta_square become linear.  Normalizing delta_square = 1 turns the
linear-fractional problem into a LINEAR PROGRAM whose optimum sits on a vertex of
a polyhedron with entries in {0, +-1, +-2}.  By Cramer that vertex is rational
with a SMALL denominator, which is what a Lean witness needs; the search-based
route produces 48-digit denominators that norm_num cannot touch.

The float LP finds the combinatorics; the vertex is then recovered EXACTLY over Q
from the active set and evaluated by an exact evaluator that shares no code with
the optimizer.  The LP only ever proposes a point: the exact evaluator decides,
so a wrong or degenerate cell costs an iteration, never a false certificate.

This differs from cell_lp_ascent in run_d6_direct_rankone_linear_fiber_search.py,
which runs the same idea in floating point to generate leads for the rational
snapper.  Here the ascent itself is exact and the fixed point is certified.
"""
from __future__ import annotations
import argparse, itertools, json, random, sys, time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from research_chains.provenance import write_artifact_with_provenance  # noqa: E402

PROTOCOL_VERSION = "d6_binary_exact_lp_ascent_v1"
EVIDENCE_CLASS = "EXACT_RATIONAL_COUNTEREXAMPLE_INDEPENDENTLY_RECOMPUTED"


# ---------------------------------------------------------------- geometry ---
def build(m):
    N = 1 << m
    k = m // 2
    subsets = list(itertools.combinations(range(m), k))
    comp = np.zeros((m, N), dtype=np.int64)
    for i in range(m):
        comp[i, 1 << i] += 1
        comp[i, 0] -= 1
    G = {}
    for S in subsets:
        rows = np.zeros((N, N), dtype=np.int64)
        for a in range(N):
            rows[a, a] += 1
            for i in S:
                if a >> i & 1:
                    rows[a] -= comp[i]
        G[S] = rows
    rho = []
    for i in range(m):
        zs = [z for z in range(N) if not (z >> i & 1)]
        r = np.zeros((len(zs), N), dtype=np.int64)
        for t, z in enumerate(zs):
            r[t, z | (1 << i)] += 1
            r[t, z] -= 1
        rho.append(r)
    return dict(m=m, N=N, k=k, subsets=subsets, comp=comp, G=G, rho=rho)


def pattern(P, x):
    """Combinatorial cell of the point x (x may be float or Fraction array)."""
    m, N = P["m"], P["N"]
    sc = [P["comp"][i] @ x for i in range(m)]
    sgn = [1 if v >= 0 else -1 for v in sc]
    absc = [sgn[i] * sc[i] for i in range(m)]
    order = sorted(range(m), key=lambda i: (-absc[i], i))
    S = tuple(sorted(order[: P["k"]]))
    ext = {}
    for T in P["subsets"]:
        v = P["G"][T] @ x
        amax = int(max(range(N), key=lambda a: v[a]))
        amin = int(min(range(N), key=lambda a: v[a]))
        ext[T] = (amax, amin, v[amax] - v[amin])
    losses = {T: ext[T][2] for T in P["subsets"]}
    Tstar = min((T for T in P["subsets"] if T != S), key=lambda T: losses[T])
    spreads = []
    for i in range(m):
        v = P["rho"][i] @ x
        tmax = int(max(range(len(v)), key=lambda t: v[t]))
        tmin = int(min(range(len(v)), key=lambda t: v[t]))
        spreads.append((tmax, tmin, v[tmax] - v[tmin]))
    istar = int(max(range(m), key=lambda i: spreads[i][2]))
    return dict(sgn=sgn, S=S, Tstar=Tstar, ext=ext, spreads=spreads, istar=istar,
                argmin_all=min(losses, key=lambda T: losses[T]))


def evaluate_exact(P, x):
    """Independent exact evaluator: no LP, no pattern, straight from the definition."""
    m, N = P["m"], P["N"]
    sc = [P["comp"][i] @ x for i in range(m)]
    score = [v if v >= 0 else -v for v in sc]
    order = sorted(range(m), key=lambda i: (-score[i], i))
    S = tuple(sorted(order[: P["k"]]))
    losses = {}
    for T in P["subsets"]:
        v = P["G"][T] @ x
        losses[T] = (max(v) - min(v)) / 2
    delta = max((max(P["rho"][i] @ x) - min(P["rho"][i] @ x)) for i in range(m))
    D = losses[S] - min(losses.values())
    lo = min(score[i] for i in S)
    hi = max(score[i] for i in range(m) if i not in S)
    return dict(delta=delta, selected=S, twoD=2 * D,
                ratio=None if delta == 0 else 2 * D / ((m - 1) * delta),
                margin=lo - hi, strict_top_c=lo > hi,
                margin_relative=None if delta == 0 else (lo - hi) / delta)


# ------------------------------------------------------------------- LP ------
def lp_rows(P, pat, margin):
    """(A_ub, b_ub, A_eq, b_eq, objective) as integer/rational numpy arrays."""
    m, N = P["m"], P["N"]
    A, b = [], []
    for i in range(m):
        r = P["rho"][i]
        tmax, tmin, _ = pat["spreads"][i]
        for t in range(r.shape[0]):
            A.append(r[t] - r[tmax]); b.append(0)      # rho_i(z) <= rho_i(zmax)
            A.append(r[tmin] - r[t]); b.append(0)      # rho_i(zmin) <= rho_i(z)
        A.append(r[tmax] - r[tmin]); b.append(1)       # spread_i <= 1
    for i in range(m):                                  # keep the sign pattern
        A.append(-pat["sgn"][i] * P["comp"][i]); b.append(0)
    for i in pat["S"]:                                  # StrictTopC with margin
        for j in range(m):
            if j not in pat["S"]:
                A.append(-(pat["sgn"][i] * P["comp"][i] - pat["sgn"][j] * P["comp"][j]))
                b.append(-margin)
    for T in (pat["S"], pat["Tstar"]):                  # argmax / argmin validity
        rows = P["G"][T]; amax, amin, _ = pat["ext"][T]
        for a in range(N):
            A.append(rows[a] - rows[amax]); b.append(0)
            A.append(rows[amin] - rows[a]); b.append(0)
    gap_star = (P["G"][pat["Tstar"]][pat["ext"][pat["Tstar"]][0]]
                - P["G"][pat["Tstar"]][pat["ext"][pat["Tstar"]][1]])
    for T in P["subsets"]:                              # Tstar is the cheapest
        if T == pat["Tstar"]:
            continue
        amax, amin, _ = pat["ext"][T]
        A.append(gap_star - (P["G"][T][amax] - P["G"][T][amin])); b.append(0)
    gap_S = (P["G"][pat["S"]][pat["ext"][pat["S"]][0]]
             - P["G"][pat["S"]][pat["ext"][pat["S"]][1]])
    Aeq = [np.eye(N, dtype=np.int64)[0]]                 # gauge F(0) = 0
    beq = [0]
    r = P["rho"][pat["istar"]]
    tmax, tmin, _ = pat["spreads"][pat["istar"]]
    Aeq.append(r[tmax] - r[tmin]); beq.append(1)         # delta_square = 1
    return (np.asarray(A, dtype=float), np.asarray(b, dtype=float),
            np.asarray(Aeq, dtype=float), np.asarray(beq, dtype=float),
            gap_S - gap_star)


def exact_vertex(A, b, Aeq, beq, xf, tol=1e-7):
    """Recover the exact rational vertex from the float LP's active set."""
    N = A.shape[1]
    rows = [(np.rint(Aeq[t]).astype(np.int64), F(int(round(beq[t])))) for t in range(len(beq))]
    res = A @ xf - b
    active = np.argsort(np.abs(res))
    piv, chosen = [], []
    def add(vec, rhs):
        r = [F(int(v)) for v in vec] + [rhs]
        for pc, pr in piv:
            if r[pc] != 0:
                f = r[pc] / pr[pc]
                r = [u - f * w for u, w in zip(r, pr)]
        nz = next((c for c, v in enumerate(r[:N]) if v != 0), None)
        if nz is None:
            return False
        piv.append((nz, r)); chosen.append((vec, rhs)); return True
    for vec, rhs in rows:
        add(vec, rhs)
    for t in active:
        if len(piv) >= N:
            break
        if abs(res[t]) > tol:
            break
        add(np.rint(A[t]).astype(np.int64), F(int(round(b[t]))))
    if len(piv) < N:
        return None
    x = [F(0)] * N
    for pc, pr in reversed(piv):
        s = pr[N]
        for c in range(N):
            if c != pc and pr[c] != 0:
                s -= pr[c] * x[c]
        x[pc] = s / pr[pc]
    return np.asarray(x, dtype=object)


def normalize(P, x):
    """Gauge-fix F(0)=0 and scale to delta_square=1.  The ratio is invariant under
    both (2D and delta_square are homogeneous of degree one; a constant shift
    cancels in every difference), so this only makes the cell well posed."""
    x = np.asarray([F(v) - F(x[0]) for v in x], dtype=object)
    delta = max((max(P["rho"][i] @ x) - min(P["rho"][i] @ x)) for i in range(P["m"]))
    if delta == 0:
        return None
    return np.asarray([v / delta for v in x], dtype=object)


# Fractions of the step from the incumbent to the LP vertex.  An LP optimum sits
# on a vertex, where the active pattern is maximally degenerate: score ties let
# the Top-C tie-break pick a different S, so the ratio AT the vertex can collapse
# even though the LP objective grew.  Stepping only part of the way stays inside
# the cell whose linearization the LP actually maximized.  This mirrors the
# mitigation documented in cell_lp_ascent; taking the vertex itself was the defect
# that made the first version of this ascent lose to random starts.
STEPS = [F(1), F(31, 32), F(7, 8), F(3, 4), F(1, 2), F(1, 4), F(1, 8),
         F(1, 16), F(1, 32), F(1, 64), F(1, 128)]


def ascend(P, x0, *, margin, rounds):
    from scipy.optimize import linprog
    best = normalize(P, [F(v) for v in x0])
    if best is None:
        return None, None, [{"round": -1, "outcome": "DEGENERATE_START_ZERO_DELTA"}]
    bev = evaluate_exact(P, best)
    if bev["ratio"] is None or bev["margin_relative"] < margin:
        return None, None, [{"round": -1, "outcome": "START_FAILS_STRICT_TOPC_GATE",
                             "margin_relative": (None if bev["margin_relative"] is None
                                                 else float(bev["margin_relative"]))}]
    history = [{"round": -1, "ratio": float(bev["ratio"]),
                "margin_relative": float(bev["margin_relative"]), "source": "start"}]
    for rd in range(rounds):
        pat = pattern(P, np.asarray([float(v) for v in best]))
        used_margin = margin
        A, b, Aeq, beq, obj = lp_rows(P, pat, used_margin)
        r = linprog(-obj.astype(float), A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq,
                    bounds=[(-12, 12)] * P["N"], method="highs")
        entry = {"round": rd, "margin_used": str(used_margin), "lp_status": int(r.status)}
        if r.status != 0 or r.x is None:
            entry["outcome"] = "LP_INFEASIBLE_OR_UNBOUNDED"; history.append(entry); break
        entry["lp_objective"] = float(-r.fun)
        entry["lp_predicted_ratio"] = float(-r.fun) / (P["m"] - 1)
        xv = exact_vertex(A, b, Aeq, beq, r.x)
        if xv is None:
            entry["outcome"] = "DEGENERATE_ACTIVE_SET"; history.append(entry); break
        # exact line search from the incumbent towards the vertex
        cand_best, cand_ev, cand_t = None, None, None
        for t in STEPS:
            xt = normalize(P, [(1 - t) * best[a] + t * xv[a] for a in range(P["N"])])
            if xt is None:
                continue
            ev = evaluate_exact(P, xt)
            if ev["ratio"] is None:
                continue
            if ev["margin_relative"] is None or ev["margin_relative"] < margin:
                continue          # StrictTopC gate, applied to the exact point
            if cand_ev is None or ev["ratio"] > cand_ev["ratio"]:
                cand_best, cand_ev, cand_t = xt, ev, t
        if cand_ev is None:
            entry["outcome"] = "NO_ADMISSIBLE_STEP"; history.append(entry); break
        entry["step"] = str(cand_t)
        entry["exact_ratio"] = float(cand_ev["ratio"])
        entry["vertex_ratio"] = float(evaluate_exact(P, xv)["ratio"] or 0)
        entry["strict_top_c"] = bool(cand_ev["strict_top_c"])
        entry["margin_relative"] = float(cand_ev["margin_relative"])
        entry["selected"] = list(cand_ev["selected"])
        entry["cell_selected"] = list(pat["S"])
        history.append(entry)
        if cand_ev["ratio"] > bev["ratio"]:
            best, bev = cand_best, cand_ev
        else:
            entry["outcome"] = "NO_IMPROVEMENT"; break
    return best, bev, history


def tie_perturb_starts(P, x0, *, margin, rounds, eps, tries, rng):
    """Two-phase seeding derived from the measured structure of the extremum.

    The near-extremal points do not sit in the interior: the ascent at margin -> 0
    converges to a ratio that is a fixed multiple of m, and rounding that limit to
    integers lands on a Top-C TIE, where the ratio collapses (0.4 at m=6). The
    supremum is therefore approached from just OFF a tie point, and is not attained.

    So phase 1 runs the ascent with the StrictTopC gate switched off, which is
    exactly what drives an arbitrary start onto a tie attractor; phase 2 perturbs
    that tie point by eps in random directions and keeps the perturbations that
    clear the gate. Those are the seeds handed to the strict ascent. This replaces
    random multi-start, which is trapped in low local basins at every m tested.
    """
    tie, tev, _ = ascend(P, x0, margin=F(0), rounds=rounds)
    if tie is None:
        return []
    seeds = []
    for _ in range(tries):
        d = [F(rng.randint(-1, 1), rng.randint(1, 3)) for _ in range(P["N"])]
        y = normalize(P, [tie[a] + eps * d[a] for a in range(P["N"])])
        if y is None:
            continue
        ev = evaluate_exact(P, y)
        if ev["ratio"] is None or ev["margin_relative"] is None:
            continue
        if ev["margin_relative"] >= margin:
            seeds.append(y)
    return seeds


# ------------------------------------------------------------------ main -----
def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--m", type=int, default=6)
    ap.add_argument("--starts", type=int, default=12)
    ap.add_argument("--rounds", type=int, default=14)
    ap.add_argument("--margin", type=str, default="1/50",
                    help="StrictTopC margin relative to delta_square = 1")
    ap.add_argument("--seed", type=int, default=5)
    ap.add_argument("--seed-world", type=str, default=None,
                    help="ledger artifact whose binary_world seeds start 0")
    ap.add_argument("--seed-mode", choices=("random", "tie-perturb"), default="random")
    ap.add_argument("--eps", type=str, default="1/64",
                    help="perturbation size off the tie point (tie-perturb mode)")
    ap.add_argument("--tries", type=int, default=6,
                    help="random perturbation directions per tie point")
    ap.add_argument("--out", type=str, default=None)
    args = ap.parse_args(argv)

    t0 = time.time()
    P = build(args.m)
    margin = F(args.margin)
    rng = random.Random(args.seed)
    starts = []
    if args.seed_world:
        d = json.load(open(args.seed_world))
        w = {tuple(e["action"]): F(e["value"]) for e in d["binary_world"]}
        vec = [w[tuple((a >> i) & 1 for i in range(P["m"]))] for a in range(P["N"])]
        starts.append(("ledger_witness", vec))
    while len(starts) < args.starts:
        starts.append((f"random_{len(starts)}",
                       [F(rng.randint(-40, 40), rng.randint(1, 9)) for _ in range(P["N"])]))

    if args.seed_mode == "tie-perturb":
        expanded = []
        for name, x0 in starts:
            for j, y in enumerate(tie_perturb_starts(
                    P, x0, margin=margin, rounds=args.rounds, eps=F(args.eps),
                    tries=args.tries, rng=rng)):
                expanded.append((f"{name}~tie+eps#{j}", list(y)))
        if expanded:
            starts = expanded

    runs, best_overall = [], None
    for name, x0 in starts:
        x, ev, hist = ascend(P, x0, margin=margin, rounds=args.rounds)
        if ev is None:
            runs.append({"start": name, "outcome": "DEGENERATE_START", "history": hist})
            continue
        rec = {"start": name,
               "start_ratio": hist[0]["ratio"],
               "final_ratio": None if ev["ratio"] is None else str(ev["ratio"]),
               "final_ratio_float": None if ev["ratio"] is None else float(ev["ratio"]),
               "strict_violation": bool(ev["ratio"] is not None and ev["ratio"] > 1),
               "strict_top_c": bool(ev["strict_top_c"]),
               "margin_relative": None if ev["margin_relative"] is None else float(ev["margin_relative"]),
               "selected": list(ev["selected"]),
               "delta_square": str(ev["delta"]), "doubled_decision_gap": str(ev["twoD"]),
               "max_denominator": max(v.denominator for v in x),
               "rounds_used": len(hist) - 1, "history": hist}
        runs.append(rec)
        if ev["ratio"] is not None and (best_overall is None
                                        or ev["ratio"] > best_overall[0]):
            best_overall = (ev["ratio"], x, ev, rec)

    if best_overall is None:
        print(json.dumps({"m": args.m, "status": "ALL_STARTS_DEGENERATE",
                          "starts": args.starts,
                          "outcomes": [r.get("outcome") or (r.get("history") or [{}])[-1].get("outcome")
                                       for r in runs]}, indent=2))
        return 2
    ratio, xbest, evbest, recbest = best_overall
    result = {
        "protocol_version": PROTOCOL_VERSION, "development_only": True,
        "evidence_class": EVIDENCE_CLASS,
        "m": args.m, "alphabet": 2, "reference": "corner (all-zero), deterministic",
        "hypothesis": "none -- at K=2 AllCoordinatesRawLocalContrastRankOne is vacuous",
        "method": "exact rational LP ascent over the polyhedral cell decomposition; "
                  "float LP fixes the cell, the vertex is recovered exactly over Q from "
                  "the active set, and an independent exact evaluator certifies it",
        "starts": args.starts, "rounds_cap": args.rounds,
        "strict_top_c_margin_imposed": str(margin),
        "best_exact_ratio": str(ratio), "best_exact_ratio_float": float(ratio),
        "best_strict_violation": bool(ratio > 1),
        "best_max_denominator": max(v.denominator for v in xbest),
        "best_delta_square": str(evbest["delta"]),
        "best_doubled_decision_gap": str(evbest["twoD"]),
        "best_selected": list(evbest["selected"]),
        "best_top_c_margin": str(evbest["margin"]),
        "best_top_c_margin_relative_float": float(evbest["margin_relative"]),
        "best_start": recbest["start"],
        "status": "KILLED" if ratio > 1 else "NO_VIOLATION_FOUND",
        "world": [{"action": [(a >> i) & 1 for i in range(args.m)], "value": str(xbest[a])}
                  for a in range(P["N"])],
        "runs": runs,
        "wall_clock_seconds": round(time.time() - t0, 3),
    }
    out = Path(args.out) if args.out else (
        ROOT / "research/d6_contrast_rank_falsification"
        / f"LPascent_m{args.m}_K2_s{args.seed}.json")
    if out.exists():
        raise SystemExit(f"refusing to overwrite existing ledger artifact: {out}")
    write_artifact_with_provenance(
        out, result,
        protocol={"protocol_version": PROTOCOL_VERSION, "m": args.m, "alphabet": 2,
                  "starts": args.starts, "rounds": args.rounds, "margin": str(margin)},
        seed=args.seed, evidence_class=EVIDENCE_CLASS, chain="D6")
    print(json.dumps({
        "m": args.m, "status": result["status"],
        "best_exact_ratio": result["best_exact_ratio"],
        "best_exact_ratio_float": result["best_exact_ratio_float"],
        "strict_violation": result["best_strict_violation"],
        "max_denominator": result["best_max_denominator"],
        "top_c_margin_relative": result["best_top_c_margin_relative_float"],
        "best_start": result["best_start"],
        "violating_starts": sum(1 for r in runs if r.get("strict_violation")),
        "starts": args.starts,
        "wall_clock_seconds": result["wall_clock_seconds"], "out": str(out)}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
