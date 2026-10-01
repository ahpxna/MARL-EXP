#!/usr/bin/env python3
"""P1 step 1: exact revision frontier of the D6 compression loss on the m = 6 family.

Model, transcribed from the Lean definitions (file:def):
  * world F : (Fin 6 -> Fin 2) -> R.  Family Vb s = 2 s * Ib + Db
      (LeanD6SharpnessM6V1.lean: Ib, Db, Vb; Ib and Db are PARSED from that file, not retyped).
  * reference q : Fin 6 -> Fin 2 -> R, product weights jointWeight q c = prod_i q i (c i)
      (LeanProductMixedDifferenceV4.lean: jointWeight).  The family uses the corner reference
      cornerQ2 i u = if u = 0 then 1 else 0 (LeanD6BinaryBridgeV1.lean: cornerQ2).
  * productResponse q F i u = sum_c jointWeight q c * F (update c i u)
      (LeanProductMixedDifferenceV4.lean: productExpectation, productResponse).
  * retainedResidual q F S x = F x - sum_{j in S} productResponse q F j (x j)
      (LeanD6H3Exchange.lean: retainedResidual).
  * loss l_S = productCompressionLoss F (productResponse q F) S = osc(retainedResidual S) / 2
      (LeanProductMixedDifferenceV4.lean: productCompressionLoss; LeanSupportGeometryV4.lean: osc).
  * mixedDifference F i x c = F x - F (update x i (c i)) - F (update c i (x i)) + F c
      (LeanProductSurrogateV4.lean: mixedDifference);  delta_box = max_{i,x,c} |mixedDifference|,
      the least delta satisfying the hdelta hypothesis of pair_loss_le_sdiff_card.
  * score j = osc (productResponse q F j)  (response span; the IsTopKByScore score in
      LeanD6SmallSymmetricDifference.pair_loss_le_sdiff_card and
      LeanD6SharpMarginThresholdV1.margin_two_sufficient).
  * Top-k sets: IsTopKByScore C S k := S.card = k and every k-set has score sum <= S's
      (LeanSupportGeometryV4.lean: IsTopKByScore).  With ties there can be several; all are reported.

Quantities, for each budget k = 1..5:
  * l*_k = min over |S| = k of l_S, and the set of optimal k-sets;
  * for each Top-k prefix P: d_k(P) = min over optimal T of |P \\ T|;
    F_k(R) = min over |S'| = k, |S' \\ P| <= R of l_{S'} - l*_k,  R = 0..min(k, 6-k);
  * G(R) = min over all 720 rankings pi of max_k min_{|S'| = k, |S' \\ pi_k| <= R} (l_{S'} - l*_k).

Self-checks (each can fail; the script refuses to write the JSON if any fails):
  * Lean-proved numbers on Vb s: delta_box = 2s+2 (integer_family_interaction_exact),
    2(l_{0,4,5} - l_{1,2,3}) = 12 s (twoD_eq), spans (2s+1, 2s-1, 2s-1, 2s-1, 2s+1, 2s+1)
    (comp_eq, strict_topC_margin_two), unique Top-3 set {0,4,5} with margin 2, the residual
    extremes gSelI/gSelD/gComI/gComD values, and 2D/delta_box = 6s/(s+1)
    (normalized_family_bridge).
  * pair_loss_le_sdiff_card on every (Top-k P, competitor T) pair;
    pair_loss_le_sdiff_card_sub_score_surplus on every such pair.
  * Monotonicity F_k(R+1) <= F_k(R), F_k(min(k,6-k)) = 0, G(R+1) <= G(R).

Exact arithmetic throughout (fractions.Fraction).  No solver, no tolerance.
"""
import hashlib
import itertools
import json
import os
import re
import sys
from fractions import Fraction as Fr

REPO = "/Users/phanan/cig-amf-main"
LEAN_DIR = os.path.join(REPO, "work/p13_conjectures")
OUT_DIR = os.path.join(REPO, "research/marl_budget/P1_d6_frontier")
M = 6
CUBE = list(itertools.product((0, 1), repeat=M))


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def parse_lean_vector(path, name):
    """Parse `def <name> : ... := ![...]` (nested `![`) into a nested Python list."""
    with open(path) as fh:
        for line in fh:
            if line.startswith("def %s :" % name):
                lit = line.split(":=", 1)[1].strip()
                return json.loads(lit.replace("![", "["))
    raise SystemExit("REFUSE: could not find def %s in %s" % (name, path))


def lookup(nested, x):
    v = nested
    for xi in x:
        v = v[xi]
    return v


def update(x, i, u):
    y = list(x)
    y[i] = u
    return tuple(y)


def corner_q():
    return [[Fr(1), Fr(0)] for _ in range(M)]


def joint_weight(q, c):
    w = Fr(1)
    for i in range(M):
        w *= q[i][c[i]]
    return w


def product_response(q, F):
    """resp[i][u] = sum_c jointWeight q c * F(update c i u)."""
    weights = {c: joint_weight(q, c) for c in CUBE}
    return [[sum(weights[c] * F[update(c, i, u)] for c in CUBE if weights[c] != 0)
             for u in (0, 1)] for i in range(M)]


def osc(vals):
    vals = list(vals)
    return max(vals) - min(vals)


def residual(F, resp, S, x):
    return F[x] - sum(resp[j][x[j]] for j in S)


def loss(F, resp, S):
    return osc(residual(F, resp, S, x) for x in CUBE) / 2


def mixed_difference(F, i, x, c):
    return F[x] - F[update(x, i, c[i])] - F[update(c, i, x[i])] + F[c]


def delta_box(F):
    return max(abs(mixed_difference(F, i, x, c)) for i in range(M) for x in CUBE for c in CUBE)


def subsets(k):
    return [frozenset(S) for S in itertools.combinations(range(M), k)]


def top_k_sets(score, k):
    sets = subsets(k)
    best = max(sum(score[j] for j in S) for S in sets)
    return [S for S in sets if sum(score[j] for j in S) == best]


def fmt(v):
    return str(v) if isinstance(v, Fr) else v


def sset(S):
    return sorted(S)


class Refuse(Exception):
    pass


def check(cond, msg, log):
    log.append({"check": msg, "ok": bool(cond)})
    if not cond:
        raise Refuse(msg)


def analyse_world(label, F, q, checks, extra=None):
    resp = product_response(q, F)
    score = [osc(resp[j]) for j in range(M)]
    dbox = delta_box(F)
    L = {}
    for k in range(M + 1):
        for S in subsets(k):
            L[S] = loss(F, resp, S)
    # proved-theorem self-checks on every pair
    for k in range(1, M):
        for P in top_k_sets(score, k):
            for T in subsets(k):
                dPT = len(P - T)
                check(L[P] - L[T] <= dPT * dbox,
                      "%s pair_loss_le_sdiff_card k=%d P=%s T=%s" % (label, k, sset(P), sset(T)), checks)
                surplus = sum(score[j] for j in P - T) - sum(score[j] for j in T - P)
                check(L[P] - L[T] <= dPT * dbox - surplus / 2,
                      "%s pair_loss_le_sdiff_card_sub_score_surplus k=%d P=%s T=%s" % (label, k, sset(P), sset(T)),
                      checks)
    per_k = []
    for k in range(1, M):
        sets = subsets(k)
        lstar = min(L[S] for S in sets)
        opt = [S for S in sets if L[S] == lstar]
        Rmax = min(k, M - k)
        prefixes = []
        for P in top_k_sets(score, k):
            d = min(len(P - T) for T in opt)
            Fk = []
            for R in range(Rmax + 1):
                Fk.append(min(L[S] - lstar for S in sets if len(S - P) <= R))
            for R in range(Rmax):
                check(Fk[R + 1] <= Fk[R], "%s F_k monotone k=%d P=%s R=%d" % (label, k, sset(P), R), checks)
            check(Fk[Rmax] == 0, "%s F_k(min(k,m-k)) = 0 k=%d P=%s" % (label, k, sset(P)), checks)
            # the (d-R)_+ delta comparison
            cmp_ = [{"R": R, "F": fmt(Fk[R]), "F_over_delta": fmt(Fk[R] / dbox) if dbox else None,
                     "bound_(d-R)+delta": fmt(max(d - R, 0) * dbox),
                     "F_le_bound": Fk[R] <= max(d - R, 0) * dbox} for R in range(Rmax + 1)]
            Rstar = next(R for R in range(Rmax + 1) if Fk[R] == 0)
            prefixes.append({"prefix": sset(P), "d_k": d, "gap_R0": fmt(Fk[0]),
                             "F_k": [fmt(v) for v in Fk], "R_star": Rstar, "rows": cmp_})
        per_k.append({"k": k, "lstar": fmt(lstar), "optimal_sets": [sset(T) for T in opt],
                      "top_k_sets": prefixes})
    # G(R) over all rankings
    Rglob = max(min(k, M - k) for k in range(1, M))
    h = {}
    for k in range(1, M):
        sets = subsets(k)
        lstar = min(L[S] for S in sets)
        for A in sets:
            for R in range(Rglob + 1):
                h[(k, A, R)] = min(L[S] - lstar for S in sets if len(S - A) <= R)
    G = []
    for R in range(Rglob + 1):
        best = None
        arg = None
        for pi in itertools.permutations(range(M)):
            val = max(h[(k, frozenset(pi[:k]), R)] for k in range(1, M))
            if best is None or val < best:
                best, arg = val, pi
        G.append({"R": R, "G": fmt(best), "G_over_delta": fmt(best / dbox) if dbox else None,
                  "argmin_ranking_example": list(arg)})
    for R in range(Rglob):
        check(Fr(G[R + 1]["G"]) <= Fr(G[R]["G"]), "%s G monotone R=%d" % (label, R), checks)
    Rstar_G = next(r["R"] for r in G if Fr(r["G"]) == 0)
    out = {"label": label, "delta_box": fmt(dbox), "scores": [fmt(v) for v in score],
           "losses": {",".join(map(str, sset(S))) if S else "empty": fmt(L[S]) for S in L},
           "per_k": per_k, "G": G, "R_star_G": Rstar_G}
    if extra:
        out.update(extra)
    return out, resp, score, dbox, L


def family_checks(s, F, resp, score, dbox, L, checks):
    """Lean-proved numbers on Vb s (LeanD6SharpnessM6V1, LeanD6M6SharpnessBridgeV1)."""
    tag = "Vb s=%d" % s
    check(dbox == 2 * s + 2, "%s delta_box = 2s+2 (integer_family_interaction_exact)" % tag, checks)
    S0, T0 = frozenset({0, 4, 5}), frozenset({1, 2, 3})
    check(2 * (L[S0] - L[T0]) == 12 * s, "%s 2D(S,T) = 12s (twoD_eq)" % tag, checks)
    check(score == [2 * s + 1, 2 * s - 1, 2 * s - 1, 2 * s - 1, 2 * s + 1, 2 * s + 1],
          "%s spans (2s+1,2s-1,2s-1,2s-1,2s+1,2s+1) (comp_eq)" % tag, checks)
    check(top_k_sets(score, 3) == [S0], "%s unique Top-3 = {0,4,5}" % tag, checks)
    margin = min(score[i] for i in S0) - max(score[j] for j in range(M) if j not in S0)
    check(margin == 2, "%s Top-C margin = 2 (strict_topC_margin_two)" % tag, checks)
    check(Fr(2 * (L[S0] - L[T0])) / dbox == Fr(6 * s, s + 1),
          "%s 2D/delta_box = 6s/(s+1) (normalized_family_bridge)" % tag, checks)
    # residual extremes (gSelI_max ... gComD_min at the Lean extremal points)
    sel_max, sel_min = (0, 1, 1, 0, 0, 0), (1, 0, 0, 1, 1, 1)
    com_max, com_min = (0, 1, 1, 0, 0, 0), (1, 0, 0, 1, 0, 0)
    rs = [residual(F, resp, S0, x) for x in CUBE]
    rt = [residual(F, resp, T0, x) for x in CUBE]
    check(residual(F, resp, S0, sel_max) == max(rs) == 2 * s * 3 + 0, "%s gSel max = 6s (gSelI_max, gSelD_max)" % tag, checks)
    check(residual(F, resp, S0, sel_min) == min(rs) == 2 * s * (-4) - 3, "%s gSel min = -8s-3" % tag, checks)
    check(residual(F, resp, T0, com_max) == max(rt) == 2 * s * 1 + 2, "%s gCom max = 2s+2" % tag, checks)
    check(residual(F, resp, T0, com_min) == min(rt) == 0 - 1, "%s gCom min = -1" % tag, checks)
    # the one mixed difference that attains delta_box (endpoint_interaction_attained)
    xI, cI = (1, 0, 0, 0, 0, 0), (0, 0, 0, 0, 1, 0)
    check(mixed_difference(F, 0, xI, cI) == 2 * s + 2, "%s mixedDifference 0 interactionX interactionC = 2s+2" % tag, checks)


def main():
    lean_m6 = os.path.join(LEAN_DIR, "LeanD6SharpnessM6V1.lean")
    Ib = parse_lean_vector(lean_m6, "Ib")
    Db = parse_lean_vector(lean_m6, "Db")
    s_values = [int(a) for a in sys.argv[1:]] or [1, 2, 6, 20, 100]
    checks = []
    results = []
    # parse check: Lean-proved point values of Ib/Db (respI_zero, comp_eq at u = 1)
    check(all(lookup(Ib, (0,) * 6) == 0 for _ in [0]) and lookup(Db, (0,) * 6) == 0,
          "Ib, Db vanish at the corner (respI_zero, respD_zero)", checks)
    slope = [lookup(Ib, update((0,) * 6, i, 1)) for i in range(M)]
    const = [lookup(Db, update((0,) * 6, i, 1)) for i in range(M)]
    check(slope == [1, 1, 1, -1, 1, 1] and const == [1, -1, -1, 1, 1, 1],
          "respI i 1 = oscSlope, respD i 1 = oscConst (comp_eq)", checks)
    q = corner_q()
    try:
        for s in s_values:
            print("world Vb s=%d ..." % s, flush=True)
            F = {x: Fr(2 * s * lookup(Ib, x) + lookup(Db, x)) for x in CUBE}
            out, resp, score, dbox, L = analyse_world("Vb s=%d" % s, F, q, checks, {"family": "Vb", "s": s})
            family_checks(s, F, resp, score, dbox, L, checks)
            results.append(out)
            k3 = out["per_k"][2]["top_k_sets"][0]
            print("  delta=%s  k=3: lstar=%s d=%s F_3=%s  G=%s" % (
                out["delta_box"], out["per_k"][2]["lstar"], k3["d_k"], k3["F_k"],
                [g["G"] for g in out["G"]]), flush=True)
    except Refuse as e:
        print("REFUSE: self-check failed: %s" % e, flush=True)
        sys.exit(2)
    producer = os.path.abspath(__file__)
    doc = {
        "artifact": "P1 D6 m=6 revision frontier, exact",
        "producer": os.path.relpath(producer, REPO),
        "producer_sha256": sha256_file(producer),
        "argv": sys.argv[1:],
        "lean_sources_sha256": {f: sha256_file(os.path.join(LEAN_DIR, f)) for f in [
            "LeanD6SharpnessM6V1.lean", "LeanD6M6SharpnessBridgeV1.lean", "LeanD6BinaryBridgeV1.lean",
            "LeanD6SmallSymmetricDifference.lean", "LeanD6MarginSensitiveExchangeV1.lean",
            "LeanD6SharpMarginThresholdV1.lean", "LeanProductMixedDifferenceV4.lean",
            "LeanD6H3Exchange.lean", "LeanSupportGeometryV4.lean", "LeanProductSurrogateV4.lean"]},
        "evidence_class": "EXACT (rational arithmetic, finite enumeration); not a proof",
        "model": __doc__,
        "self_checks": {"n": len(checks), "all_ok": all(c["ok"] for c in checks),
                        "family_and_parse_checks": [c for c in checks if "pair_loss" not in c["check"]
                                                    and "monotone" not in c["check"]]},
        "worlds": results,
    }
    out_path = os.environ.get("P1_OUT", os.path.join(OUT_DIR, "d6_frontier_exact.json"))
    if os.path.exists(out_path):
        print("REFUSE: %s exists; never overwrite (set P1_OUT to a new path)" % out_path, flush=True)
        sys.exit(3)
    with open(out_path, "w") as fh:
        json.dump(doc, fh, indent=1)
    print("wrote %s (%d self-checks, all ok)" % (out_path, len(checks)), flush=True)


if __name__ == "__main__":
    main()
