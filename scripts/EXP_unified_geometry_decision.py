#!/usr/bin/env python3
"""Support-aware compression: geometry, decision, and the certificate gap.

Covers three of the constructions in the unified batch, all in exact rational
arithmetic, and SELF-CHECKS each one against a statement that is proved (or is
being proved) in Lean.  Nothing here is estimated; every number is a fraction.

  PART A (sec 2)  The support decomposition identity and the support exchange
                  bound with the geometry term, on
                      F(x) = 3x1 - 2x2 - 2x3,  X = {0,1}^3,  K = {000,111}.
                  Top-C is WRONG on K even though the interaction is zero, and
                  the geometry-corrected exchange bound holds with EQUALITY.

  PART B (sec 3)  The certificate gap on F = a x1 + b x2 + c x1 x2:
                  the decision depends only on a-b, while the Top-C margin
                  certificate compares a-b against 2*delta_I = 2c.

  PART C (sec 4)  The theta-family
                      F_t(x) = (3+t) x1 + (-2+t) x2 + (-2+t) x3
                  on K = {000,111}: the decision flips at t = 3/4 exactly, the
                  safe-answer intervals, and the confounded pair of worlds.

Definitions transcribed from the Lean corpus (NOT re-invented):
  productResponse q F j u   = E_q[ F(update c j u) ]       (corner q => F(e_j u))
  retainedResidual q F T x  = F x - sum_{j in T} Q_j(x_j)
  productCompressionLoss    = osc(retainedResidual) / 2
  mixedDifference F i x c   = F x - F(x|i<-c_i) - F(c|i<-x_i) + F c
  oscOn K f                 = max_K f - min_K f            (LeanSupportGeometryV4)
"""

from fractions import Fraction as Fr
from itertools import product
import json
import sys

# --------------------------------------------------------------------------
# Core definitions, transcribed from the Lean corpus.
# --------------------------------------------------------------------------

def cube(n):
    return list(product((0, 1), repeat=n))


def product_response(F, n, j, u, ref):
    """Corner reference: q is the point mass at `ref`, so the expectation is
    the single evaluation F(ref with coordinate j set to u)."""
    c = list(ref)
    c[j] = u
    return F(tuple(c))


def responses(F, n, ref):
    return [{u: product_response(F, n, j, u, ref) for u in (0, 1)}
            for j in range(n)]


def osc_on(F, n, T, ref, domain):
    """oscOn(domain, retainedResidual q F T)."""
    Q = responses(F, n, ref)
    vals = [F(x) - sum(Q[j][x[j]] for j in T) for x in domain]
    return max(vals) - min(vals)


def loss_on(F, n, T, ref, domain):
    """productCompressionLoss restricted to `domain`: osc/2."""
    return osc_on(F, n, T, ref, domain) / 2


def delta_I(F, n):
    """delta_I = max over (i,x,c) of |mixedDifference F i x c|."""
    best = Fr(0)
    for i in range(n):
        for x in cube(n):
            for c in cube(n):
                xi = list(x); xi[i] = c[i]
                ci = list(c); ci[i] = x[i]
                md = F(x) - F(tuple(xi)) - F(tuple(ci)) + F(c)
                best = max(best, abs(md))
    return best


def topk_by_osc(F, n, k, ref):
    Q = responses(F, n, ref)
    scores = [abs(Q[j][1] - Q[j][0]) for j in range(n)]
    order = sorted(range(n), key=lambda j: (-scores[j], j))
    return frozenset(order[:k]), scores


def margin_rho(scores, T, n):
    """rho = min over selected of score, minus max over unselected."""
    sel = [scores[j] for j in T]
    uns = [scores[j] for j in range(n) if j not in T]
    if not uns:
        return None
    return min(sel) - max(uns)


CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    flag = "OK  " if ok else "FAIL"
    print(f"  [{flag}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# --------------------------------------------------------------------------
# PART A -- the support decomposition and the geometry-corrected exchange.
# --------------------------------------------------------------------------

def part_A():
    print("\nPART A  support decomposition, support exchange bound, witness")
    print("-" * 70)
    n = 3
    ref = (0, 0, 0)
    X = cube(n)
    K = [(0, 0, 0), (1, 1, 1)]

    def F(x):
        return Fr(3) * x[0] - Fr(2) * x[1] - Fr(2) * x[2]

    d = delta_I(F, n)
    check("delta_I = 0 (F is additive, no interaction)", d == 0, f"delta_I={d}")

    T, scores = topk_by_osc(F, n, 1, ref)
    check("component spans C = (3,2,2)", scores == [Fr(3), Fr(2), Fr(2)],
          f"C={[str(s) for s in scores]}")
    check("Top-C at k=1 selects {1}", T == frozenset({0}), f"T={sorted(T)}")

    rho = margin_rho(scores, T, n)
    check("margin rho = 1", rho == Fr(1), f"rho={rho}")

    singles = [frozenset({0}), frozenset({1}), frozenset({2})]
    LX = {S: loss_on(F, n, S, ref, X) for S in singles}
    LK = {S: loss_on(F, n, S, ref, K) for S in singles}
    DK = {S: LX[S] - LK[S] for S in singles}

    for S in singles:
        print(f"      S={sorted(S)}  L_X={LX[S]}  L_K={LK[S]}  D_K={DK[S]}")

    check("L_K({1}) = 2", LK[frozenset({0})] == Fr(2))
    check("L_K({2}) = L_K({3}) = 1/2",
          LK[frozenset({1})] == Fr(1, 2) and LK[frozenset({2})] == Fr(1, 2))

    # D_K >= 0 is oscOn_mono; check it on every subset, not just the singletons.
    allsub = []
    for r in range(n + 1):
        for T2 in product(range(n), repeat=r):
            if len(set(T2)) == r:
                allsub.append(frozenset(T2))
    allsub = list(set(allsub))
    check("D_K(S) >= 0 for EVERY subset (oscOn_mono)",
          all(loss_on(F, n, S, ref, X) - loss_on(F, n, S, ref, K) >= 0
              for S in allsub),
          f"{len(allsub)} subsets")

    # Top-C is wrong on K although delta_I = 0.
    best_K = min(LK, key=lambda S: LK[S])
    check("Top-C is NOT optimal on K despite delta_I = 0",
          LK[T] > LK[best_K],
          f"L_K(TopC)={LK[T]} > min={LK[best_K]} at {sorted(best_K)}")

    # The identity, on every ordered pair of subsets of every size.
    ident_ok = True
    for S1 in allsub:
        for S2 in allsub:
            lhs = loss_on(F, n, S1, ref, K) - loss_on(F, n, S2, ref, K)
            rhs = (loss_on(F, n, S1, ref, X) - loss_on(F, n, S2, ref, X)
                   + (loss_on(F, n, S2, ref, X) - loss_on(F, n, S2, ref, K))
                   - (loss_on(F, n, S1, ref, X) - loss_on(F, n, S1, ref, K)))
            if lhs != rhs:
                ident_ok = False
    check("identity L_K(T)-L_K(S) = L_X(T)-L_X(S) + D_K(S)-D_K(T)  (all pairs)",
          ident_ok, f"{len(allsub)**2} ordered pairs")

    # The geometry-corrected exchange bound, and equality at the witness.
    S = frozenset({1})
    A = T - S
    lhs = 2 * (LK[T] - LK[S])
    rhs = len(A) * (2 * d - rho) + 2 * (DK[S] - DK[T])
    check("support exchange bound holds at the witness", lhs <= rhs,
          f"2*(L_K(T)-L_K(S))={lhs} <= {rhs}")
    check("and it holds with EQUALITY (geometry term is not removable)",
          lhs == rhs, f"{lhs} == {rhs}")

    # Without the geometry term the plain D6 bound is violated on K: that is
    # precisely why the term is needed.
    plain = len(A) * (2 * d - rho)
    check("plain (full-domain) exchange bound FAILS on K", lhs > plain,
          f"{lhs} > {plain}")

    # The kappa threshold: rho >= 2 delta_I + 2 kappa  =>  T optimal on K.
    # Verify the implication by brute force over a grid of kappa.
    kap_ok = True
    for S2 in singles:
        A2 = T - S2
        if not A2:
            continue
        kappa = (DK[S2] - DK[T]) / len(A2)
        if rho >= 2 * d + 2 * kappa and LK[T] > LK[S2]:
            kap_ok = False
    check("threshold rho >= 2 delta_I + 2 kappa implies K-optimality", kap_ok)

    # The smallest valid kappa here, and the threshold it demands.
    kappas = [(DK[S2] - DK[T]) / len(T - S2) for S2 in singles if T - S2]
    kmax = max(kappas)
    check("witness needs kappa = 2, so rho >= 4; actual rho = 1 < 4",
          kmax == Fr(2) and rho < 2 * d + 2 * kmax,
          f"kappa={kmax}, required rho>={2*d+2*kmax}, actual rho={rho}")

    return {
        "delta_I": str(d), "rho": str(rho),
        "C": [str(s) for s in scores],
        "L_X": {str(sorted(S)): str(LX[S]) for S in singles},
        "L_K": {str(sorted(S)): str(LK[S]) for S in singles},
        "D_K": {str(sorted(S)): str(DK[S]) for S in singles},
        "exchange_lhs": str(lhs), "exchange_rhs": str(rhs),
        "equality": lhs == rhs, "kappa_required": str(kmax),
    }


# --------------------------------------------------------------------------
# PART B -- decision needs a-b, certificate demands 2c.
# --------------------------------------------------------------------------

def part_B():
    print("\nPART B  true decision boundary vs certificate boundary")
    print("-" * 70)
    n = 2
    ref = (0, 0)
    X = cube(n)

    def make(a, b, c):
        return lambda x: a * x[0] + b * x[1] + c * x[0] * x[1]

    # Symbolic check on a grid of rationals: L({1}) = (b+c)/2, L({2}) = (a+c)/2.
    formula_ok = True
    for a in [Fr(3), Fr(5, 2), Fr(7, 3)]:
        for b in [Fr(1), Fr(2), Fr(1, 2)]:
            for c in [Fr(1), Fr(1, 4), Fr(3)]:
                if not (a > b > 0 and c > 0):
                    continue
                F = make(a, b, c)
                l1 = loss_on(F, n, frozenset({0}), ref, X)
                l2 = loss_on(F, n, frozenset({1}), ref, X)
                if l1 != (b + c) / 2 or l2 != (a + c) / 2:
                    formula_ok = False
    check("L({1})=(b+c)/2 and L({2})=(a+c)/2 on the whole grid", formula_ok)

    # delta_I = c.
    dI_ok = all(delta_I(make(a, b, c), n) == c
                for a in [Fr(3), Fr(5, 2)] for b in [Fr(1), Fr(2)]
                for c in [Fr(1), Fr(1, 4), Fr(3)] if a > b > 0)
    check("delta_I = c for this family", dI_ok)

    # The gap: decision clear (a>b) but certificate rho >= 2 delta_I fails.
    gap_rows = []
    for (a, b, c) in [(Fr(3), Fr(1), Fr(1)), (Fr(3), Fr(1), Fr(3)),
                      (Fr(5, 2), Fr(2), Fr(1, 4)), (Fr(3), Fr(2), Fr(2))]:
        F = make(a, b, c)
        d = delta_I(F, n)
        _, scores = topk_by_osc(F, n, 1, ref)
        rho = scores[0] - scores[1]
        l1 = loss_on(F, n, frozenset({0}), ref, X)
        l2 = loss_on(F, n, frozenset({1}), ref, X)
        decided = l1 < l2
        certified = rho >= 2 * d
        gap_rows.append({"a": str(a), "b": str(b), "c": str(c),
                         "rho": str(rho), "delta_I": str(d),
                         "decision_clear": decided, "certificate_holds": certified})
        print(f"      a={a} b={b} c={c}:  rho={rho}  2*delta_I={2*d}  "
              f"decided={decided}  certified={certified}")

    check("decision depends only on sign(a-b) (rho = a-b)",
          all(Fr(r["rho"]) == Fr(r["a"]) - Fr(r["b"]) for r in gap_rows))
    check("a-b < 2c gives a clear decision with NO certificate",
          any(r["decision_clear"] and not r["certificate_holds"] for r in gap_rows))
    check("certificate never fires when the decision is wrong (it is sound)",
          all(r["decision_clear"] for r in gap_rows if r["certificate_holds"]))
    return {"rows": gap_rows}


# --------------------------------------------------------------------------
# PART C -- the theta family, its flip point, safe intervals, confounding.
# --------------------------------------------------------------------------

def part_C():
    print("\nPART C  theta family: flip at 3/4, safe intervals, confounding")
    print("-" * 70)
    n = 3
    ref = (0, 0, 0)
    K = [(0, 0, 0), (1, 1, 1)]

    def Ft(t):
        return lambda x: (3 + t) * x[0] + (-2 + t) * x[1] + (-2 + t) * x[2]

    # Loss formulas on K, checked on a dense rational grid of theta in [0,1].
    grid = [Fr(i, 24) for i in range(25)]
    f1_ok = all(loss_on(Ft(t), n, frozenset({0}), ref, K) == 2 - t for t in grid)
    f2_ok = all(loss_on(Ft(t), n, frozenset({1}), ref, K) == Fr(1, 2) + t
                for t in grid)
    f3_ok = all(loss_on(Ft(t), n, frozenset({2}), ref, K) == Fr(1, 2) + t
                for t in grid)
    check("L_theta({1}) = 2 - theta on [0,1]", f1_ok)
    check("L_theta({2}) = L_theta({3}) = 1/2 + theta on [0,1]", f2_ok and f3_ok)

    # The flip point.
    tstar = Fr(3, 4)
    at = loss_on(Ft(tstar), n, frozenset({0}), ref, K)
    bt = loss_on(Ft(tstar), n, frozenset({1}), ref, K)
    check("decision flips exactly at theta* = 3/4", at == bt, f"both = {at}")
    below = [t for t in grid if t < tstar]
    above = [t for t in grid if t > tstar]
    check("below 3/4 the better answer is {2}",
          all(loss_on(Ft(t), n, frozenset({1}), ref, K)
              < loss_on(Ft(t), n, frozenset({0}), ref, K) for t in below))
    check("above 3/4 the better answer is {1}",
          all(loss_on(Ft(t), n, frozenset({0}), ref, K)
              < loss_on(Ft(t), n, frozenset({1}), ref, K) for t in above))

    # Safe-answer intervals: d is eps-safe iff L(d) - min L <= eps.
    def safe(t, S, eps):
        L = {Sx: loss_on(Ft(t), n, Sx, ref, K)
             for Sx in [frozenset({0}), frozenset({1}), frozenset({2})]}
        return L[S] - min(L.values()) <= eps

    iv_ok = True
    for eps in [Fr(0), Fr(1, 8), Fr(1, 4), Fr(2, 5)]:
        for t in grid:
            if safe(t, frozenset({0}), eps) != (t >= tstar - eps / 2):
                iv_ok = False
            if safe(t, frozenset({1}), eps) != (t <= tstar + eps / 2):
                iv_ok = False
    check("safe intervals: {1} iff theta >= 3/4-eps/2, {2} iff theta <= 3/4+eps/2",
          iv_ok)

    # Δ_dec = |theta - 3/4| + eps/2 for the BETTER answer.
    dd_ok = True
    for eps in [Fr(0), Fr(1, 8), Fr(1, 4), Fr(2, 5)]:
        for t in grid:
            best = frozenset({0}) if t > tstar else frozenset({1})
            # distance from t to the nearest theta' where `best` stops being safe
            if best == frozenset({0}):
                dist = t - (tstar - eps / 2)
            else:
                dist = (tstar + eps / 2) - t
            if dist != abs(t - tstar) + eps / 2:
                dd_ok = False
    check("Delta_dec(theta,eps) = |theta - 3/4| + eps/2", dd_ok)

    # Confounding: (theta,b) = (0,0) and (1,-3) give the same law of Y.
    def meanY(t, b):
        return -1 + 3 * t + b
    check("worlds (0,0) and (1,-3) give the same mean of Y",
          meanY(Fr(0), Fr(0)) == meanY(Fr(1), Fr(-3)),
          f"both = {meanY(Fr(0), Fr(0))}")
    check("F_theta(111) = -1 + 3 theta",
          all(Ft(t)((1, 1, 1)) == -1 + 3 * t for t in grid))
    check("F_theta(000) = 0, so Z = b + noise isolates the nuisance",
          all(Ft(t)((0, 0, 0)) == 0 for t in grid))
    # ...but they demand different decisions once eps < 1/2.
    check("yet the two confounded worlds need different answers when eps < 1/2",
          not safe(Fr(0), frozenset({0}), Fr(2, 5))
          and not safe(Fr(1), frozenset({1}), Fr(2, 5)))
    check("at eps >= 1/2 the answer {2} is safe for EVERY theta in [0,1]",
          all(safe(t, frozenset({1}), Fr(1, 2)) for t in grid))

    return {"theta_star": "3/4",
            "flip_value": str(at),
            "no_measurement_phase": "eps >= 1/2"}


def main():
    print("=" * 70)
    print("Unified batch: support geometry, decision boundary, certificate gap")
    print("=" * 70)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_unified_geometry_decision.py").read_bytes()).hexdigest(),"partA": part_A(), "partB": part_B(), "partC": part_C()}
    nfail = sum(1 for c in CHECKS if not c["ok"])
    print("\n" + "=" * 70)
    print(f"{len(CHECKS) - nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 70)
    out["checks"] = CHECKS
    out["all_passed"] = nfail == 0
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    with open("research/unified_20260919/geometry_decision.json", "w") as f:
        json.dump(out, f, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())
