#!/usr/bin/env python3
"""The geometry rate, measured instead of assumed.

`LeanUnifiedSupportExchangeV1` leaves `kappa` -- the rate at which the support geometry
term can grow under an exchange -- as an INPUT.  `LeanUnifiedGeometryBoundV1` removes that
input by bounding it with two measurements per coordinate:

    s_j = oscillation of coordinate j's response on the FULL domain,
    c_j = oscillation of coordinate j's response on the SUPPORT,

giving

    D_K(S) - D_K(T)  <=  (1/2) sum_{j in T \\ S} (s_j + c_j).

This script checks that bound, and measures how much it gives away.  Three things are
verified, all in exact rational arithmetic:

  1. THE DECOMPOSITION.  D_K(T) = (1/2)[ sum_{j not in T} (s_j - c_j) + gamma_K(T^c) ]
     where gamma_K(A) = sum_{j in A} c_j - osc_K(sum_{j in A} Q_j) is the support
     coupling defect.  Both pieces are directly measurable.

  2. THE BOUND HOLDS, on the witness and on random product families with random supports.

  3. HOW LOOSE IT IS.  The exact single-swap constant is also computed -- at cost O(m^2)
     support evaluations rather than O(m) -- so the price of the cheap bound is reported
     rather than hidden.

A soundness check closes the loop: whenever the computable threshold fires, the Top-C set
really is optimal on the support.  That is the statement `computable_threshold` proves, and
it is checked here against a brute-force search over competitors.
"""

import json
import random
import sys
from fractions import Fraction as Fr
from itertools import combinations, product

CHECKS = []


def check(name, ok, detail=""):
    CHECKS.append({"name": name, "ok": bool(ok), "detail": detail})
    print(f"  [{'OK  ' if ok else 'FAIL'}] {name}" + (f"   {detail}" if detail else ""))
    return ok


# --------------------------------------------------------------------------
# The objects, transcribed from the Lean definitions.
# --------------------------------------------------------------------------

def osc_on(vals):
    return max(vals) - min(vals)


def span_full(Q, j, X):
    """s_j = oscillation of component j over the full domain."""
    return osc_on([Q[j][x[j]] for x in X])


def span_on(Q, j, K):
    """c_j = oscillation of component j over the support."""
    return osc_on([Q[j][x[j]] for x in K])


def sum_over(Q, E, x):
    return sum(Q[j][x[j]] for j in E)


def loss_on(Q, T, m, D):
    """Half the oscillation of the residual (= sum of omitted components) on D."""
    comp = [j for j in range(m) if j not in T]
    return osc_on([sum_over(Q, comp, x) for x in D]) / 2


def geom_gap(Q, T, m, K, X):
    return loss_on(Q, T, m, X) - loss_on(Q, T, m, K)


def coupling(Q, A, K):
    """gamma_K(A): how much the coordinates fail to co-extremise on the support."""
    return sum(span_on(Q, j, K) for j in A) - osc_on([sum_over(Q, A, x) for x in K])


def kappa_cheap(Q, T, K, X):
    """The O(m) bound: max over the retained coordinates of (s_j + c_j)/2."""
    return max((span_full(Q, j, X) + span_on(Q, j, K)) / 2 for j in T)


def kappa_exact_single_swap(Q, T, m, K, X):
    """The O(m^2) constant: the largest actual rate over SINGLE swaps.

    WARNING, and the reason this is kept alongside `kappa_exact_all`: this is NOT a
    valid `kappa` for the threshold when the budget exceeds one, because a competitor
    may differ from `T` in several coordinates and the theorem quantifies over every
    competitor.  Using it as `kappa` is unsound, and the run below demonstrates that."""
    best = Fr(0)
    for out_j in T:
        for in_j in range(m):
            if in_j in T:
                continue
            S = frozenset(T - {out_j}) | {in_j}
            d = geom_gap(Q, S, m, K, X) - geom_gap(Q, T, m, K, X)
            best = max(best, d)
    return best


def kappa_exact_all(Q, T, m, k, K, X):
    """The valid exact constant: the largest rate over EVERY competitor of size k,
    normalised by the size of the exchange."""
    best = Fr(0)
    base = geom_gap(Q, T, m, K, X)
    for t in combinations(range(m), k):
        S = frozenset(t)
        if S == T:
            continue
        a = len(T - S)
        if a == 0:
            continue
        best = max(best, (geom_gap(Q, S, m, K, X) - base) / a)
    return best


def cube(m):
    return list(product((0, 1), repeat=m))


def random_family(m, rng):
    """A random additive family with a corner reference: Q[j][u] = w_j * u."""
    return [{0: Fr(0), 1: Fr(rng.randint(-6, 6), rng.choice([1, 2]))} for _ in range(m)]


# --------------------------------------------------------------------------

def main():
    print("=" * 76)
    print("The geometry rate kappa, measured from support spans instead of assumed")
    print("=" * 76)

    # ---- the witness of LeanUnifiedSupportExchangeV1
    print("\n  the witness  F = 3x1 - 2x2 - 2x3,  K = {000, 111}")
    print("  " + "-" * 68)
    m = 3
    X = cube(m)
    K = [(0, 0, 0), (1, 1, 1)]
    Qw = [{0: Fr(0), 1: Fr(3)}, {0: Fr(0), 1: Fr(-2)}, {0: Fr(0), 1: Fr(-2)}]
    s = [span_full(Qw, j, X) for j in range(m)]
    c = [span_on(Qw, j, K) for j in range(m)]
    print(f"      full spans   s = {[str(v) for v in s]}")
    print(f"      support spans c = {[str(v) for v in c]}")
    T = frozenset({0})
    Sc = frozenset({1})
    true_rate = geom_gap(Qw, Sc, m, K, X) - geom_gap(Qw, T, m, K, X)
    kc = kappa_cheap(Qw, T, K, X)
    ke = kappa_exact_single_swap(Qw, T, m, K, X)
    print(f"      true rate on the exchange  T={{1}} -> S={{2}}:  {true_rate}")
    print(f"      exact single-swap kappa (O(m^2)):          {ke}")
    print(f"      cheap measured bound     (O(m)):           {kc}")
    check("the cheap bound dominates the true rate at the witness", kc >= true_rate,
          f"{kc} >= {true_rate}")
    check("the exact single-swap constant is 2, as the Lean witness states", ke == Fr(2))
    check("the cheap bound is 3, so it gives away a factor 3/2 here", kc == Fr(3))

    # ---- the decomposition, exactly
    dec_ok = True
    for T2 in [frozenset(t) for r in range(m + 1) for t in combinations(range(m), r)]:
        comp = [j for j in range(m) if j not in T2]
        lhs = geom_gap(Qw, T2, m, K, X)
        rhs = (sum(s[j] - c[j] for j in comp) + coupling(Qw, comp, K)) / 2
        if lhs != rhs:
            dec_ok = False
    check("D_K(T) = [sum (s_j - c_j) + gamma_K(T^c)]/2, on every subset", dec_ok)

    # ---- the bound on random families and random supports
    print("\n  random additive families with random supports")
    print("  " + "-" * 68)
    rng = random.Random(20260919)
    bound_ok, tight_ok = True, True
    ratios, tested = [], 0
    for trial in range(400):
        mm = rng.choice([3, 4, 5])
        XX = cube(mm)
        ksz = rng.randint(2, min(6, len(XX)))
        KK = rng.sample(XX, ksz)
        Q = random_family(mm, rng)
        k = rng.randint(1, mm - 1)
        # Top-C by full span
        order = sorted(range(mm), key=lambda j: (-span_full(Q, j, XX), j))
        TT = frozenset(order[:k])
        kc2 = kappa_cheap(Q, TT, KK, XX)
        for SS in [frozenset(t) for t in combinations(range(mm), k)]:
            if SS == TT:
                continue
            a = len(TT - SS)
            rate = geom_gap(Q, SS, mm, KK, XX) - geom_gap(Q, TT, mm, KK, XX)
            bound = sum(span_full(Q, j, XX) + span_on(Q, j, KK) for j in (TT - SS)) / 2
            tested += 1
            if rate > bound:
                bound_ok = False
            if rate > kc2 * a:
                tight_ok = False
            if bound > 0:
                ratios.append(float(rate / bound))
    check("the summed bound holds on every random exchange", bound_ok,
          f"{tested} exchanges")
    check("the kappa form holds too", tight_ok)
    avg = sum(ratios) / len(ratios) if ratios else 0.0
    print(f"      mean  (true rate)/(bound)  = {avg:.3f}   "
          f"max = {max(ratios):.3f}" if ratios else "")
    check("the bound is not vacuous: some exchange comes close to it",
          max(ratios) > 0.40 if ratios else False,
          f"closest approach {max(ratios):.3f}" if ratios else "")

    # ---- when can the threshold fire at all?
    print("\n  does the threshold fire?  by support size, cheap bound vs exact constant")
    print("  " + "-" * 68)
    rows, sound_cheap, sound_exact, sound_swap = [], True, True, True
    for mm in [3, 4]:
        XX = cube(mm)
        for frac in [0.25, 0.5, 0.75, 1.0]:
            ksz = max(2, int(round(frac * len(XX))))
            fc = fe = fs = n = 0
            for trial in range(150):
                KK = rng.sample(XX, min(ksz, len(XX)))
                Q = random_family(mm, rng)
                k = rng.randint(1, mm - 1)
                sp = [span_full(Q, j, XX) for j in range(mm)]
                if min(sp) == 0:
                    continue
                order = sorted(range(mm), key=lambda j: (-sp[j], j))
                TT = frozenset(order[:k])
                uns = [sp[j] for j in range(mm) if j not in TT]
                rho = min(sp[j] for j in TT) - max(uns)
                delta = Fr(0)                  # additive family: zero interaction
                n += 1
                best = min(loss_on(Q, frozenset(t), mm, KK)
                           for t in combinations(range(mm), k))
                optimal = loss_on(Q, TT, mm, KK) <= best
                if 2 * delta + 2 * kappa_cheap(Q, TT, KK, XX) <= rho:
                    fc += 1
                    if not optimal:
                        sound_cheap = False
                if 2 * delta + 2 * kappa_exact_all(Q, TT, mm, k, KK, XX) <= rho:
                    fe += 1
                    if not optimal:
                        sound_exact = False
                if 2 * delta + 2 * kappa_exact_single_swap(Q, TT, mm, KK, XX) <= rho:
                    fs += 1
                    if not optimal:
                        sound_swap = False
            rows.append({"m": mm, "support_fraction": frac, "instances": n,
                         "fired_cheap": fc, "fired_exact": fe, "fired_singleswap": fs})
            print(f"      m={mm}  |K|/|X|={frac:4.2f}:  fired  cheap {fc:3d}/{n:3d}"
                  f"   exact {fe:3d}/{n:3d}")

    check("soundness holds whenever the cheap threshold fires", sound_cheap)
    check("soundness holds whenever the VALID exact threshold fires", sound_exact)
    check("the single-swap constant is NOT a valid kappa, as its docstring warns",
          not sound_swap,
          "it certifies instances where Top-C is not optimal on the support")
    tot_c = sum(r["fired_cheap"] for r in rows)
    tot_e = sum(r["fired_exact"] for r in rows)
    check("the O(m) bound is too weak to fire at any support size", tot_c == 0,
          f"{tot_c} firings out of {sum(r['instances'] for r in rows)}")
    check("the exact O(m^2) constant DOES fire, and only when the support is large",
          tot_e > 0 and rows[0]["fired_exact"] <= rows[-1]["fired_exact"],
          f"{tot_e} firings, concentrated at large supports")

    nfail = sum(1 for c_ in CHECKS if not c_["ok"])
    print("\n" + "=" * 76)
    print(f"{len(CHECKS)-nfail}/{len(CHECKS)} self-checks passed")
    print("=" * 76)
    out = {
           "source_sha256": __import__("hashlib").sha256(
               __import__("pathlib").Path("scripts/EXP_unified_geometry_kappa.py").read_bytes()).hexdigest(),"witness": {"s": [str(v) for v in s], "c": [str(v) for v in c],
                       "true_rate": str(true_rate), "kappa_exact": str(ke),
                       "kappa_cheap": str(kc)},
           "exchanges_tested": tested,
           "mean_tightness": avg,
           "threshold_by_support_size": rows,
           "checks": CHECKS, "all_passed": nfail == 0}
    with open("research/unified_20260919/geometry_kappa.json", "w") as f:
        json.dump(out, f, indent=2)
    if nfail:
        print("REFUSING to report: a self-check failed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
