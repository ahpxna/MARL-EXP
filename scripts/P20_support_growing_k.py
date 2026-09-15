#!/usr/bin/env python3
"""P20 -- Support: the growing-K law with the TOTAL sampling mass held fixed.

Audit item S2: the fixed-K constants `k0 = min_i 1/(a_i+1)` and `B = prod b_i` depend
on K, so no uniform growing-K statement follows from them.  The clean extension the
audit proposes is a_i = b_i = 1 and p_i = P/K with P fixed: every class has one safe
and one unsafe tip, and only unsafe tips are ever observed.

EXACT laws in this model (no simulation, no independence assumed between classes --
they come from one categorical stream):

  decide   R_dec(N) = (1/2)(1-P)^N,                       independent of K
  recover  R_rec(N) = 1 - sum_k C(K,k) (-1/2)^k (1-kP/K)^N
           and       Pr(U>0) = 1 - sum_k C(K,k) (-1)^k (1-kP/K)^N
           with      (1/2) Pr(U>0) <= R_rec <= Pr(U>0).

The recovery identity is inclusion-exclusion on (1/2)^U = prod_i (1 - X_i/2), where
X_i indicates that class i's unsafe tip is still unseen; it does NOT assume the X_i
independent.

This is the quantitative separation: deciding safely is governed by the TOTAL unsafe
mass P and is flat in K; recovering the world is governed by the per-class mass P/K and
grows like (K/P)(log K + log(1/eps)).

Lean counterparts: `LeanSupportSamplingLawV1` (the product law and the tuple identity),
`LeanSupportDecideRecoverV1` (binary_decide_value, growing_K_recover, the two pointwise
recovery bounds).
"""
import json, os
from fractions import Fraction as F
from math import comb, log

OUT = "research/worker_P20_support_20260915"


def r_dec(P, N):
    return F(1, 2) * (1 - P) ** N


def e_half_pow_U(K, P, N):
    """E[(1/2)^U] = sum_k C(K,k) (-1/2)^k (1-kP/K)^N, exact."""
    tot = F(0)
    for k in range(K + 1):
        tot += comb(K, k) * F((-1) ** k, 2 ** k) * (1 - k * P / K) ** N
    return tot


def pr_U_pos(K, P, N):
    tot = F(0)
    for k in range(K + 1):
        tot += comb(K, k) * F((-1) ** k) * (1 - k * P / K) ** N
    return 1 - tot


def min_N(target, f, hi=1 << 22):
    """Smallest N with f(N) <= target, by doubling then bisection."""
    lo, cur = 0, 1
    while cur < hi and f(cur) > target:
        lo, cur = cur, cur * 2
    if f(cur) > target:
        return None
    a, b = lo, cur
    while a < b:
        mid = (a + b) // 2
        if f(mid) <= target:
            b = mid
        else:
            a = mid + 1
    return a


def main():
    os.makedirs(OUT, exist_ok=True)
    P = F(1, 2)
    rows = []
    for K in [1, 2, 4, 8, 16, 32]:
        for eps in [F(1, 10), F(1, 100)]:
            # sanity: the exact decide law and the exact recovery identity
            for N in [0, 1, 3, 7]:
                assert r_dec(P, N) == F(1, 2) * (1 - P) ** N
                eh = e_half_pow_U(K, P, N)
                rr = 1 - eh
                pu = pr_U_pos(K, P, N)
                assert F(1, 2) * pu <= rr <= pu, (K, N, rr, pu)
            Nd = min_N(eps, lambda N: r_dec(P, N))
            Nr = min_N(eps, lambda N: 1 - e_half_pow_U(K, P, N))
            coupon = (K / float(P)) * (log(max(K, 2)) + log(1 / float(eps)))
            decide_scale = log(1 / float(2 * eps)) / (-log(1 - float(P)))
            rows.append({
                "K": K, "P": str(P), "eps": str(eps),
                "N_decide_exact": Nd,
                "N_recover_exact": Nr,
                "ratio_recover_over_decide": round(Nr / Nd, 4) if Nd else None,
                "decide_scale_log(1/2eps)/(-log(1-P))": round(decide_scale, 4),
                "coupon_scale_(K/P)(logK+log1/eps)": round(coupon, 4),
                "R_dec_at_N_decide": str(r_dec(P, Nd)),
                "R_rec_at_N_decide": str(1 - e_half_pow_U(K, P, Nd)),
            })
            print(f"K={K:3d} eps={float(eps):.2f}  N_dec={Nd:5d}  N_rec={Nr:7d}  "
                  f"ratio={Nr/Nd:8.3f}  coupon~{coupon:8.1f}")

    # the decide count really is flat in K
    dec = {(r["eps"], r["N_decide_exact"]) for r in rows}
    per_eps = {}
    for e, n in dec:
        per_eps.setdefault(e, set()).add(n)
    flat = all(len(v) == 1 for v in per_eps.values())
    out = {
        "script": "P20_support_growing_k.py",
        "model": "a_i = b_i = 1, p_i = P/K, total unsafe mass P fixed; only unsafe tips observed",
        "exact_laws": {
            "R_dec": "(1/2)(1-P)^N, independent of K",
            "R_rec": "1 - sum_k C(K,k)(-1/2)^k (1-kP/K)^N (inclusion-exclusion; no independence assumed)",
            "Pr_U_pos": "1 - sum_k C(K,k)(-1)^k (1-kP/K)^N",
            "sandwich": "(1/2) Pr(U>0) <= R_rec <= Pr(U>0), verified exactly at several N",
        },
        "decide_count_flat_in_K": flat,
        "rows": rows,
        "not_established": [
            "The coupon-collector CONSTANT is not proved here; the column "
            "'coupon_scale' is the textbook scale for comparison only.",
            "This model has a_i = b_i = 1.  It does NOT extend the fixed-K constants "
            "k0 and B, which depend on K.",
            "Every number is exact rational arithmetic; nothing is simulated.",
        ],
        "lean": [
            "LeanSupportSamplingLawV1.avoid_prob / transversal_mass / expected_prod_unseen",
            "LeanSupportDecideRecoverV1.binary_decide_value / growing_K_recover",
        ],
    }
    path = os.path.join(OUT, "P20_support_growing_k.json")
    with open(path, "w") as f:
        json.dump(out, f, indent=1)
    print(f"\ndecide count flat in K: {flat}")
    print(f"artifact: {path}")


if __name__ == "__main__":
    main()
