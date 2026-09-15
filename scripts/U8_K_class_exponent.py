#!/usr/bin/env python3
"""Support: K classes, the exact minimax law, and the error EXPONENT of deciding
versus recovering the support.

`U7_two_class_minimax.py` confirmed the two-class law. This opens it to K classes and,
more importantly, closes the PREFACTOR and the REMAINDER rather than writing `~`.

SETTING. Class i has a_i >= 1 safe labels and b_i >= 1 unsafe ones; every unsafe tip of
class i is observed with probability p_i > 0. The counts are known, the identities are
not. Write s = sum_i p_i < 1 and let L_i be the unsafe tips of class i still unseen
after N observations.

THE LAW (checked, not assumed):   R_N^* = E min_i L_i/(a_i + L_i).

THE FINITE REMAINDER BOUND, which is what the instruction asks for before any `~`.
With k_0 = min_i 1/(a_i+1) and B = prod_i b_i,

    0  <=  k_0 B (1-s)^N - R_N^*  <=  k_0 B sum_i C(b_i,2) prod_{j!=i} b_j (1-s-p_i)^N.

Both ends are checked exactly here, at every N in the ladder. That is a bound with an
explicit remainder, so `~` is earned rather than asserted -- and it also shows where the
asymptotic would stop being uniform if the number of classes grew.

RECOVERY, for comparison. The Bayes-optimal chance of naming the whole support is
prod_i C(a_i+L_i, L_i)^{-1}, so R_{N,rec}^* = E[1 - prod_i C(a_i+L_i, L_i)^{-1}], and
the two exponents to compare are

    -(1/N) log R_N^*        ->  -log(1 - sum_i p_i)
    -(1/N) log R_{N,rec}^*  ->  -log(1 - min_i p_i).

Both are computed exactly from the occupancy law and the running exponents printed, so
the reader sees convergence rather than a claimed limit.

INDEPENDENCE IS NOT ASSUMED. The L_i come from ONE observation stream, so the joint law
of (L_1,...,L_K) is computed by inclusion-exclusion over which tips were missed, using
that a given set of tips is jointly missed with probability (1 - sum of their masses)^N.
A brute-force ordered-transcript enumeration cross-checks it on the small cases.

WHAT THIS DOES NOT ESTABLISH
 - The law and the bound are verified exactly on the listed configurations; neither is
   a theorem, and there is no Lean module.
 - The limits are read off a finite ladder of N; the running exponents are printed so
   that is visible.
 - The recovery comparison uses the Bayes-optimal recovery probability; no decoder is
   constructed for it.

    .venv/bin/python scripts/U8_K_class_exponent.py
"""
from __future__ import annotations

from fractions import Fraction as F
import itertools, json, math
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def miss_law(bs, ps, N):
    """Exact joint law of (L_1,...,L_K) by inclusion-exclusion. NOT a product."""
    K = len(bs)
    out = {}
    for ks in itertools.product(*[range(b + 1) for b in bs]):
        pr = F(0)
        for js in itertools.product(*[range(k, b + 1) for k, b in zip(ks, bs)]):
            sgn = (-1) ** sum(j - k for j, k in zip(js, ks))
            coef = 1
            for j, k, b in zip(js, ks, bs):
                coef *= math.comb(j, k) * math.comb(b, j)
            pr += F(sgn * coef) * (1 - sum(j * p for j, p in zip(js, ps))) ** N
        if pr != 0:
            out[ks] = pr
    return out


def R_decide(as_, bs, ps, N):
    law = miss_law(bs, ps, N)
    return sum(pr * min(F(k, a + k) for k, a in zip(ks, as_))
               for ks, pr in law.items())


def R_recover(as_, bs, ps, N):
    law = miss_law(bs, ps, N)
    tot = F(0)
    for ks, pr in law.items():
        succ = F(1)
        for k, a in zip(ks, as_):
            succ *= F(1, math.comb(a + k, k))
        tot += pr * (1 - succ)
    return tot


def brute(as_, bs, ps, N):
    """ordered-transcript cross-check of the Bayes value and the law."""
    K = len(as_)
    starts, labels, cls = [], [], []
    for i in range(K):
        starts.append(len(labels))
        for _ in range(as_[i] + bs[i]):
            labels.append(len(labels)); cls.append(i)
    m = len(labels)
    blocks = [list(range(starts[i], starts[i] + as_[i] + bs[i])) for i in range(K)]
    worlds = [frozenset().union(*[frozenset(u) for u in combo])
              for combo in itertools.product(
                  *[list(itertools.combinations(blocks[i], bs[i])) for i in range(K)])]
    prior = F(1, len(worlds))
    anchor = 1 - sum(b * p for b, p in zip(bs, ps))
    syms = [None] + list(range(m))
    bayes = mass = F(0)
    for x in itertools.product(syms, repeat=N):
        T = set(v for v in x if v is not None)
        joint = {}
        for W in worlds:
            if not T <= W:
                continue
            v = prior
            for sx in x:
                v *= anchor if sx is None else ps[cls[sx]]
            joint[W] = v
        if not joint:
            continue
        mass += sum(joint.values())
        err = [sum(v for W, v in joint.items() if j in W) for j in range(m)]
        bayes += min(err)
    return bayes, mass


def main():
    print("Support: K classes -- the law, the remainder bound, and the exponents\n")
    print("PART 1 -- the law, cross-checked against ordered-transcript enumeration")
    rows = []
    for as_, bs, ps, N in [((1, 1), (1, 1), (F(1, 4), F(1, 8)), 2),
                           ((1, 2), (1, 1), (F(1, 5), F(1, 9)), 3),
                           ((1, 1, 1), (1, 1, 1), (F(1, 6), F(1, 8), F(1, 10)), 2)]:
        occ = R_decide(as_, bs, ps, N)
        bay, mass = brute(as_, bs, ps, N)
        if mass != 1:
            raise AssertionError(f"transcript mass {mass}")
        if occ != bay:
            raise AssertionError(f"law {occ} != Bayes {bay}")
        print(f"   a={as_} b={bs} p={[str(x) for x in ps]} N={N}: "
              f"E min_i L_i/(a_i+L_i) = {occ} = Bayes value, mass 1")
        rows.append({"a": list(as_), "b": list(bs), "p": [str(x) for x in ps],
                     "N": N, "law": str(occ), "bayes": str(bay)})
    print("   => the K-class law reproduces the exact Bayes value on every case; the")
    print("      joint law of (L_1,...,L_K) is NOT a product and is not treated as one.\n")

    print("PART 2 -- the finite remainder bound, at every N (no `~` anywhere)")
    br = []
    for as_, bs, ps in [((1, 2), (2, 1), (F(1, 5), F(1, 12))),
                        ((2, 1, 2), (2, 2, 1), (F(1, 8), F(1, 10), F(1, 30))),
                        ((1, 1), (3, 2), (F(1, 9), F(1, 20)))]:
        s = sum(ps)
        k0 = min(F(1, a + 1) for a in as_)
        B = 1
        for b in bs:
            B *= b
        rem = lambda N: k0 * B * sum(
            F(math.comb(bs[i], 2) * math.prod(bs[j] for j in range(len(bs)) if j != i))
            * (1 - s - ps[i]) ** N for i in range(len(bs)))
        print(f"   a={as_} b={bs} p={[str(x) for x in ps]}  k0={k0} B={B} s={s}")
        print(f"      {'N':>3} {'k0 B (1-s)^N - R':>18} {'bound':>16} "
              f"{'0<=gap':>8} {'gap<=bound':>11}")
        ok = True
        for N in (4, 8, 12, 16, 24, 32):
            R = R_decide(as_, bs, ps, N)
            gap = k0 * B * (1 - s) ** N - R
            bd = rem(N)
            lo_ok = gap >= 0
            hi_ok = gap <= bd
            ok = ok and lo_ok and hi_ok
            print(f"      {N:>3} {float(gap):18.6e} {float(bd):16.6e} "
                  f"{str(lo_ok):>8} {str(hi_ok):>11}")
        if not ok:
            raise AssertionError(f"the remainder bound FAILS at a={as_} b={bs}")
        br.append({"a": list(as_), "b": list(bs), "p": [str(x) for x in ps],
                   "k0": str(k0), "B": B, "s": str(s), "bound_holds": ok})
        print()

    print("PART 3 -- the two exponents")
    ex = []
    for as_, bs, ps in [((1, 2), (2, 1), (F(1, 5), F(1, 12))),
                        ((2, 1, 2), (2, 2, 1), (F(1, 8), F(1, 10), F(1, 30)))]:
        s = sum(ps)
        tgt_dec = -math.log(float(1 - s))
        tgt_rec = -math.log(float(1 - min(ps)))
        print(f"   a={as_} b={bs} p={[str(x) for x in ps]}:"
              f"  target decide {tgt_dec:.6f}   target recover {tgt_rec:.6f}")
        print(f"      {'N':>3} {'-log R_dec /N':>14} {'-log R_rec /N':>14} "
              f"{'R_dec/R_rec':>13}")
        row = {"a": list(as_), "b": list(bs), "p": [str(x) for x in ps],
               "target_decide": tgt_dec, "target_recover": tgt_rec, "N": []}
        for N in (8, 16, 24, 32, 48, 64):
            Rd = R_decide(as_, bs, ps, N)
            Rr = R_recover(as_, bs, ps, N)
            ed = -math.log(float(Rd)) / N
            er = -math.log(float(Rr)) / N
            print(f"      {N:>3} {ed:14.6f} {er:14.6f} {float(Rd / Rr):13.3e}")
            row["N"].append({"N": N, "exp_decide": ed, "exp_recover": er,
                             "ratio": float(Rd / Rr)})
        ex.append(row)
        print()

    print("VERDICT")
    print("   The K-class law matches the exact Bayes value; the two-sided remainder")
    print("   bound holds at every N tried, so the leading term k0 B (1-s)^N is earned")
    print("   with an explicit error rather than asserted; and the two exponents")
    print("   separate, with the decide exponent heading for -log(1-sum p_i) and the")
    print("   recover exponent for -log(1-min p_i). The ladders are finite: the running")
    print("   exponents are printed so convergence is visible, not claimed.")

    out = REPO / "research/worker_U8_support_20260914/U8_K_class_exponent.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "law": "R_N* = E min_i L_i/(a_i+L_i)", "law_checks": rows,
        "remainder_bound": "0 <= k0 B (1-s)^N - R_N* <= k0 B sum_i C(b_i,2) "
                           "prod_{j!=i} b_j (1-s-p_i)^N",
        "remainder_checks": br, "exponents": ex,
        "not_established": [
            "verified exactly on the listed configurations; not a theorem, no Lean",
            "limits read off a finite ladder of N",
            "the recovery comparison uses the Bayes-optimal recovery probability; no "
            "decoder is constructed for it",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
