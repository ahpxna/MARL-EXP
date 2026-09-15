#!/usr/bin/env python3
"""Support A: the safe-decision law by the ONE-TIP-PER-CLASS event, not by
inclusion-exclusion.

`P2_support_exponent_law.py` built the exact joint law of (L_1,...,L_K) by
inclusion-exclusion and verified sharp brackets on finite configurations.  That is
more machinery than the exponent needs, and the supervisor's route is both shorter
and closer to a theorem.  With s = sum_i p_i < 1:

    LOWER.  Fix ONE unsafe tip in each class.  No draw hits any of those K tips with
    probability exactly (1-s)^N, and on that event every L_i >= 1, so
        min_i L_i/(a_i+L_i) >= min_i 1/(a_i+1) =: k0.
    Hence  R_dec >= k0 (1-s)^N.

    UPPER.  Since a_i >= 1, L_i/(a_i+L_i) <= L_i, so min_i L_i/(a_i+L_i) <= min_i L_i
    <= prod_i L_i (both sides vanish together when some L_i = 0).  Taking
    expectations and counting tuples, E[prod_i L_i] = B (1-s)^N with B = prod_i b_i.
    Hence  R_dec <= B (1-s)^N.

    RECOVERY.  With i* attaining p_min: R_rec >= (a_{i*}/(a_{i*}+1)) (1-p_min)^N from a
    single fixed tip of class i*, and R_rec <= sum_i b_i (1-p_i)^N <= (sum_i b_i)
    (1-p_min)^N by a union bound over all unsafe tips.

So both tasks are Theta of a single exponential, the exponents are -log(1-s) and
-log(1-p_min), and NO joint law is needed.  All four inequalities are checked here in
exact rational arithmetic against the exact values computed from P2's joint law, at
every N in the grid, on every configuration -- so the shortcut is verified against
the machinery it replaces.

The two pointwise facts the argument rests on -- `L/(a+L) <= L` for `a >= 1` and
`min_i L_i <= prod_i L_i` -- are proved in `LeanSupportDecideExponentV1`.

WHAT THIS DOES NOT ESTABLISH
  * The step E[prod_i L_i] = B (1-s)^N is the tuple count; the counting identity is
    `LeanSupportTupleCountV1.prod_card_eq_tuples`, the probability (1-s)^N of a fixed
    tuple staying unseen is checked here against the exact law, not proved in Lean.
  * The posterior/minimax step for K classes is NOT re-derived; `passive_minimax` in
    `LeanSupportBayesMinimaxV1` is the one-class statement, and the K-class version is
    cross-checked numerically by `U8_K_class_exponent.py`, not proved.
  * Finite configurations and a finite grid of N.

    .venv/bin/python scripts/P13_support_decide_exponent.py
"""
from __future__ import annotations
from fractions import Fraction as F
import importlib.util, json, math
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("u8", REPO / "scripts/U8_K_class_exponent.py")
u8 = importlib.util.module_from_spec(spec); spec.loader.exec_module(u8)

CONFIGS = [((1, 1), (2, 2), (F(1, 8), F(1, 12))),
           ((1, 2), (2, 3), (F(1, 10), F(1, 30))),
           ((2, 1, 1), (2, 2, 2), (F(1, 12), F(1, 16), F(1, 24))),
           ((1, 3), (3, 2), (F(1, 16), F(1, 40))),
           ((3, 1), (2, 4), (F(1, 20), F(1, 25)))]


def main():
    print("Support: the decide/recover exponents by one-tip-per-class events\n")
    res = {"configs": []}
    nchecks = 0
    for as_, bs, ps in CONFIGS:
        s = sum(ps); pmin = min(ps)
        istar = min(range(len(ps)), key=lambda i: ps[i])
        k0 = min(F(1, a + 1) for a in as_)
        B = 1
        for b in bs:
            B *= b
        row = {"a": as_, "b": bs, "p": [str(x) for x in ps], "s": str(s),
               "p_min": str(pmin), "k0": str(k0), "B": B, "N": []}
        for N in (4, 8, 12, 16, 24, 32, 48):
            Rd = u8.R_decide(as_, bs, ps, N)
            Rr = u8.R_recover(as_, bs, ps, N)
            lo_d = k0 * (1 - s) ** N
            hi_d = B * (1 - s) ** N
            lo_r = F(as_[istar], as_[istar] + 1) * (1 - pmin) ** N
            hi_r = sum(b * (1 - p) ** N for b, p in zip(bs, ps))
            for name, lo, val, hi in (("decide", lo_d, Rd, hi_d),
                                      ("recover", lo_r, Rr, hi_r)):
                if not (lo <= val <= hi):
                    raise AssertionError(
                        f"{name} bracket FAILS a={as_} b={bs} N={N}: "
                        f"{float(lo)} <= {float(val)} <= {float(hi)}")
                nchecks += 1
            # the tuple-count identity behind the upper bound
            law = u8.miss_law(bs, ps, N)
            ET = sum(pr * math.prod(ks) for ks, pr in law.items())
            if ET != B * (1 - s) ** N:
                raise AssertionError(f"E[prod L_i] != B(1-s)^N at N={N}")
            nchecks += 1
            row["N"].append({"N": N, "R_decide": float(Rd), "R_recover": float(Rr),
                             "decide_lo": float(lo_d), "decide_hi": float(hi_d),
                             "recover_lo": float(lo_r), "recover_hi": float(hi_r),
                             "E_prod_L": float(ET),
                             "decide_ratio_hi_over_lo": float(hi_d / lo_d),
                             "recover_ratio_hi_over_lo": float(hi_r / lo_r)})
        ed, er = -math.log(1 - float(s)), -math.log(1 - float(pmin))
        row["decide_exponent"] = ed
        row["recover_exponent"] = er
        row["exponent_ratio"] = ed / er
        print(f"   a={as_} b={bs}: both brackets hold at 7 values of N; "
              f"constants (lo,hi) = ({float(k0):.4f}, {B}) decide, "
              f"({float(F(as_[istar], as_[istar]+1)):.4f}, {sum(bs)}) recover")
        print(f"      exponents: decide {ed:.6f} = -log(1-s), recover {er:.6f} = "
              f"-log(1-p_min), ratio {ed/er:.4f}")
        res["configs"].append(row)
    print(f"\n   {nchecks} exact rational checks, zero failures.")
    print("   Both tasks are Theta of ONE exponential with EXPLICIT constants, and")
    print("   the joint law is never needed -- only the one-tip-per-class event and")
    print("   a union bound.  The ratio hi/lo is a constant in N, so the exponents")
    print("   are pinned, not fitted.")
    res["nchecks"] = nchecks
    res["not_established"] = [
        "E[prod L_i] = B(1-s)^N is checked against the exact law here; the counting "
        "half is LeanSupportTupleCountV1, the probability half is not in Lean",
        "the K-class posterior/minimax step is not re-derived; U8 cross-checks it "
        "against ordered-transcript enumeration",
        "finite configurations, finite grid of N",
    ]
    out = REPO / "research/worker_P13_support_20260915/P13_support_decide_exponent.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
