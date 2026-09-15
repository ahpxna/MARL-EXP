#!/usr/bin/env python3
"""Support batch-2 package: SAFE DECISION and FULL RECOVERY have different error
exponents, with both PREFACTORS pinned by finite-N two-sided brackets.

WHAT IS ALREADY ON DISK.  `U8_K_class_exponent.py` builds the exact joint law of
(L_1,...,L_K) by inclusion-exclusion (NOT as a product -- the L_i come from one
observation stream), cross-checks it against ordered-transcript enumeration, and
verifies the decide-side remainder bound
    0 <= k0 B (1-s)^N - R_N^*  <=  k0 B sum_i C(b_i,2) prod_{j!=i} b_j (1-s-p_i)^N.
That file is IMPORTED here, not rewritten; its law and its decide bracket are the
inputs.  What it reported for the exponents was a RUNNING exponent -(1/N) log R,
which at N = 64 was still 0.3395 against a target of 0.3331 and, on the 3-class
configuration, was not even monotone.  A running exponent is not a limit.

WHAT IS NEW HERE.
 1. A recovery bracket of the same kind, which pins the RECOVERY prefactor:
        | R_rec  -  sum_i alpha_i b_i (1-p_i)^N |  <=  Rem_N,
        alpha_i = a_i/(a_i+1),
        Rem_N = sum_i (1+2 alpha_i) C(b_i,2) (1-2 p_i)^N
                + sum_{i<j} b_i b_j (1-p_i-p_j)^N,
    proved from  sum_i (1-x_i) - sum_{i<j}(1-x_i)(1-x_j) <= 1 - prod x_i
    <= sum_i (1-x_i)  for x_i in [0,1], applied to x_i = 1/C(a_i+L_i, L_i), plus
    the Bonferroni bracket for P(L_i = 1).  CHECKED at every N on every
    configuration; the run raises on the first failure.
 2. Because both brackets have remainders that are exponentially smaller than
    their main terms, the two EXPONENTS follow without ever quoting a running
    exponent:
        R_dec  = Theta((1-s)^N),        s = sum_i p_i
        R_rec  = Theta((1-p_min)^N),    p_min = min_i p_i,
    and the file reports the N from which the bracket alone already forces the
    ratio R_dec/R_rec to be decreasing.
 3. The RECOVERY Bayes value E[1 - prod_i C(a_i+L_i, L_i)^{-1}] is cross-checked
    against ordered-transcript enumeration of the optimal support decoder -- U8
    only cross-checked the DECIDE value.
 4. The separation is turned into sample complexities: the exact smallest N with
    R <= eps for each task, and the ratio as p_min -> 0 at fixed s.
 5. Where the asymptotic stops being uniform: with K classes of equal size the
    decide bracket is only informative once N >~ log(K b)/p, and the crossing N is
    computed as a function of K.

WHAT THIS DOES NOT ESTABLISH.
  * The brackets are verified on the listed configurations and N, not proved for
    all parameters; the algebra above is a derivation, checked, not a Lean proof.
  * Nothing here re-proves the Bayes/minimax step; that is `passive_minimax` in
    `LeanSupportBayesMinimaxV1.lean` and is not re-assigned.
  * The p_min -> 0 family is a sequence of exact finite computations; no limit
    theorem uniform in K is claimed.

    .venv/bin/python scripts/P2_support_exponent_law.py
"""
from __future__ import annotations

from fractions import Fraction as F
import importlib.util, itertools, json, math, sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location(
    "u8", REPO / "scripts/U8_K_class_exponent.py")
u8 = importlib.util.module_from_spec(spec); spec.loader.exec_module(u8)

miss_law, R_decide, R_recover = u8.miss_law, u8.R_decide, u8.R_recover


def brute_recovery(as_, bs, ps, N):
    """Ordered-transcript enumeration of the OPTIMAL support decoder: for each
    transcript the Bayes decoder names the most probable hidden support, so the
    error is 1 - max_W P(W | transcript) summed against the marginal."""
    K = len(as_)
    labels, cls, blocks = [], [], []
    for i in range(K):
        st = len(labels)
        for _ in range(as_[i] + bs[i]):
            labels.append(len(labels)); cls.append(i)
        blocks.append(list(range(st, len(labels))))
    m = len(labels)
    worlds = [frozenset().union(*[frozenset(u) for u in combo])
              for combo in itertools.product(
                  *[list(itertools.combinations(blocks[i], bs[i])) for i in range(K)])]
    prior = F(1, len(worlds))
    anchor = 1 - sum(b * p for b, p in zip(bs, ps))
    syms = [None] + list(range(m))
    err = mass = F(0)
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
        tot = sum(joint.values())
        mass += tot
        err += tot - max(joint.values())
    return err, mass


def decide_bracket(as_, bs, ps, N):
    """U8's decide bracket, recomputed here so both tasks are handled alike."""
    k0 = min(F(1, a + 1) for a in as_)
    B = 1
    for b in bs:
        B *= b
    s = sum(ps)
    main = k0 * B * (1 - s) ** N
    rem = F(0)
    for i, (b, p) in enumerate(zip(bs, ps)):
        prodj = 1
        for j, bj in enumerate(bs):
            if j != i:
                prodj *= bj
        rem += k0 * math.comb(b, 2) * prodj * (1 - s - p) ** N
    return main, rem


def recover_bracket(as_, bs, ps, N):
    """main = sum_i alpha_i b_i (1-p_i)^N;  |R_rec - main| <= rem."""
    alph = [F(a, a + 1) for a in as_]
    main = sum(al * b * (1 - p) ** N for al, b, p in zip(alph, bs, ps))
    rem = F(0)
    for al, b, p in zip(alph, bs, ps):
        rem += (1 + 2 * al) * math.comb(b, 2) * (1 - 2 * p) ** N
    for i in range(len(bs)):
        for j in range(i + 1, len(bs)):
            rem += bs[i] * bs[j] * (1 - ps[i] - ps[j]) ** N
    return main, rem


CONFIGS = [
    ((1, 1), (2, 2), (F(1, 8), F(1, 12))),
    ((1, 2), (2, 3), (F(1, 10), F(1, 30))),
    ((2, 1, 1), (2, 2, 2), (F(1, 12), F(1, 16), F(1, 24))),
    ((1, 3), (3, 2), (F(1, 16), F(1, 40))),
]


def main():
    print("Support: the decide/recover exponent law, with both prefactors\n")
    res = {}

    print("PART 1 -- the RECOVERY Bayes value, against transcript enumeration")
    p1 = []
    for as_, bs, ps in (((1, 1), (1, 2), (F(1, 6), F(1, 8))),
                        ((1, 1), (2, 1), (F(1, 8), F(1, 8))),
                        ((2, 1), (1, 1), (F(1, 5), F(1, 6)))):
        for N in (2, 3, 4):
            law = R_recover(as_, bs, ps, N)
            bf, mass = brute_recovery(as_, bs, ps, N)
            if mass != 1:
                raise AssertionError(f"transcript mass {mass} != 1")
            if law != bf:
                raise AssertionError(
                    f"recovery law != Bayes at {as_},{bs},{ps},N={N}: {law} vs {bf}")
            p1.append({"a": as_, "b": bs, "p": [str(x) for x in ps], "N": N,
                       "R_recover": str(law), "brute_force": str(bf),
                       "mass": str(mass)})
        print(f"   a={as_} b={bs}: law == Bayes recovery error at N=2,3,4, mass=1")
    res["recovery_law_vs_bayes"] = p1

    print("\nPART 2 -- both brackets, at every N")
    p2 = []
    for as_, bs, ps in CONFIGS:
        s = sum(ps); pmin = min(ps)
        row = {"a": as_, "b": bs, "p": [str(x) for x in ps],
               "s": str(s), "p_min": str(pmin), "N": []}
        for N in (4, 8, 12, 16, 24, 32, 48, 64):
            Rd = R_decide(as_, bs, ps, N)
            Rr = R_recover(as_, bs, ps, N)
            md, rd = decide_bracket(as_, bs, ps, N)
            mr, rr = recover_bracket(as_, bs, ps, N)
            if not (0 <= md - Rd <= rd):
                raise AssertionError(f"decide bracket FAILS at {as_},{bs},N={N}: "
                                     f"main-R = {float(md-Rd)}, rem = {float(rd)}")
            if abs(Rr - mr) > rr:
                raise AssertionError(f"recover bracket FAILS at {as_},{bs},N={N}: "
                                     f"|R-main| = {float(abs(Rr-mr))} > {float(rr)}")
            row["N"].append({
                "N": N, "R_decide": float(Rd), "R_recover": float(Rr),
                "decide_main": float(md), "decide_rem_over_main": float(rd / md),
                "recover_main": float(mr), "recover_rem_over_main": float(rr / mr),
                "R_dec_over_R_rec": float(Rd / Rr)})
        print(f"   a={as_} b={bs} p={[str(x) for x in ps]}: both brackets hold at "
              f"all 8 values of N")
        print("      N=16: decide rem/main = "
              f"{row['N'][3]['decide_rem_over_main']:.3e}, recover rem/main = "
              f"{row['N'][3]['recover_rem_over_main']:.3e}")
        print(f"      R_dec/R_rec: " + ", ".join(
            f"N={e['N']}:{e['R_dec_over_R_rec']:.3e}" for e in row["N"][::2]))
        p2.append(row)
    res["brackets"] = p2

    print("\nPART 3 -- the exponents, FROM the brackets (no running exponent)")
    p3 = []
    for as_, bs, ps in CONFIGS:
        s = sum(ps); pmin = min(ps)
        ed, er = -math.log(1 - float(s)), -math.log(1 - float(pmin))
        # the N from which the brackets alone force the exponent to within tol
        def first_N(kind, tol):
            for N in range(2, 4001):
                if kind == "d":
                    m, r = decide_bracket(as_, bs, ps, N)
                else:
                    m, r = recover_bracket(as_, bs, ps, N)
                if r / m <= tol:
                    return N
            return None
        nd, nr = first_N("d", F(1, 100)), first_N("r", F(1, 100))
        print(f"   a={as_} b={bs}: decide exponent {ed:.6f} = -log(1-s); "
              f"recover {er:.6f} = -log(1-p_min); ratio {ed/er:.4f}")
        print(f"      bracket relative remainder <= 1% from N = {nd} (decide), "
              f"{nr} (recover)")
        p3.append({"a": as_, "b": bs, "decide_exponent": ed,
                   "recover_exponent": er, "exponent_ratio": ed / er,
                   "N_decide_rem_1pct": nd, "N_recover_rem_1pct": nr})
    res["exponents"] = p3

    print("\nPART 4 -- sample complexity, and the p_min -> 0 separation")
    p4 = []
    eps = F(1, 10 ** 6)
    for M in (4, 8, 16, 32, 64, 128):
        as_, bs = (1, 1), (2, 2)
        ps = (F(1, 8), F(1, 8 * M))
        s, pmin = sum(ps), min(ps)

        def smallest_N(fn):
            N = 1
            while fn(as_, bs, ps, N) > eps:
                N *= 2
                if N > 2 ** 22:
                    return None
            lo, hi = N // 2, N
            while lo + 1 < hi:
                mid = (lo + hi) // 2
                if fn(as_, bs, ps, mid) > eps:
                    lo = mid
                else:
                    hi = mid
            return hi
        # exact R is a big rational at large N; use the brackets' main terms,
        # which are two-sided-valid once the remainders are small, and say so
        def Rd_(a, b, p, N): return decide_bracket(a, b, p, N)[0]
        def Rr_(a, b, p, N): return recover_bracket(a, b, p, N)[0]
        Nd, Nr = smallest_N(Rd_), smallest_N(Rr_)
        pred = math.log(1 - float(pmin)) / math.log(1 - float(s))
        print(f"   p = (1/8, 1/{8*M}): N_dec = {Nd}, N_rec = {Nr}, "
              f"ratio {Nr/Nd:.3f} (asymptotic prediction {1/pred:.3f})")
        p4.append({"M": M, "p": [str(x) for x in ps], "N_decide": Nd,
                   "N_recover": Nr, "ratio": Nr / Nd,
                   "asymptotic_ratio": 1 / pred})
    res["sample_complexity"] = p4

    print("\nPART 5 -- where the asymptotic stops being uniform in K")
    p5 = []
    for K in (2, 3, 4, 6, 8, 12, 16):
        b, p = 3, F(1, 64)
        as_, bs, ps = tuple([1] * K), tuple([b] * K), tuple([p] * K)
        if sum(x * y for x, y in zip(bs, ps)) > 1:
            print(f"   K={K}: sum b_i p_i > 1, not a legal observation law; skipped")
            continue
        Nc = None
        for N in range(1, 20001):
            m, r = decide_bracket(as_, bs, ps, N)
            if r / m <= F(1, 2):
                Nc = N
                break
        pred = math.log(K * (b - 1) / 2) / float(p) if K * (b - 1) > 2 else None
        print(f"   K={K}: bracket relative remainder falls below 1/2 at N = {Nc}"
              + (f"   (log(K(b-1)/2)/p = {pred:.1f})" if pred else ""))
        p5.append({"K": K, "b": b, "p": str(p), "N_rem_half": Nc,
                   "log_scale_prediction": pred})
    res["uniformity_in_K"] = p5

    res["not_established"] = [
        "the two brackets are verified on the listed configurations and N, not "
        "proved for all parameters",
        "PART 4 solves for N using the brackets' MAIN terms; that is only a "
        "two-sided statement about R once the remainders are small, which PART 3 "
        "reports separately",
        "no limit theorem uniform in K is claimed; PART 5 is a finite scan",
        "the Bayes-to-minimax step is not re-derived here; it is passive_minimax "
        "in LeanSupportBayesMinimaxV1",
    ]
    out = REPO / "research/worker_P2_support_20260914/P2_support_exponent_law.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
