#!/usr/bin/env python3
"""D1 / Goi D -- passive support learning with MANY safe answers.

WHAT THIS PROBE CHECKS (exact rational arithmetic, raises on any mismatch).

Model.  m = a + b singleton decisions on the multi-tip support geometry.  The
world W is the set of UNSAFE decisions, |W| = b; the a = m - b decisions outside
W are safe (selectedRadius = 0, `zero_radius_iff`).  A passive sample is N i.i.d.
draws from the law that puts mass gamma on each unsafe tip and 1 - b*gamma on the
anchor, with 0 < b*gamma <= 1.  L_N = number of unsafe tips not yet observed; the
UNSEEN set has a + L_N elements, of which L_N are unsafe.

Checks.
  C1  exact law of L_N by inclusion-exclusion, total mass 1, and
      E L_N = b (1-gamma)^N  exactly.
  C2  second moment:  E L_N^2 = lam + b(b-1)(1-2 gamma)^N  <=  lam + lam^2
      (negative correlation of the "tip still unseen" events).
  C3  the two moment bounds, on 1008 configurations:
          lam/(a+1+lam)  <=  E[L/(a+L)]  <=  lam/(a+lam).
  C4  MINIMAX IDENTITY by brute force on small configurations: enumerate all
      C(m,b) worlds and all (b+1)^N transcripts;
        (i)  every transcript has the SAME likelihood under every consistent
             world of size b (step 3 of the proof route);
        (ii) the posterior-optimal error on a transcript with L unseen unsafe
             tips is exactly L/(a+L);
        (iii) the uniform-on-unseen rule has risk exactly E[L/(a+L)] in EVERY
             world, so sup_W = Bayes and R_N^star = E[L/(a+L)];
        (iv) no rule (over the full randomized simplex, checked via the exact
             Bayes optimum) beats that value.
  C5  sample-size thresholds: sufficient  b(1-gamma)^N <= a*delta/(1-delta),
      necessary with a replaced by a+1; the two integer thresholds differ by at
      most ceil(log 2 / -log(1-gamma)).
  C6  the three regimes (a=1 pays log b; a ~ b kills the log b; b/m <= delta is
      solvable with zero samples).

WHAT THIS DOES NOT ESTABLISH.  Numerical evidence only -- no Lean receipt is
produced here; see work/p13_conjectures/LeanSupportPassiveAnswerMultiplicityV1.lean
for the compiled statements.  Only passive sampling, one tip per decision,
homogeneous tip mass gamma, N fixed in advance.
"""

from fractions import Fraction as F
from itertools import combinations, product
from math import comb, log, ceil
import json
import sys


# ----------------------------------------------------------------- exact law

def law_L(b, gamma, N):
    """Exact distribution of L_N = # unsafe tips never drawn, as {l: prob}."""
    out = {}
    for l in range(b + 1):
        # inclusion-exclusion over the tips outside the chosen unseen set
        s = F(0)
        for i in range(0, b - l + 1):
            s += F((-1) ** i) * comb(b - l, i) * (1 - (l + i) * gamma) ** N
        out[l] = comb(b, l) * s
    return out


def moments(b, gamma, N):
    law = law_L(b, gamma, N)
    tot = sum(law.values())
    if tot != 1:
        raise AssertionError(f"law of L does not sum to 1: b={b} gamma={gamma} N={N} tot={tot}")
    for l, p in law.items():
        if p < 0:
            raise AssertionError(f"negative probability: b={b} gamma={gamma} N={N} l={l} p={p}")
    m1 = sum(l * p for l, p in law.items())
    m2 = sum(l * l * p for l, p in law.items())
    return law, m1, m2


# ------------------------------------------------------- brute force minimax

def brute_force_minimax(a, b, gamma, N):
    """Exact minimax risk by enumeration.  Returns a dict of certified facts."""
    m = a + b
    tips = list(range(m))
    worlds = list(combinations(tips, b))
    anchor = None
    alphabet = [anchor] + tips          # an observation is the anchor or a tip
    transcripts = list(product(alphabet, repeat=N))

    def like(W, x):
        """likelihood of transcript x under world W (exact Fraction)."""
        Ws = set(W)
        p = F(1)
        for o in x:
            if o is anchor:
                p *= 1 - b * gamma
            elif o in Ws:
                p *= gamma
            else:
                return F(0)
        return p

    # (i) same likelihood for every consistent world of size b
    for x in transcripts:
        seen = {o for o in x if o is not anchor}
        vals = {like(W, x) for W in worlds if seen <= set(W)}
        if len(vals) > 1:
            raise AssertionError(f"likelihood not constant across consistent worlds: {x} {vals}")

    # marginal of a transcript under the uniform prior on worlds
    nW = len(worlds)
    # (ii)+(iv) Bayes risk of the posterior-optimal rule
    bayes = F(0)
    for x in transcripts:
        seen = frozenset(o for o in x if o is not anchor)
        if len(seen) > b:
            continue
        # posterior mass of "decision j is unsafe", up to the common factor
        marg = sum(like(W, x) for W in worlds) / nW
        if marg == 0:
            continue
        post_unsafe = {}
        for j in tips:
            post_unsafe[j] = sum(like(W, x) for W in worlds if j in W) / nW / marg
        best = min(post_unsafe.values())
        # (ii) the optimum equals L/(a+L) and is attained exactly on unseen tips
        L = b - len(seen)
        target = F(L, a + L)
        if best != target:
            raise AssertionError(f"posterior optimum {best} != L/(a+L) = {target} at {x}")
        for j in tips:
            if j in seen and post_unsafe[j] != 1:
                raise AssertionError(f"seen tip {j} not certainly unsafe at {x}")
            if j not in seen and post_unsafe[j] != target:
                raise AssertionError(f"unseen tip {j} posterior {post_unsafe[j]} != {target}")
        bayes += marg * best

    # (iii) uniform-on-unseen rule: risk in EVERY world
    risks = []
    for W in worlds:
        r = F(0)
        for x in transcripts:
            p = like(W, x)
            if p == 0:
                continue
            seen = {o for o in x if o is not anchor}
            unseen = [j for j in tips if j not in seen]
            bad = len([j for j in unseen if j in set(W)])
            r += p * F(bad, len(unseen))
        risks.append(r)
    if len(set(risks)) != 1:
        raise AssertionError(f"uniform-on-unseen risk is not world independent: {set(risks)}")
    achieved = risks[0]

    _, m1, _ = moments(b, gamma, N)
    law = law_L(b, gamma, N)
    closed = sum(p * F(l, a + l) for l, p in law.items())

    if achieved != closed:
        raise AssertionError(f"achieved {achieved} != E[L/(a+L)] {closed}")
    if bayes != closed:
        raise AssertionError(f"Bayes {bayes} != E[L/(a+L)] {closed}")
    return {"minimax": closed, "bayes": bayes, "achieved": achieved, "lam": m1}


# ----------------------------------------------------------------- the bounds

def check_bounds(a, b, gamma, N):
    law, lam, m2 = moments(b, gamma, N)
    # C2 : the explicit second moment and the negative-correlation bound
    m2_closed = lam + b * (b - 1) * (1 - 2 * gamma) ** N if b >= 2 else lam
    if m2 != m2_closed:
        raise AssertionError(f"second moment mismatch a={a} b={b} g={gamma} N={N}: {m2} {m2_closed}")
    if m2 > lam + lam * lam:
        raise AssertionError(f"E L^2 > lam + lam^2 at a={a} b={b} g={gamma} N={N}")
    lam_closed = b * (1 - gamma) ** N
    if lam != lam_closed:
        raise AssertionError(f"E L != b(1-gamma)^N at a={a} b={b} g={gamma} N={N}")
    R = sum(p * F(l, a + l) for l, p in law.items())
    lo = F(lam, 1) / (a + 1 + lam)
    hi = F(lam, 1) / (a + lam)
    if not (lo <= R <= hi):
        raise AssertionError(f"bounds fail a={a} b={b} g={gamma} N={N}: {lo} {R} {hi}")
    return R, lam, lo, hi


# ------------------------------------------------------------ sample sizes

def threshold(a, b, gamma, delta):
    """least N with b(1-gamma)^N <= a*delta/(1-delta)."""
    rhs = F(a) * delta / (1 - delta)
    N = 0
    while b * (1 - gamma) ** N > rhs:
        N += 1
        if N > 100000:
            raise AssertionError("threshold search diverged")
    return N


def main():
    report = {}

    # ---- C3 : 1008 configurations of the two moment bounds
    A = [1, 2, 3, 5, 7, 11]
    B = [1, 2, 3, 4, 6, 8, 12]
    KS = [1, 2, 3, 4]
    NS = [0, 1, 2, 3, 5, 8]
    rows = 0
    tight_upper = 0
    tight_lower = 0
    worst_lo_gap = None
    worst_hi_gap = None
    for a in A:
        for b in B:
            for k in KS:
                gamma = F(1, k * b)          # b*gamma = 1/k <= 1
                for N in NS:
                    R, lam, lo, hi = check_bounds(a, b, gamma, N)
                    rows += 1
                    if R == hi:
                        tight_upper += 1
                    if R == lo:
                        tight_lower += 1
                    gh = hi - R
                    gl = R - lo
                    if worst_hi_gap is None or gh > worst_hi_gap[0]:
                        worst_hi_gap = (gh, a, b, str(gamma), N)
                    if worst_lo_gap is None or gl > worst_lo_gap[0]:
                        worst_lo_gap = (gl, a, b, str(gamma), N)
    if rows != 1008:
        raise AssertionError(f"expected 1008 configurations, got {rows}")
    report["C3_moment_bounds"] = {
        "configurations": rows,
        "all_bounds_hold": True,
        "upper_bound_tight_count": tight_upper,
        "lower_bound_tight_count": tight_lower,
        "worst_upper_slack": [str(worst_hi_gap[0])] + list(worst_hi_gap[1:]),
        "worst_lower_slack": [str(worst_lo_gap[0])] + list(worst_lo_gap[1:]),
    }

    # ---- C4 : brute-force minimax identity on small configurations
    bf = []
    for (a, b, N) in [(1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 2, 1), (1, 2, 2),
                      (2, 1, 1), (2, 2, 1), (2, 2, 2), (3, 2, 2), (2, 3, 2),
                      (1, 3, 2), (3, 1, 3), (2, 2, 3)]:
        for k in (1, 2):
            gamma = F(1, k * b)
            d = brute_force_minimax(a, b, gamma, N)
            lam = d["lam"]
            lo = F(lam, 1) / (a + 1 + lam)
            hi = F(lam, 1) / (a + lam)
            if not (lo <= d["minimax"] <= hi):
                raise AssertionError("brute force minimax violates the moment bounds")
            bf.append({"a": a, "b": b, "gamma": str(gamma), "N": N,
                       "minimax": str(d["minimax"]), "lam": str(lam),
                       "lower": str(lo), "upper": str(hi)})
    report["C4_minimax_identity"] = {
        "configurations": len(bf),
        "bayes_equals_achieved_equals_E_L_over_a_plus_L": True,
        "rows": bf,
    }

    # ---- C5 : the two sample-size thresholds
    gaps = []
    for a in [1, 2, 3, 5, 10]:
        for b in [2, 4, 8, 16, 64]:
            for k in [1, 2, 4]:
                gamma = F(1, k * b)
                for delta in [F(1, 2), F(1, 4), F(1, 10), F(1, 100)]:
                    Ns = threshold(a, b, gamma, delta)       # sufficient
                    Nn = threshold(a + 1, b, gamma, delta)   # necessary
                    if Nn > Ns:
                        raise AssertionError("necessary threshold exceeds sufficient one")
                    bound = ceil(log(2) / (-log(1 - float(gamma))))
                    if Ns - Nn > bound:
                        raise AssertionError(
                            f"threshold gap {Ns-Nn} exceeds ceil(log2/-log(1-gamma))={bound}")
                    # sufficiency really gives risk <= delta
                    R, lam, lo, hi = check_bounds(a, b, gamma, Ns)
                    if R > delta:
                        raise AssertionError("sufficient threshold does not deliver risk <= delta")
                    # necessity: below Nn the minimax risk exceeds delta
                    if Nn > 0:
                        R2, _, lo2, _ = check_bounds(a, b, gamma, Nn - 1)
                        if R2 <= delta and lo2 <= delta:
                            pass  # the necessary bound is on the CERTIFICATE lam, not on R
                        if lo2 <= delta:
                            raise AssertionError(
                                "below the necessary threshold the lower certificate still passes")
                    gaps.append(Ns - Nn)
    report["C5_sample_size"] = {
        "configurations": len(gaps),
        "max_threshold_gap": max(gaps),
        "all_gaps_within_log2_over_minus_log_1_minus_gamma": True,
    }

    # ---- C6 : the three regimes
    regimes = {}
    delta = F(1, 10)
    # a = 1: the log b cost
    r = []
    for b in [2, 4, 8, 16, 32, 64, 128]:
        gamma = F(1, 256)
        r.append({"b": b, "N": threshold(1, b, gamma, delta)})
    regimes["a_equals_1_log_b_cost"] = r
    # a proportional to b: no log b
    r = []
    for b in [2, 4, 8, 16, 32, 64, 128]:
        gamma = F(1, 256)
        r.append({"b": b, "a": b, "N": threshold(b, b, gamma, delta)})
    regimes["a_equals_b_no_log_b"] = r
    # b/m <= delta : zero samples
    zero = []
    for (a, b) in [(9, 1), (18, 2), (90, 10), (19, 1)]:
        m = a + b
        if F(b, m) <= delta:
            R, lam, lo, hi = check_bounds(a, b, F(1, b), 0)
            if R != F(b, m):
                raise AssertionError("N=0 risk is not b/m")
            if R > delta:
                raise AssertionError("b/m <= delta but the zero-sample risk exceeds delta")
            zero.append({"a": a, "b": b, "risk_at_N_0": str(R)})
    regimes["b_over_m_le_delta_zero_samples"] = zero
    report["C6_regimes"] = regimes

    out = "/Users/phanan/cig-amf-main/research/worker_gopD_20260913/D1_support_answer_multiplicity.json"
    with open(out, "w") as f:
        json.dump(report, f, indent=2, sort_keys=True)
    print(json.dumps({k: (v if k != "C4_minimax_identity" else
                          {kk: vv for kk, vv in v.items() if kk != "rows"})
                      for k, v in report.items()}, indent=2, sort_keys=True))
    print("wrote", out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
