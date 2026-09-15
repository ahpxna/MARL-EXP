#!/usr/bin/env python3
"""Support: verify the posterior, the passive minimax and the active minimax by
brute force before any of it is formalised.

Model. m = a + b decisions; the hidden world W is a b-subset (the unsafe tips).
Passive observation law: anchor with probability 1 - b*p, tip i with probability
p for each i in W. Active query: "is i unsafe", i.e. membership of i in W.

Three claims under test, all exactly:

  U2  with a uniform prior over b-subsets and a transcript whose seen-tip set is
      S (|S| = s), the posterior is uniform on {W : |W| = b, S subset W}, so for
      j not in S,   Pr(j in W | data) = (b-s)/(m-s).

  U3  the passive minimax risk is  R_N* = E[ L_N/(a + L_N) ],  L_N = |W \\ S_N|,
      attained by choosing uniformly among the unseen decisions.

  U5  the active minimax risk after k membership queries is
      R*_k = C(b,k+1)/C(a+b,k+1),
      and this is the Bayes-optimal value over ALL deterministic adaptive query
      trees of depth k (enumerated, not assumed).

Raises on any mismatch.   python3 scripts/U1_support_minimax_check.py
"""
from fractions import Fraction as F
from functools import lru_cache
import itertools, json, math
from pathlib import Path


def worlds(m, b):
    return [frozenset(c) for c in itertools.combinations(range(m), b)]


# ---------------------------------------------------------------- U2 posterior
def check_posterior(m, b):
    Ws = worlds(m, b)
    bad = 0
    for s in range(0, b + 1):
        for S in itertools.combinations(range(m), s):
            S = frozenset(S)
            comp = [W for W in Ws if S <= W]
            if not comp:
                continue
            for j in range(m):
                if j in S:
                    post = F(sum(1 for W in comp if j in W), len(comp))
                    if post != 1:
                        raise AssertionError(f"a seen tip is not certainly unsafe: {j}")
                    continue
                post = F(sum(1 for W in comp if j in W), len(comp))
                claim = F(b - s, m - s)
                if post != claim:
                    bad += 1
                    print(f"  MISMATCH m={m} b={b} S={sorted(S)} j={j}: "
                          f"{post} vs {claim}")
    return bad


# ------------------------------------------------------------- U3 passive risk
def check_passive(m, b, p, N):
    """ORDERED-TRANSCRIPT enumeration. No sufficient-statistic shortcut, no
    inclusion-exclusion, and -- this is the point -- the Bayes value is obtained by
    MINIMISING over the decision, not by re-adding the policy's own expression.

    Sample space: sequences in ({anchor} u {0..m-1})^N. Joint mass of (W, x) is
    prior(W) * prod_i P(x_i | W), with P(anchor|W) = 1 - b p and P(j|W) = p for
    j in W, 0 otherwise. Everything below is a mass, never a conditional, so no
    division by P(x) is needed and no transcript has to be renormalised.

    Returns (bayes, policy, flat, per_world, mass):
      bayes    sum_x min_j  P(x, j in W)                  -- Bayes optimum
      policy   sum_x mean_{j unseen} P(x, j in W)         -- uniform-unseen policy
      flat     sum_x mean_{j in all m}  P(x, j in W)      -- negative control
      per_world  W -> conditional risk of the policy given W (Bayes -> minimax)
      mass     sum_x P(x); must be exactly 1
    """
    p = F(p)
    anchor = 1 - b * p
    Ws = worlds(m, b)
    prior = F(1, len(Ws))
    syms = [None] + list(range(m))
    bayes = F(0)
    policy = F(0)
    flat = F(0)
    mass = F(0)
    per_world = {W: F(0) for W in Ws}
    for x in itertools.product(syms, repeat=N):
        T = set(s for s in x if s is not None)
        ndraw = sum(1 for s in x if s is not None)
        joint = {}
        for W in Ws:
            if not T <= W:
                continue
            joint[W] = prior * anchor ** (N - ndraw) * p ** ndraw
        if not joint:
            continue
        mass += sum(joint.values())
        # error mass of declaring decision j safe, for each j
        err = [sum(v for W, v in joint.items() if j in W) for j in range(m)]
        bayes += min(err)                                   # <-- the minimisation
        unseen = [j for j in range(m) if j not in T]
        if not unseen:
            raise AssertionError("no unseen decision; a >= 1 is required")
        policy += sum(err[j] for j in unseen) / F(len(unseen))
        flat += sum(err) / F(m)
        # conditional risk given W: same average, but with the W-slice of the mass
        for W, v in joint.items():
            per_world[W] += sum(v for j in unseen if j in W) / F(len(unseen)) / prior
    return bayes, policy, flat, per_world, mass


def passive_expression(m, b, p, N):
    """E[L_N/(a+L_N)] computed directly from the occupancy law."""
    a = m - b
    anchor = 1 - b * p
    tot = F(0)
    for k in range(b + 1):
        # P(exactly k distinct tips seen) by inclusion-exclusion
        prob = F(0)
        for drop in range(k + 1):
            prob += (F((-1) ** drop) * math.comb(k, drop)
                     * (anchor + (k - drop) * p) ** N)
        prob *= math.comb(b, k)
        tot += prob * F(b - k, a + (b - k))
    return tot


# -------------------------------------------------------------- U5 active risk
def active_minimax(m, b, k):
    """Bayes-optimal error over ALL deterministic adaptive trees of depth <= k,
    under the uniform prior on b-subsets. Enumerated, not assumed."""
    Ws = worlds(m, b)

    @lru_cache(maxsize=None)
    def best(asked, unsafe, budget):
        comp = [W for W in Ws
                if all((i in W) == (i in unsafe) for i in asked)]
        n = len(comp)
        if n == 0:
            return F(0)
        stop = min(F(sum(1 for W in comp if j in W), n) for j in range(m))
        if budget == 0:
            return stop
        val = stop
        for i in range(m):
            if i in asked:
                continue
            nu = sum(1 for W in comp if i in W)
            ns = n - nu
            e = F(0)
            if nu:
                e += F(nu, n) * best(asked | {i}, unsafe | {i}, budget - 1)
            if ns:
                e += F(ns, n) * best(asked | {i}, unsafe, budget - 1)
            if e < val:
                val = e
        return val

    return best(frozenset(), frozenset(), k)


def main():
    print("U2  posterior on the unseen coordinates")
    bad = 0
    for m, b in ((5, 2), (6, 3), (7, 3), (7, 4)):
        bad += check_posterior(m, b)
        print(f"   m={m} b={b}: Pr(j in W | S) = (b-s)/(m-s) verified for every S, j")
    if bad:
        raise AssertionError(f"{bad} posterior mismatches")

    print("\nU3  passive risk: ordered-transcript Bayes optimum, the uniform-unseen")
    print("    policy, and the closed form E[L/(a+L)] -- three separate routes")
    u3 = []
    for m, b, p, N in ((5, 2, F(1, 4), 3), (6, 3, F(1, 6), 4), (7, 3, F(1, 8), 5)):
        bayes, policy, flat, per_world, mass = check_passive(m, b, p, N)
        rhs = passive_expression(m, b, p, N)
        if mass != 1:
            raise AssertionError(f"transcript masses sum to {mass}, not 1")
        if policy != rhs:
            raise AssertionError("uniform-unseen policy does not attain the expression")
        if bayes != policy:
            raise AssertionError("the uniform-unseen policy is NOT Bayes-optimal")
        risks = set(per_world.values())
        if len(risks) != 1:
            raise AssertionError(f"policy risk is not constant in W: {sorted(risks)}")
        if not (flat > bayes):
            raise AssertionError("negative control failed: the minimisation is inert")
        print(f"   m={m} b={b} p={p} N={N}: Bayes {bayes} == policy {policy} "
              f"== E[L/(a+L)] {rhs}; mass 1; risk constant in W = {risks.pop()}; "
              f"uniform-over-all control {flat} > {bayes}")
        u3.append({"m": m, "b": b, "p": str(p), "N": N, "bayes_risk": str(bayes),
                   "uniform_unseen_policy_risk": str(policy),
                   "closed_form_E_L_over_a_plus_L": str(rhs),
                   "uniform_over_all_control": str(flat),
                   "total_transcript_mass": str(mass)})

    print("\nU5  active minimax over all deterministic adaptive trees")
    for m, b in ((5, 2), (6, 3), (7, 3)):
        a = m - b
        for k in range(0, min(b, 3) + 1):
            got = active_minimax(m, b, k)
            claim = F(math.comb(b, k + 1), math.comb(a + b, k + 1))
            ok = got == claim
            print(f"   m={m} b={b} k={k}: enumerated {got} "
                  f"{'==' if ok else '!='} C(b,k+1)/C(m,k+1) = {claim}")
            if not ok:
                raise AssertionError("the active law is not the enumerated optimum")

    out = Path("research/worker_U_minimax_20260914/U1_support_minimax_check.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "claims": {
            "U2": "posterior uniform on b-subsets containing the seen set; "
                  "Pr(j in W | S) = (b-s)/(m-s) for unseen j",
            "U3": "the uniform-unseen policy attains E[L_N/(a+L_N)] exactly AND "
                  "equals the Bayes optimum, which is obtained by minimising over "
                  "the decision on each ordered transcript (not by re-adding the "
                  "policy's own expression); its conditional risk is constant in W, "
                  "which is what turns Bayes into minimax",
            "U5": "C(b,k+1)/C(a+b,k+1) is the Bayes optimum over ALL deterministic "
                  "adaptive query trees of depth k, enumerated",
        },
        "arithmetic": "exact Fraction; inclusion-exclusion for the occupancy law; "
                      "full memoised tree enumeration for the active branch",
        "configurations": "m in {5,6,7}, b in {2,3,4}, N in {3,4,5}, k <= 3",
        "scope": "small m only. For U3 the Bayes value is a genuine per-transcript "
                 "minimisation over all m decisions on the ORDERED sample space, the "
                 "total transcript mass is verified to be exactly 1, the policy's "
                 "conditional risk is verified constant across worlds, and a "
                 "uniform-over-all-decisions control is verified strictly worse. "
                 "For U5 the BAYES value is enumerated over all deterministic trees; "
                 "the step from Bayes to MINIMAX there is an argument, not an "
                 "enumeration.",
        "U3_results": u3,
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
