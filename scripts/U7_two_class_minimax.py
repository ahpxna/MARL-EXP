#!/usr/bin/env python3
"""Support target B: two classes with DIFFERENT tip masses -- is deciding safely
exponentially cheaper than learning the support?

`U6_support_unequal_masses.py` showed the equal-mass law does not survive unequal
masses at all. This is the specific family worth proving, with a candidate exact law:

  labels split into two classes; class i has a_i safe labels and b_i unsafe ones, and
  every unsafe tip of class i carries mass p_i. The composition (b_1, b_2) is KNOWN;
  which subset of each class is unsafe is not. Then

      R_N^*  =  E min{ L_1/(a_1+L_1),  L_2/(a_2+L_2) },      L_i = unseen unsafe in i.

WHY IT SHOULD BE TRUE, and what is checked here rather than assumed:
  * the posterior is uniform WITHIN each class, so for an unseen label j of class i,
    Pr(j unsafe | transcript) = L_i/(a_i+L_i), and for a seen label it is 1;
  * hence the per-transcript Bayes-optimal error is min over i of L_i/(a_i+L_i),
    attained by naming an unseen label of whichever class has the smaller ratio;
  * the product permutation group (permute inside class 1, permute inside class 2)
    makes that decoder's risk the same in EVERY world, which turns Bayes into minimax.
All three are computed, not asserted: the Bayes value comes from a genuine per-
transcript minimisation over all m labels on the ORDERED sample space, the total
transcript mass is checked to be exactly 1, and the per-world risks are compared.

THE SEPARATION. The event that no safe decision is certain needs an unseen unsafe tip
in BOTH classes, whose dominant term is b_1 b_2 (1-p_1-p_2)^N, while merely having
some unsafe tip unseen decays like (1-min{p_1,p_2})^N. So

      R_N^*  ~  b_1 b_2 min{1/(a_1+1), 1/(a_2+1)} (1-p_1-p_2)^N
      P(support not fully seen)  ~  (1 - min{p_1,p_2})^N,

a strictly faster exponent for deciding than for learning. Both sides are computed in
exact rationals at growing N from the occupancy law (not by enumeration), and the
ratio to the predicted leading term is reported so the reader sees the remainder.

WHAT THIS DOES NOT ESTABLISH
 - Exact on the listed (a_1,b_1,a_2,b_2,p_1,p_2,N); a candidate law confirmed on
   instances, not a theorem. No Lean module.
 - The Bayes-to-minimax step is checked through the per-world risks, not proved.
 - The asymptotic claim is checked as a RATIO tending to 1 over a finite range of N;
   finitely many points cannot establish a limit, and the ratios are printed so that
   is visible.

    .venv/bin/python scripts/U7_two_class_minimax.py
"""
from __future__ import annotations

from fractions import Fraction as F
import itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def analyse(a1, b1, a2, b2, p1, p2, N):
    """Exact, over ORDERED transcripts. Labels 0..m-1; class 1 is the first a1+b1."""
    n1, n2 = a1 + b1, a2 + b2
    m = n1 + n2
    cls = [0] * n1 + [1] * n2
    p = [p1, p2]
    W1 = list(itertools.combinations(range(n1), b1))
    W2 = list(itertools.combinations(range(n1, m), b2))
    worlds = [frozenset(u) | frozenset(v) for u in W1 for v in W2]
    prior = F(1, len(worlds))
    anchor = 1 - b1 * p1 - b2 * p2
    if anchor < 0:
        raise ValueError("tip masses exceed 1")
    syms = [None] + list(range(m))
    bayes = policy = formula = mass = F(0)
    per_world = {W: F(0) for W in worlds}
    for x in itertools.product(syms, repeat=N):
        T = set(s for s in x if s is not None)
        joint = {}
        for W in worlds:
            if not T <= W:
                continue
            v = prior
            for s in x:
                v *= anchor if s is None else p[cls[s]]
            joint[W] = v
        if not joint:
            continue
        mass += sum(joint.values())
        err = [sum(v for W, v in joint.items() if j in W) for j in range(m)]
        bayes += min(err)
        # the candidate decoder: unseen label of the class with the smaller ratio
        s1 = len(T & set(range(n1)))
        s2 = len(T & set(range(n1, m)))
        L1, L2 = b1 - s1, b2 - s2
        r1, r2 = F(L1, a1 + L1), F(L2, a2 + L2)
        pick_cls = 0 if r1 <= r2 else 1
        rng = range(n1) if pick_cls == 0 else range(n1, m)
        unseen = [j for j in rng if j not in T]
        if not unseen:
            unseen = [j for j in range(m) if j not in T]
        policy += sum(err[j] for j in unseen) / F(len(unseen))
        formula += sum(joint.values()) * min(r1, r2)
        for W, v in joint.items():
            per_world[W] += sum(v for j in unseen if j in W) / F(len(unseen)) / prior
    return bayes, policy, formula, mass, per_world


def occupancy_exact(a1, b1, a2, b2, p1, p2, N):
    """E min{L1/(a1+L1), L2/(a2+L2)} from the occupancy law, no enumeration:
    the unseen counts are determined by which tips were missed, and by symmetry the
    probability that a given set of tips is jointly missed is (1 - sum of their
    masses)^N, so inclusion-exclusion over (L1, L2) is exact."""
    import math
    tot = F(0)
    for k1 in range(b1 + 1):
        for k2 in range(b2 + 1):
            # P(exactly k1 tips of class 1 and k2 of class 2 are MISSED)
            pr = F(0)
            for j1 in range(k1, b1 + 1):
                for j2 in range(k2, b2 + 1):
                    sgn = (-1) ** (j1 - k1 + j2 - k2)
                    pr += (F(sgn) * math.comb(j1, k1) * math.comb(j2, k2)
                           * math.comb(b1, j1) * math.comb(b2, j2)
                           * (1 - j1 * p1 - j2 * p2) ** N)
            tot += pr * min(F(k1, a1 + k1), F(k2, a2 + k2))
    return tot


def support_incomplete(b1, b2, p1, p2, N):
    """P(some unsafe tip never appeared), by inclusion-exclusion."""
    import math
    tot = F(0)
    for j1 in range(b1 + 1):
        for j2 in range(b2 + 1):
            if j1 + j2 == 0:
                continue
            tot += (F((-1) ** (j1 + j2 + 1)) * math.comb(b1, j1) * math.comb(b2, j2)
                    * (1 - j1 * p1 - j2 * p2) ** N)
    return tot


def main():
    print("Support: two classes with different tip masses\n")
    print("PART 1 -- the candidate exact law, by ordered-transcript enumeration")
    rows = []
    cfgs = [(1, 1, 1, 1, F(1, 4), F(1, 8), 2),
            (1, 1, 1, 1, F(1, 3), F(1, 9), 3),
            (2, 1, 1, 1, F(1, 4), F(1, 10), 3),
            (1, 2, 2, 1, F(1, 5), F(1, 12), 2),
            (1, 1, 2, 2, F(2, 7), F(1, 9), 2)]
    for (a1, b1, a2, b2, p1, p2, N) in cfgs:
        bayes, policy, formula, mass, pw = analyse(a1, b1, a2, b2, p1, p2, N)
        risks = sorted(set(pw.values()))
        occ = occupancy_exact(a1, b1, a2, b2, p1, p2, N)
        if mass != 1:
            raise AssertionError(f"transcript masses sum to {mass}")
        ok_law = (bayes == formula)
        ok_pol = (policy == bayes)
        ok_const = (len(risks) == 1)
        ok_occ = (occ == formula)
        print(f"   (a1,b1,a2,b2)=({a1},{b1},{a2},{b2}) p=({p1},{p2}) N={N}")
        print(f"      Bayes {bayes}   E min{{L1/(a1+L1),L2/(a2+L2)}} {formula}"
              f"   {'MATCH' if ok_law else 'DIFFER'}")
        print(f"      uniform-unseen-in-better-class policy {policy}"
              f"   {'optimal' if ok_pol else 'NOT optimal'}")
        print(f"      per-world risk {'constant' if ok_const else str(len(risks)) + ' values'}"
              f"   |   occupancy-law recomputation {'agrees' if ok_occ else 'DIFFERS'}")
        for nm, flag in (("law", ok_law), ("policy", ok_pol),
                         ("constant risk", ok_const), ("occupancy", ok_occ)):
            if not flag:
                raise AssertionError(f"{nm} FAILS at {(a1,b1,a2,b2,str(p1),str(p2),N)}")
        rows.append({"a1": a1, "b1": b1, "a2": a2, "b2": b2,
                     "p1": str(p1), "p2": str(p2), "N": N,
                     "bayes": str(bayes), "formula": str(formula),
                     "policy": str(policy), "law_holds": ok_law,
                     "policy_optimal": ok_pol, "risk_constant": ok_const,
                     "occupancy_agrees": ok_occ})
    print("   => the candidate law, the policy's optimality and the constancy of the")
    print("      per-world risk all hold exactly on every configuration tried, and an")
    print("      independent occupancy-law computation reproduces the same number.\n")

    print("PART 2 -- the two exponents: deciding versus learning the support")
    exps = []
    for (a1, b1, a2, b2, p1, p2) in [(1, 2, 2, 1, F(1, 5), F(1, 12)),
                                     (2, 2, 3, 2, F(1, 6), F(1, 20)),
                                     (1, 3, 1, 2, F(1, 8), F(1, 25))]:
        lead = b1 * b2 * min(F(1, a1 + 1), F(1, a2 + 1))
        base_dec = 1 - p1 - p2
        base_lrn = 1 - min(p1, p2)
        print(f"   (a1,b1,a2,b2)=({a1},{b1},{a2},{b2}) p=({p1},{p2}):"
              f"  decide base {float(base_dec):.6f}  learn base {float(base_lrn):.6f}")
        print(f"      {'N':>3} {'R_N*':>14} {'/ predicted':>12} "
              f"{'P(support unseen)':>18} {'ratio R/P':>12}")
        row = {"a1": a1, "b1": b1, "a2": a2, "b2": b2, "p1": str(p1), "p2": str(p2),
               "leading_coefficient": str(lead),
               "decide_base": str(base_dec), "learn_base": str(base_lrn), "N": []}
        for N in (4, 8, 12, 16, 20, 30):
            R = occupancy_exact(a1, b1, a2, b2, p1, p2, N)
            S = support_incomplete(b1, b2, p1, p2, N)
            pred = lead * base_dec ** N
            print(f"      {N:>3} {float(R):14.6e} {float(R / pred):12.6f} "
                  f"{float(S):18.6e} {float(R / S):12.3e}")
            row["N"].append({"N": N, "R": str(R), "R_over_predicted": float(R / pred),
                             "support_incomplete": str(S),
                             "R_over_support_incomplete": float(R / S)})
        exps.append(row)
        print()

    print("VERDICT")
    print("   The exact law holds on every configuration checked, with an independent")
    print("   occupancy recomputation agreeing, so it is a well-supported CANDIDATE.")
    print("   The ratio R_N*/predicted approaches 1 and R_N*/P(support unseen) goes to")
    print("   0, i.e. deciding safely is exponentially cheaper than learning the")
    print("   support -- with the caveat that a finite ladder of N cannot establish a")
    print("   limit; the ratios are printed so the trend is visible rather than")
    print("   asserted.")

    out = REPO / "research/worker_U7_support_20260914/U7_two_class_minimax.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "candidate_law": "R_N* = E min{L_1/(a_1+L_1), L_2/(a_2+L_2)}",
        "exact_checks": rows,
        "exponents": exps,
        "not_established": [
            "exact on the listed configurations; a candidate confirmed on instances, "
            "not a theorem, and no Lean module",
            "the Bayes-to-minimax step is checked through the per-world risks, not "
            "proved",
            "the asymptotic claim is a finite ladder of N; the ratios are reported "
            "rather than a limit being claimed",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
