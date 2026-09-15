#!/usr/bin/env python3
"""Support, high-risk probe: is the equal-tip-mass hypothesis in `passive_minimax`
essential, or cosmetic?

`work/p13_conjectures/LeanSupportBayesMinimaxV1.lean` proves

    R_N^* = E[L_N/(a+L_N)],   attained by the uniform-on-unseen decoder,

with EVERY tip carrying the same mass p. That hypothesis sits in `draw`, so the
theorem says nothing about unequal masses. This script decides, by exact
enumeration, whether the law survives -- and if not, WHICH of its three parts fails.

MODEL. m = a + b labels, the hidden world W is a b-subset, uniform prior. Label i
carries mass p_i whenever i is unsafe in the present world; the anchor carries
1 - sum_{i in W} p_i, which now DEPENDS ON W. So the likelihood of a transcript
depends on W through more than the indicator {S subset W}, and the posterior has no
reason to stay uniform on the consistent worlds.

WHAT IS COMPUTED, exactly, over ORDERED transcripts:
  bayes     sum_x min_j  P(x, j in W)                    -- the true Bayes value
  policy    sum_x mean_{j unseen} P(x, j in W)           -- the uniform-unseen rule
  formula   E[L_N/(a+L_N)]                               -- the equal-mass law
  worlds    the conditional risk of the policy in each world (constant <=> minimax)
plus the total transcript mass, which must be exactly 1.

A POSITIVE CONTROL runs the same code with equal masses and must reproduce
bayes == policy == formula and a constant per-world risk, i.e. the theorem.

WHAT THIS DOES NOT ESTABLISH
 - Exact on the listed (m, b, p, N) only. A separation on one instance refutes the
   general law; agreement on these instances would not prove it.
 - The Bayes value is a minimisation over decisions per transcript; the step from
   Bayes to minimax needs the per-world risks, which are reported but whose
   constancy is checked, not proved.

    .venv/bin/python scripts/U6_support_unequal_masses.py
"""
from __future__ import annotations

from fractions import Fraction as F
import itertools, json
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


def analyse(m, b, p, N):
    """p: list of m masses. Returns the four quantities plus the mass check."""
    a = m - b
    Ws = [frozenset(c) for c in itertools.combinations(range(m), b)]
    for W in Ws:
        if sum(p[i] for i in W) > 1:
            raise ValueError(f"world {sorted(W)} has total tip mass > 1")
    prior = F(1, len(Ws))
    syms = [None] + list(range(m))
    bayes = F(0); policy = F(0); formula = F(0); mass = F(0)
    per_world = {W: F(0) for W in Ws}
    for x in itertools.product(syms, repeat=N):
        T = set(s for s in x if s is not None)
        joint = {}
        for W in Ws:
            if not T <= W:
                continue
            anchor = 1 - sum(p[i] for i in W)
            v = prior
            for s in x:
                v *= anchor if s is None else p[s]
            if v:
                joint[W] = v
        if not joint:
            continue
        mass += sum(joint.values())
        err = [sum(v for W, v in joint.items() if j in W) for j in range(m)]
        bayes += min(err)
        unseen = [j for j in range(m) if j not in T]
        if not unseen:
            raise AssertionError("no unseen label; a >= 1 required")
        policy += sum(err[j] for j in unseen) / F(len(unseen))
        for W, v in joint.items():
            L = len(W - T)
            formula += v * F(L, a + L)
            per_world[W] += sum(v for j in unseen if j in W) / F(len(unseen)) / prior
    return bayes, policy, formula, mass, per_world


def show(tag, m, b, p, N):
    bayes, policy, formula, mass, per_world = analyse(m, b, p, N)
    risks = sorted(set(per_world.values()))
    const = (len(risks) == 1)
    print(f"{tag}: m={m} b={b} N={N} p={[str(v) for v in p]}")
    print(f"   total transcript mass      {mass}")
    print(f"   Bayes optimum              {bayes}  = {float(bayes):.9f}")
    print(f"   uniform-unseen policy      {policy}  = {float(policy):.9f}"
          f"   {'(optimal)' if policy == bayes else '(NOT optimal)'}")
    print(f"   E[L_N/(a+L_N)]             {formula}  = {float(formula):.9f}"
          f"   {'(equals Bayes)' if formula == bayes else '(DIFFERS from Bayes)'}")
    print(f"   per-world policy risk      {'constant = ' + str(risks[0]) if const else str(len(risks)) + ' distinct values: ' + ', '.join(str(r) for r in risks[:4])}")
    if mass != 1:
        raise AssertionError(f"masses sum to {mass}")
    return {"tag": tag, "m": m, "b": b, "N": N, "p": [str(v) for v in p],
            "bayes": str(bayes), "policy": str(policy), "formula": str(formula),
            "policy_is_optimal": policy == bayes,
            "formula_equals_bayes": formula == bayes,
            "per_world_risk_constant": const,
            "per_world_risks": [str(r) for r in risks]}


def main():
    rows = []
    print("POSITIVE CONTROL -- equal masses, where the theorem applies\n")
    rows.append(show("equal", 5, 2, [F(1, 4)] * 5, 3))
    print()
    rows.append(show("equal", 6, 3, [F(1, 6)] * 6, 3))
    ctrl = rows[:]
    for r in ctrl:
        if not (r["policy_is_optimal"] and r["formula_equals_bayes"]
                and r["per_world_risk_constant"]):
            raise AssertionError("the equal-mass control does not reproduce the "
                                 "theorem; the enumeration is wrong")
    print("\n   control passes: with equal masses the three agree and the per-world")
    print("   risk is constant, which is exactly `passive_minimax`.\n")

    print("UNEQUAL MASSES\n")
    rows.append(show("unequal, mild", 5, 2, [F(1, 4), F(1, 5), F(1, 6), F(1, 8),
                                             F(1, 10)], 3))
    print()
    rows.append(show("unequal, sharp", 5, 2, [F(1, 2), F(1, 3), F(1, 20),
                                              F(1, 40), F(1, 50)], 3))
    print()
    rows.append(show("unequal, sharp", 6, 3, [F(1, 3), F(1, 4), F(1, 30),
                                              F(1, 40), F(1, 50), F(1, 60)], 3))
    print()
    rows.append(show("unequal, two scales", 6, 2, [F(2, 5), F(2, 5), F(1, 50),
                                                   F(1, 50), F(1, 50), F(1, 50)], 4))

    ue = [r for r in rows if r["tag"] != "equal"]
    broke_policy = [r for r in ue if not r["policy_is_optimal"]]
    broke_formula = [r for r in ue if not r["formula_equals_bayes"]]
    broke_const = [r for r in ue if not r["per_world_risk_constant"]]
    print("\nVERDICT")
    print(f"   uniform-unseen still optimal : "
          f"{len(ue) - len(broke_policy)}/{len(ue)} unequal instances")
    print(f"   E[L/(a+L)] still the value   : "
          f"{len(ue) - len(broke_formula)}/{len(ue)} unequal instances")
    print(f"   per-world risk still constant: "
          f"{len(ue) - len(broke_const)}/{len(ue)} unequal instances")
    if broke_formula or broke_policy or broke_const:
        print("   => the equal-mass hypothesis in `passive_minimax` is ESSENTIAL, not")
        print("      cosmetic. Each part that fails above fails on an explicit,")
        print("      exactly-computed instance.")
    else:
        print("   => no separation found on these instances. That is NOT a proof that")
        print("      the law extends; it only says these instances do not refute it.")

    out = REPO / "research/worker_U_minimax_20260914/U6_support_unequal_masses.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({
        "question": "does R_N* = E[L_N/(a+L_N)] survive unequal tip masses?",
        "model": "label i carries mass p_i when unsafe; the anchor carries "
                 "1 - sum_{i in W} p_i, so the likelihood depends on W beyond the "
                 "indicator {S subset W}",
        "rows": rows,
        "not_established": [
            "exact on the listed instances only; a separation refutes the general "
            "law, agreement would not prove it",
            "the Bayes-to-minimax step is checked through the per-world risks, not "
            "proved",
        ],
    }, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
