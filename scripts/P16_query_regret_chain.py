#!/usr/bin/env python3
"""Query step 5: from the testing bound BACK to the regret of a real decision.

A testing theorem is not the end of the Query chain.  `P9`/`P15` give
    (1/4) rho^{2N} <= e*_N <= (1/2) rho^N,   rho = 1 - H^2 ~ 1 - c h^{2r},
which is about labelling the world.  What the paper claims is about DECIDING: the
algorithm outputs a retained set, and pays the corpus's own `productCompressionLoss`.
This file closes that last link on the real geometry.

THE REDUCTION.  With l_W(a) = loss_W(a) - min_{a'} loss_W(a') the regret in world W,
put G_W(gamma) = {a : l_W(a) < gamma}.  If gamma is small enough that
G_A(gamma) ∩ G_B(gamma) = empty, then any decision algorithm induces a binary test --
"say A if the decision lies in G_A, else say B" -- and a MISLABEL forces a decision
outside the true world's good set, hence regret at least gamma.  Therefore
    (E_A l_A + E_B l_B)/2  >=  gamma * e*_N  >=  (gamma/4) rho^{2N}.
In the other direction the likelihood-ratio test picks between the two worlds' own
optimal decisions, and an error costs at most the CROSS-WORLD loss
L_max = max(l_B(a_A*), l_A(a_B*)), so
    (E_A l_A + E_B l_B)/2  <=  L_max * e*_N  <=  (L_max/2) rho^N.

Everything about the geometry -- gamma, L_max, the two good sets, their disjointness
-- is computed here in exact rationals from `G4.compression_loss`, the corpus's own
loss.  Nothing is assumed about the decision space.

WHAT THIS DOES NOT ESTABLISH
  * The chain arithmetic is `LeanQueryRegretChainV1`; the testing bracket is
    `LeanQueryAffinityTestingV1`; the rate constants are measured in P15.  This file
    supplies the geometric constants and checks the reduction's hypotheses.
  * `E_A`, `E_B` are expectations over the transcript; no algorithm is simulated.
    The statement proved is the INEQUALITY chain, not a claim about any particular
    learner.
  * One pair of worlds and one budget grid.

    .venv/bin/python scripts/P16_query_regret_chain.py
"""
from __future__ import annotations
import importlib.util, json, math
from fractions import Fraction as F
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("p5", REPO / "scripts/P5_query_h4_robustness.py")
p5 = importlib.util.module_from_spec(spec); spec.loader.exec_module(p5)
g4 = p5.g4


def main():
    print("Query: the testing bound carried back to the regret of a real decision\n")
    k, t0, rho_par = 3, F(1, 8), F(1)
    cfg = g4.make_cfg(k, t0, rho_par)
    A, B = frozenset({0, 1, 3}), frozenset({0, 2, 3})
    res = {"k": k, "t0": str(t0), "A": sorted(A), "B": sorted(B), "budgets": []}

    tabs = {}
    for W in (A, B):
        Fw = g4.world_fn(cfg, W)
        Qw = {i: g4.response_levels(cfg, Fw, i) for i in range(cfg["m"])}
        tabs[W] = (Fw, Qw)

    for budget in (1, 2, 3):
        decs = g4.decisions(cfg, budget)
        loss = {W: {S: g4.compression_loss(cfg, tabs[W][0], tabs[W][1], S)
                    for S in decs} for W in (A, B)}
        opt = {W: min(loss[W].values()) for W in (A, B)}
        reg = {W: {S: loss[W][S] - opt[W] for S in decs} for W in (A, B)}
        # the largest gamma keeping the two good sets disjoint: the smallest value of
        # max(l_A(a), l_B(a)) over decisions -- above it some a is good in both
        worst_common = min(max(reg[A][S], reg[B][S]) for S in decs)
        gamma = worst_common
        GA = [S for S in decs if reg[A][S] < gamma]
        GB = [S for S in decs if reg[B][S] < gamma]
        disjoint = not (set(GA) & set(GB))
        if gamma == 0:
            print(f"   budget {budget}: gamma = 0 -- some decision is optimal in BOTH "
                  f"worlds, so no separation is possible at this budget.  Skipped.")
            res["budgets"].append({"budget": budget, "gamma": "0",
                                   "separable": False,
                                   "n_decisions": len(decs)})
            continue
        if not disjoint:
            raise AssertionError("good sets are not disjoint at the chosen gamma")
        aA = min(decs, key=lambda S: (reg[A][S], sorted(S)))
        aB = min(decs, key=lambda S: (reg[B][S], sorted(S)))
        Lmax = max(reg[B][aA], reg[A][aB])
        # the hypothesis the reduction needs, checked on EVERY decision
        for S in decs:
            if S not in GA and reg[A][S] < gamma:
                raise AssertionError("good-set membership is inconsistent")
            if S not in GA and S not in GB:
                # outside both: costs at least gamma in both worlds
                if not (reg[A][S] >= gamma and reg[B][S] >= gamma):
                    raise AssertionError("a decision outside both sets is cheap")
        print(f"   budget {budget}: {len(decs)} decisions; gamma = {gamma} = "
              f"{float(gamma):.6f}; |G_A| = {len(GA)}, |G_B| = {len(GB)}, "
              f"disjoint = {disjoint}")
        print(f"      optimal decisions a_A* = {sorted(aA)}, a_B* = {sorted(aB)}; "
              f"cross-world L_max = {Lmax} = {float(Lmax):.6f}")
        print(f"      so  (gamma/4) rho^{{2N}} <= avg regret <= (L_max/2) rho^N, "
              f"a window of ratio {float(2*Lmax/gamma):.3f} x rho^{{-N}}")
        res["budgets"].append({
            "budget": budget, "n_decisions": len(decs), "gamma": str(gamma),
            "gamma_float": float(gamma), "L_max": str(Lmax),
            "L_max_float": float(Lmax), "separable": True,
            "G_A_size": len(GA), "G_B_size": len(GB), "disjoint": disjoint,
            "a_A_star": sorted(aA), "a_B_star": sorted(aB),
            "lower_constant": float(gamma / 4), "upper_constant": float(Lmax / 2)})

    print("\n   instantiating with the Hellinger constants measured in P15")
    p15 = REPO / "research/worker_P15_query_20260915/P15_query_hellinger_order.json"
    sep = [b for b in res["budgets"] if b.get("separable")]
    if p15.exists() and sep:
        q = json.loads(p15.read_text())
        rows = []
        for name, blk in q.items():
            if not isinstance(blk, dict) or "c_minus" not in blk:
                continue
            r = blk["order"]
            cm, cp = blk["c_minus"], blk["c_plus"]
            b0 = sep[0]
            gam, Lm = b0["gamma_float"], b0["L_max_float"]
            for h in (0.1, 0.025):
                # rho = 1 - H^2, H^2 in [cm h^2r, cp h^2r]; use L = -log rho in
                # [H^2, 2H^2] to bracket the N at which each side hits a target
                target = 1e-3
                Nlo = math.log(gam / (4 * target)) / (4 * cp * h ** (2 * r))
                Nhi = math.ceil(math.log(Lm / (2 * target)) / (cm * h ** (2 * r)))
                rows.append({"measurement": name, "order": r, "h": h,
                             "target_avg_regret": target,
                             "N_necessary_lower": Nlo, "N_sufficient_upper": Nhi})
                print(f"      {name[:22]:22s} h={h}: to drive the average regret "
                      f"below {target}, N >= {Nlo:.4g} is necessary and "
                      f"N <= {Nhi:.4g} suffices  (both Theta(h^-{2*r}))")
        res["instantiated"] = rows
    res["not_established"] = [
        "the chain arithmetic is LeanQueryRegretChainV1; the testing bracket is "
        "LeanQueryAffinityTestingV1; the rate constants are MEASURED in P15",
        "E_A, E_B are expectations over the transcript; no algorithm is simulated",
        "one pair of worlds, one budget grid",
        "gamma is the largest value keeping the good sets disjoint; at budgets where "
        "it is 0 the two worlds share an optimal decision and no separation exists",
    ]
    out = REPO / "research/worker_P16_query_20260915/P16_query_regret_chain.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(res, indent=2) + "\n")
    print(f"\n-> {out}")


if __name__ == "__main__":
    main()
