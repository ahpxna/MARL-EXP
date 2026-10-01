# PROGRESS: Paper C counts (2,2,1,1), g=(a,a,-a,-a,b,-b)

## Conjecture from JSON (ratios 3/2,2,3,5)
V(eta) = (a-b)/(4a+2b) * max((2-eta)/3, 2/5); breakpoint 4/5; price 5/3.

## Plan
- baselines (b,0,b,0,b) ratio-independent (parity argument)
- cost lower bound: typedCost >= |x0-x1|*(a-b)/D on box states (b=0 limit)
- dual: cert_lower with kappa cost |x0-x1|*c
- primal: mixFlow of type sequences, L0 (eta=0) and L1 (eta=4/5), mixTwo

## Discovery DONE (exact, verify_exact.py ALL OK)
- LP numerics: conjecture holds at ratios 1.001..1000, eta in [0,1.5] step 1/40 (gap ~1e-16).
- Dual band: E r1 = (a-b)(1 - P(b-item first)) >= (a-b)(1-(1+eta)/3) = (a-b)(2-eta)/3 (UPPER band side of the two b-items at k=1).
- Dual free: every order r1+..+r5 >= 2(a-b), case split on a/b type of sigma0, sigma5, sigma4/sigma1.
- Primal L0 (eta=0, dev 0, costs (2/3,1/3,2/3,1/3,2/3)(a-b)): AaaABb AaBabA aAbBAa aBAbaA BbaAAa bAAaaB, 1/6 each.
- Primal L1 (eta=4/5, dev 4/5, costs 2/5 each): AabAaB 1/5, aAaABb 1/10, aAaAbB 1/10, BaAaAb 1/5, BbaAaA 1/10, bAaBAa 1/5, bBAaaA 1/10.
  (A=+a,a=-a,B=+b,b=-b)
## Lean: writing LeanPaperCTwoMag2211V1.lean now (dual on laws, primal on mixFlow)

## STATUS at coordinator STOP (2026-09-26)
- Full Lean draft written: scratchpad c2211/lean/LeanPaperCTwoMag2211V1.lean (NOT yet compiled, NOT yet copied into work/p13_conjectures).
  Contains: baselines base1..base5, per_order, lower_band, lower_free, value_le_flow, cost_formula,
  flow0/flow1 (mixFlow) with tab0_spec/tab1_spec (decide), num0/num1, obj0_le/obj1_le, band0/band1,
  twoMag2211_frontier, twoMag2211_price, twoMag2211_etaFree.
- Only compile done: T1.lean smoke test (decide on stC/mult works; decide correctly refuted a wrong table entry).
- Next: compile the draft from work/p13_conjectures with `lake env lean <scratch path>` (no -o), fix errors,
  then copy to work/p13_conjectures/LeanPaperCTwoMag2211V1.lean and build with -o; check #print axioms.
- Riskiest tactic spots: num0/num1 finishing combinator after `simp [tab0, kap0]`; band0/band1 simp+norm_num;
  S1..S5 simp on Fin.sum_univ_six; pair_zero simp_all; odd_counts interval_cases combinator.
