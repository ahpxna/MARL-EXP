import Mathlib

/-! # Query step 5: carrying the testing bound back to the REGRET of a real decision.

`LeanQueryAffinityTestingV1` bounds the error of the best TEST.  The paper's claim is
about DECIDING: the algorithm outputs a retained set and pays the corpus's own
`productCompressionLoss`.  `scripts/P16_query_regret_chain.py` computes the geometry
on the real worlds -- at budget 1 the two good sets are disjoint with
`gamma = 13983/32768 = 0.4267` and the cross-world loss is `L_max = 2401/4096 =
0.5862` -- and this file proves the arithmetic that turns those two numbers plus the
testing bracket into a two-sided regret bound.

## WHAT IS PROVED

* `mislabel_costs` — if the two good sets are disjoint, then for EVERY decision `a`,
  either `gamma ≤ l_A a` or `gamma ≤ l_B a`: no single decision is cheap in both
  worlds.  This is the reduction: an algorithm that gets the world wrong is paying
  at least `gamma` in the true world.
* `regret_lower_rate` — with the induced test's error `e` and `rho^{2N}/4 ≤ e`,
      gamma * rho^{2N} / 4  ≤  average regret.
* `regret_upper_rate` — with `e ≤ rho^N/2` and the likelihood-ratio test's cross-world
  cost `L_max`,
      average regret  ≤  L_max * rho^N / 2.
* `regret_window` — both at once, so the regret is pinned between two powers of the
  same `rho`, with the two constants read off the geometry.

## WHAT THIS DOES NOT ESTABLISH

- `e`, and the two inequalities that bracket it, come from
  `LeanQueryAffinityTestingV1`; they are hypotheses here.
- `gamma * e ≤ R` and `R ≤ L_max * e` are the reduction's two steps stated as
  hypotheses: the first needs the algorithm's decision to land outside the true
  world's good set whenever the induced test errs, the second needs the LRT to output
  the erring world's own optimal decision.  `mislabel_costs` proves the geometric
  half of the first; the expectation step is not formalised.
- No algorithm is analysed, and nothing here is probabilistic.
-/

namespace CIGAMF.P13.QueryRegretChain

variable {Act : Type*}

/-- Disjoint good sets: every decision is expensive in at least one world. -/
theorem mislabel_costs (lA lB : Act → ℝ) (GA GB : Set Act) (gamma : ℝ)
    (hA : ∀ a, a ∉ GA → gamma ≤ lA a) (hB : ∀ a, a ∉ GB → gamma ≤ lB a)
    (hdis : ∀ a, ¬(a ∈ GA ∧ a ∈ GB)) (a : Act) :
    gamma ≤ lA a ∨ gamma ≤ lB a := by
  by_cases h : a ∈ GA
  · right
    exact hB a (fun hb => hdis a ⟨h, hb⟩)
  · left
    exact hA a h

theorem regret_lower_rate (gamma e R rho2N : ℝ) (hg : 0 ≤ gamma)
    (hlow : rho2N/4 ≤ e) (hR : gamma * e ≤ R) :
    gamma * rho2N / 4 ≤ R := by
  have : gamma * (rho2N/4) ≤ gamma * e := mul_le_mul_of_nonneg_left hlow hg
  linarith

theorem regret_upper_rate (Lmax e R rhoN : ℝ) (hL : 0 ≤ Lmax)
    (hup : e ≤ rhoN/2) (hR : R ≤ Lmax * e) :
    R ≤ Lmax * rhoN / 2 := by
  have : Lmax * e ≤ Lmax * (rhoN/2) := mul_le_mul_of_nonneg_left hup hL
  linarith

/-- The regret is pinned between two powers of the same affinity. -/
theorem regret_window (gamma Lmax e R rhoN rho2N : ℝ)
    (hg : 0 ≤ gamma) (hL : 0 ≤ Lmax)
    (hlow : rho2N/4 ≤ e) (hup : e ≤ rhoN/2)
    (hR1 : gamma * e ≤ R) (hR2 : R ≤ Lmax * e) :
    gamma * rho2N / 4 ≤ R ∧ R ≤ Lmax * rhoN / 2 :=
  ⟨regret_lower_rate gamma e R rho2N hg hlow hR1,
   regret_upper_rate Lmax e R rhoN hL hup hR2⟩

#print axioms mislabel_costs
#print axioms regret_lower_rate
#print axioms regret_upper_rate
#print axioms regret_window

end CIGAMF.P13.QueryRegretChain
