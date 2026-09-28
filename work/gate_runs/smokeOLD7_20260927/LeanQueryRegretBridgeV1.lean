import Mathlib

/-! # Query: the EXPECTATION bridge `gamma·e ≤ R ≤ L_max·e`, proved.

`LeanQueryRegretChainV1` proves `mislabel_costs` (the geometric half) but takes
`gamma * e ≤ R` and `R ≤ L_max * e` as HYPOTHESES; its own "what this does not
establish" says the expectation step is not formalised.  This file integrates the
decision kernel against the two transcript laws and proves both, with the quantifiers
the reduction actually needs:

* the LOWER bound holds for **every** decision kernel `D` (all policies);
* the UPPER bound is for **one** explicit rule (a deterministic test that then plays
  the selected world's own optimal action).

Both are stated for the equal-prior Bayes average, which is what the affinity bracket
of `LeanQueryAffinityTestingV1` bounds.

## THE REDUCTION

`t h = ∑_{a ∉ G_A} D(a|h)` is the mass the kernel puts outside world `A`'s good set.
Because `G_A ∩ G_B = ∅` we have `G_A ⊆ G_Bᶜ`, so `1 - t h = ∑_{a ∈ G_A} D(a|h)` is at
most the mass outside `G_B`.  With `ℓ_W ≥ gamma` off `G_W`,

    gamma · t h      ≤ ∑_a D(a|h) ℓ_A(a),
    gamma · (1-t h)  ≤ ∑_a D(a|h) ℓ_B(a),

pointwise in the transcript.  Integrating the first against `P_A` and the second
against `P_B` and halving gives `gamma · e ≤ R`, where `e` is the error of the test
"say B iff the decision leaves `G_A`".

## WHAT IS PROVED

* `outside_cost` — the pointwise bound for world `A`.
* `inside_cost` — the pointwise bound for world `B`, using disjointness.
* `regret_ge_gamma_error` — **`gamma · e ≤ R` for every decision kernel.**
* `lrt_regret_le` — **`R ≤ L_max · e` for the rule that plays the selected world's own
  optimal action**, whose loss is `0` when the label is right and at most `L_max` when
  it is wrong.
* `bayes_regret_window` — the two together with the affinity bracket, giving
  `gamma·rho^{2N}/4 ≤ R* ≤ L_max·rho^N/2`.

## WHAT THIS DOES NOT ESTABLISH

- The transcript is a finite type here (a finite set of possible histories); nothing
  is claimed for continuous transcripts.
- `e ≥ rho^{2N}/4` and `e_LRT ≤ rho^N/2` come from `LeanQueryAffinityTestingV1`; they
  are hypotheses of `bayes_regret_window`.
- The prior is equal (Bayes risk).  This is NOT a worst-case minimax statement.
- `gamma` and `L_max` are read off the corpus geometry by
  `scripts/P16_query_regret_chain.py`; they are parameters here.
-/

namespace CIGAMF.P13.QueryRegretBridge

open Finset

variable {H Act : Type*} [Fintype H] [Fintype Act] [DecidableEq Act]

/-- Pointwise: the decision cost in world `A` is at least `gamma` times the mass the
kernel places outside `A`'s good set. -/
theorem outside_cost (D : Act → ℝ) (lA : Act → ℝ) (GA : Finset Act) (gamma : ℝ)
    (hD : ∀ a, 0 ≤ D a) (hlA : ∀ a, 0 ≤ lA a) (hA : ∀ a ∉ GA, gamma ≤ lA a) :
    gamma * (∑ a ∈ GAᶜ, D a) ≤ ∑ a, D a * lA a := by
  classical
  have h1 : gamma * (∑ a ∈ GAᶜ, D a) = ∑ a ∈ GAᶜ, D a * gamma := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h2 : ∑ a ∈ GAᶜ, D a * gamma ≤ ∑ a ∈ GAᶜ, D a * lA a :=
    Finset.sum_le_sum fun a ha =>
      mul_le_mul_of_nonneg_left (hA a (by simpa using (Finset.mem_compl.1 ha))) (hD a)
  have h3 : ∑ a ∈ GAᶜ, D a * lA a ≤ ∑ a, D a * lA a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun a _ _ => mul_nonneg (hD a) (hlA a)
  linarith [h1 ▸ h2, h3]

/-- Pointwise: the decision cost in world `B` is at least `gamma` times the mass the
kernel places INSIDE `A`'s good set -- because the good sets are disjoint. -/
theorem inside_cost (D : Act → ℝ) (lB : Act → ℝ) (GA GB : Finset Act) (gamma : ℝ)
    (hdis : Disjoint GA GB)
    (hD : ∀ a, 0 ≤ D a) (hlB : ∀ a, 0 ≤ lB a) (hB : ∀ a ∉ GB, gamma ≤ lB a) :
    gamma * (∑ a ∈ GA, D a) ≤ ∑ a, D a * lB a := by
  classical
  have hsub : ∀ a ∈ GA, a ∉ GB := fun a ha hb =>
    (Finset.disjoint_left.1 hdis) ha hb
  have h1 : gamma * (∑ a ∈ GA, D a) = ∑ a ∈ GA, D a * gamma := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have h2 : ∑ a ∈ GA, D a * gamma ≤ ∑ a ∈ GA, D a * lB a :=
    Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hB a (hsub a ha)) (hD a)
  have h3 : ∑ a ∈ GA, D a * lB a ≤ ∑ a, D a * lB a :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun a _ _ => mul_nonneg (hD a) (hlB a)
  linarith [h1 ▸ h2, h3]

/-- **The lower bound, for every decision kernel.**  `t h` is the mass outside `G_A`;
the induced test says "B" with probability `t h`, and its equal-prior error is `e`. -/
theorem regret_ge_gamma_error
    (PA PB : H → ℝ) (D : H → Act → ℝ) (lA lB : Act → ℝ) (GA GB : Finset Act)
    (gamma : ℝ)
    (hPA : ∀ h, 0 ≤ PA h) (hPB : ∀ h, 0 ≤ PB h)
    (hD : ∀ h a, 0 ≤ D h a) (hDsum : ∀ h, ∑ a, D h a = 1)
    (hlA : ∀ a, 0 ≤ lA a) (hlB : ∀ a, 0 ≤ lB a)
    (hA : ∀ a ∉ GA, gamma ≤ lA a) (hB : ∀ a ∉ GB, gamma ≤ lB a)
    (hdis : Disjoint GA GB) :
    gamma * ((∑ h, PA h * (∑ a ∈ GAᶜ, D h a)
              + ∑ h, PB h * (1 - ∑ a ∈ GAᶜ, D h a)) / 2)
      ≤ (∑ h, PA h * (∑ a, D h a * lA a)
          + ∑ h, PB h * (∑ a, D h a * lB a)) / 2 := by
  classical
  have hcompl : ∀ h : H, (1 : ℝ) - ∑ a ∈ GAᶜ, D h a = ∑ a ∈ GA, D h a := by
    intro h
    have := Finset.sum_add_sum_compl GA (D h)
    rw [hDsum h] at this
    linarith [this]
  have hstepA : ∀ h : H, PA h * (gamma * (∑ a ∈ GAᶜ, D h a))
      ≤ PA h * (∑ a, D h a * lA a) := fun h =>
    mul_le_mul_of_nonneg_left
      (outside_cost (D h) lA GA gamma (hD h) hlA hA) (hPA h)
  have hstepB : ∀ h : H, PB h * (gamma * (∑ a ∈ GA, D h a))
      ≤ PB h * (∑ a, D h a * lB a) := fun h =>
    mul_le_mul_of_nonneg_left
      (inside_cost (D h) lB GA GB gamma hdis (hD h) hlB hB) (hPB h)
  have hsumA := Finset.sum_le_sum (fun h (_ : h ∈ (univ : Finset H)) => hstepA h)
  have hsumB := Finset.sum_le_sum (fun h (_ : h ∈ (univ : Finset H)) => hstepB h)
  have hA' : ∑ h, PA h * (gamma * (∑ a ∈ GAᶜ, D h a))
      = gamma * ∑ h, PA h * (∑ a ∈ GAᶜ, D h a) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
  have hB' : ∑ h, PB h * (gamma * (∑ a ∈ GA, D h a))
      = gamma * ∑ h, PB h * (1 - ∑ a ∈ GAᶜ, D h a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [hcompl h]; ring
  rw [hA'] at hsumA
  rw [hB'] at hsumB
  have : gamma * (∑ h, PA h * (∑ a ∈ GAᶜ, D h a))
        + gamma * (∑ h, PB h * (1 - ∑ a ∈ GAᶜ, D h a))
      ≤ (∑ h, PA h * (∑ a, D h a * lA a)) + ∑ h, PB h * (∑ a, D h a * lB a) := by
    linarith [hsumA, hsumB]
  linarith [this]

/-- **The upper bound, for one explicit rule.**  A deterministic test `dec` picks a
world; the rule then plays that world's own optimal action (loss `0` there) and pays
at most `L_max` in the other world.  So the regret is at most `L_max` times the test's
error. -/
theorem lrt_regret_le
    (PA PB : H → ℝ) (dec : H → Bool) (lA lB : Act → ℝ) (aA aB : Act) (Lmax : ℝ)
    (hPA : ∀ h, 0 ≤ PA h) (hPB : ∀ h, 0 ≤ PB h)
    (hA0 : lA aA = 0) (hB0 : lB aB = 0)
    (hAx : lA aB ≤ Lmax) (hBx : lB aA ≤ Lmax) :
    (∑ h, PA h * lA (if dec h then aA else aB)
      + ∑ h, PB h * lB (if dec h then aA else aB)) / 2
      ≤ Lmax * ((∑ h, PA h * (if dec h then (0:ℝ) else 1)
          + ∑ h, PB h * (if dec h then (1:ℝ) else 0)) / 2) := by
  classical
  have hstepA : ∀ h : H, PA h * lA (if dec h then aA else aB)
      ≤ Lmax * (PA h * (if dec h then (0:ℝ) else 1)) := by
    intro h
    by_cases hd : dec h = true
    · rw [if_pos hd, if_pos hd, hA0]
      simp
    · rw [if_neg hd, if_neg hd]
      have h1 : PA h * lA aB ≤ PA h * Lmax := mul_le_mul_of_nonneg_left hAx (hPA h)
      have heq : Lmax * (PA h * 1) = PA h * Lmax := by ring
      rw [heq]
      exact h1
  have hstepB : ∀ h : H, PB h * lB (if dec h then aA else aB)
      ≤ Lmax * (PB h * (if dec h then (1:ℝ) else 0)) := by
    intro h
    by_cases hd : dec h = true
    · rw [if_pos hd, if_pos hd]
      have h1 : PB h * lB aA ≤ PB h * Lmax := mul_le_mul_of_nonneg_left hBx (hPB h)
      have heq : Lmax * (PB h * 1) = PB h * Lmax := by ring
      rw [heq]
      exact h1
    · rw [if_neg hd, if_neg hd, hB0]
      simp
  have hsumA := Finset.sum_le_sum (fun h (_ : h ∈ (univ : Finset H)) => hstepA h)
  have hsumB := Finset.sum_le_sum (fun h (_ : h ∈ (univ : Finset H)) => hstepB h)
  have hA' : ∑ h, Lmax * (PA h * (if dec h then (0:ℝ) else 1))
      = Lmax * ∑ h, PA h * (if dec h then (0:ℝ) else 1) := by rw [Finset.mul_sum]
  have hB' : ∑ h, Lmax * (PB h * (if dec h then (1:ℝ) else 0))
      = Lmax * ∑ h, PB h * (if dec h then (1:ℝ) else 0) := by rw [Finset.mul_sum]
  rw [hA'] at hsumA
  rw [hB'] at hsumB
  linarith [hsumA, hsumB]

/-- The chain, assembled: with the affinity bracket for `e`, the equal-prior Bayes
regret is pinned between two powers of the same affinity. -/
theorem bayes_regret_window (gamma Lmax e R rhoN rho2N : ℝ)
    (hg : 0 ≤ gamma) (hL : 0 ≤ Lmax)
    (hlow : rho2N / 4 ≤ e) (hup : e ≤ rhoN / 2)
    (hR1 : gamma * e ≤ R) (hR2 : R ≤ Lmax * e) :
    gamma * rho2N / 4 ≤ R ∧ R ≤ Lmax * rhoN / 2 := by
  constructor
  · have : gamma * (rho2N / 4) ≤ gamma * e := mul_le_mul_of_nonneg_left hlow hg
    linarith
  · have : Lmax * e ≤ Lmax * (rhoN / 2) := mul_le_mul_of_nonneg_left hup hL
    linarith

#print axioms outside_cost
#print axioms inside_cost
#print axioms regret_ge_gamma_error
#print axioms lrt_regret_le
#print axioms bayes_regret_window

end CIGAMF.P13.QueryRegretBridge
