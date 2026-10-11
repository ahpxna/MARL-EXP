import Mathlib
import «LeanMarlEstimatedRevisionV1»

/-!
# Actor realization: the E1b Bayes-decoder MEAN value satisfies the edge-local hypothesis

E1b (`scripts/MARL_E1_controlled_calibration.py`) has senders with independent ±1 signals, and a
target `Y = Σ g_j x_j + β x_a x_b + σ₀ ξ` with a hidden interacting pair `E = {a, b}`. The Bayes
decoder that hears the set `S` has mean team value

    f(S) = −σ₀² − Σ_{j ∉ S} g_j² − β² · [E ⊄ S]

(this is the closed form the script checks against Monte-Carlo rollouts). The Monte-Carlo identity
itself is not formalised here.

## WHAT IS PROVED

* `e1b_marginal`: f(A ∪ {i}) − f(A) = g_i² + β²·[E ⊆ A ∪ {i} and E ⊄ A], for i ∉ A.
* `e1b_scoreLocal`: `ScoreLocal f g² β²`, the hypothesis of `LeanMarlEstimatedRevisionV1`.
* `e1b_scoreLocal_half`: with the pair-shifted scores w_i = g_i² + (β²/2)·[i ∈ E], the constant
  halves: `ScoreLocal f w (β²/2)`.
* `e1b_mono`: f is monotone when g² ≥ 0 and β² ≥ 0.
* `e1b_satisfiable`: a concrete instance.

## WHAT THIS DOES NOT ESTABLISH

- **The observation law.** The realization is of the MEAN value. E1b's paired raw rewards are not
  the Gaussian channel `rChan`: `MARL_E1_INDEPENDENT_AUDIT_20260927` §1 gives a finite witness in
  which the interaction changes the variance on queries that do not contain the pair. Nothing
  here transfers a KL or calibration bound to E1b.
- **Numerical usefulness.** With E1b's parameters (g² steps of 0.1, β² = 1.6) the frontier
  coefficient 2η is 3.2 (or 1.6 with the shifted scores), far above the score gaps. The deployed
  regret bound is valid but loose there.
- **Scope.** A single receiver. It is not a heterogeneous team-value realization. The decoder is
  world-specific: it knows the pair it decodes for.
-/

namespace CIGAMF.P13.MarlE1bRealization

open Finset CIGAMF.P13.MarlEstimatedRevision

variable {m : ℕ}

/-- The E1b mean value of broadcasting `S`. -/
def e1bValue (g2 : Fin m → ℝ) (β2 σ2 : ℝ) (E S : Finset (Fin m)) : ℝ :=
  -σ2 - (Finset.univ \ S).sum g2 - (if E ⊆ S then 0 else β2)

theorem sum_compl_insert (g2 : Fin m → ℝ) (A : Finset (Fin m)) (i : Fin m) (hi : i ∉ A) :
    (Finset.univ \ insert i A).sum g2 = (Finset.univ \ A).sum g2 - g2 i := by
  rw [Finset.sdiff_insert, Finset.sum_erase_eq_sub]
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩

theorem e1b_marginal (g2 : Fin m → ℝ) (β2 σ2 : ℝ) (E A : Finset (Fin m)) (i : Fin m) (hi : i ∉ A) :
    e1bValue g2 β2 σ2 E (insert i A) - e1bValue g2 β2 σ2 E A
      = g2 i + (if E ⊆ insert i A ∧ ¬ E ⊆ A then β2 else 0) := by
  unfold e1bValue
  rw [sum_compl_insert g2 A i hi]
  have hmono : E ⊆ A → E ⊆ insert i A := fun h => h.trans (Finset.subset_insert _ _)
  by_cases h1 : E ⊆ A
  · simp [h1, hmono h1]
  · by_cases h2 : E ⊆ insert i A
    · simp [h1, h2]; ring
    · simp [h1, h2]

/-- **E1b's mean value is edge-local with scores g² and constant β².** -/
theorem e1b_scoreLocal (g2 : Fin m → ℝ) (β2 σ2 : ℝ) (E : Finset (Fin m)) (hβ : 0 ≤ β2) :
    ScoreLocal (e1bValue g2 β2 σ2 E) g2 β2 := by
  intro A i hi
  rw [e1b_marginal g2 β2 σ2 E A i hi]
  split_ifs <;> simp [abs_of_nonneg hβ, hβ]

theorem subset_insert_iff_of_not_mem {E A : Finset (Fin m)} {i : Fin m} (hiE : i ∉ E) :
    E ⊆ insert i A ↔ E ⊆ A := by
  constructor
  · intro h x hx
    rcases Finset.mem_insert.mp (h hx) with rfl | hxA
    · exact absurd hx hiE
    · exact hxA
  · exact fun h => h.trans (Finset.subset_insert _ _)

/-- **Pair-shifted scores halve the constant.** -/
theorem e1b_scoreLocal_half (g2 : Fin m → ℝ) (β2 σ2 : ℝ) (E : Finset (Fin m)) (hβ : 0 ≤ β2) :
    ScoreLocal (e1bValue g2 β2 σ2 E) (fun i => g2 i + if i ∈ E then β2 / 2 else 0) (β2 / 2) := by
  intro A i hi
  rw [e1b_marginal g2 β2 σ2 E A i hi]
  beta_reduce
  by_cases hiE : i ∈ E
  · rw [if_pos hiE]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  · have : ¬ (E ⊆ insert i A ∧ ¬ E ⊆ A) := fun h => h.2 ((subset_insert_iff_of_not_mem hiE).mp h.1)
    rw [if_neg this, if_neg hiE, add_zero, sub_self, abs_zero]
    linarith

/-- **Monotone.** -/
theorem e1b_mono (g2 : Fin m → ℝ) (β2 σ2 : ℝ) (E : Finset (Fin m)) (hg : ∀ j, 0 ≤ g2 j)
    (hβ : 0 ≤ β2) {A B : Finset (Fin m)} (hAB : A ⊆ B) :
    e1bValue g2 β2 σ2 E A ≤ e1bValue g2 β2 σ2 E B := by
  unfold e1bValue
  have hs : (Finset.univ \ B).sum g2 ≤ (Finset.univ \ A).sum g2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset_sdiff le_rfl hAB)
      (fun j _ _ => hg j)
  have hp : (if E ⊆ B then (0 : ℝ) else β2) ≤ (if E ⊆ A then 0 else β2) := by
    by_cases hA : E ⊆ A
    · simp [hA, hA.trans hAB]
    · by_cases hB : E ⊆ B <;> simp [hA, hB, hβ]
  linarith

/-- A concrete instance meets every hypothesis. -/
theorem e1b_satisfiable :
    ScoreLocal (e1bValue (fun _ : Fin 4 => (1 : ℝ)) (8 / 5) (1 / 4) {0, 1}) (fun _ => 1) (8 / 5) :=
  e1b_scoreLocal _ _ _ _ (by norm_num)

end CIGAMF.P13.MarlE1bRealization

#print axioms CIGAMF.P13.MarlE1bRealization.e1b_marginal
#print axioms CIGAMF.P13.MarlE1bRealization.e1b_scoreLocal
#print axioms CIGAMF.P13.MarlE1bRealization.e1b_scoreLocal_half
#print axioms CIGAMF.P13.MarlE1bRealization.e1b_mono
#print axioms CIGAMF.P13.MarlE1bRealization.e1b_satisfiable
