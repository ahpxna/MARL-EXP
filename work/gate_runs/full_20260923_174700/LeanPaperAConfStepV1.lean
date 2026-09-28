import «LeanPaperA7ChainV1»
import «LeanPaperA7ConfidenceV1»

/-!
# Paper A: the `n^{-4}` confidence step, produced rather than assumed

`a7_chain_rate` carries

    hstep : forall alpha n, (mu (good alpha n)^c).toReal <= 1 / n^4,

the per-round failure probability of the confidence set the learner uses to choose its
answer and its allocation.  `THEOREM_MAP.md` recorded it as still assumed.  It is not an
assumption about the world: it is a property of the set the ALGORITHM builds, and the
algorithm builds it from the same mixture supermartingale that `LeanPaperA7ConfidenceV1`
already analyses.

The round-`n` confidence set is "the mixture has not crossed `n^4` by time `n`".  Its
complement is exactly the event `confidence_of_supermartingale` bounds at `delta = n^{-4}`,
since `1/delta = n^4`.  So `hstep` follows from Ville's inequality applied at a level that
shrinks with the round -- which is precisely the design choice
`fixed_level_gives_no_summable_tail` says is forced.

`sum_inv_fourth_le_two` then supplies the other half of the design: the levels are summable,
with the explicit constant `2`, so the whole run contributes a bounded head however long it
runs.  `a7_chain_rate_constructed` is `a7_chain_rate` with `good` instantiated at the built
set and `hstep` discharged.
-/

namespace CIGAMF.P13.PaperAConfStep

open MeasureTheory
open CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Chain

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ## The confidence set the learner actually builds -/

/-- The round-`n` failure event: the mixture crossed `n^4` by time `n`.  Round `0` is
vacuous, matching the convention `1/0^4 = 0`. -/
def badRound (M : ℕ → Ω → ℝ) (n : ℕ) : Set Ω :=
  if n = 0 then (∅ : Set Ω) else {ω | ∃ j ≤ n, (n : ℝ) ^ 4 ≤ M j ω}

/-- The round-`n` confidence set. -/
def goodRound (M : ℕ → Ω → ℝ) (n : ℕ) : Set Ω := (badRound M n)ᶜ

theorem goodRound_compl (M : ℕ → Ω → ℝ) (n : ℕ) :
    (goodRound M n)ᶜ = badRound M n := compl_compl _

/-- **The confidence step, proved.**  The round-`n` set the learner builds fails with
probability at most `n^{-4}`, by Ville's inequality at level `n^{-4}`. -/
theorem confidence_step_pow_four {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ m0} [SigmaFiniteFiltration μ 𝒢]
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M 𝒢 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hstart : ∫ ω, M 0 ω ∂μ ≤ 1) (n : ℕ) :
    (μ (goodRound M n)ᶜ).toReal ≤ 1 / (n : ℝ) ^ 4 := by
  rw [goodRound_compl]
  unfold badRound
  by_cases hn : n = 0
  · rw [if_pos hn, hn]
    norm_num
  · rw [if_neg hn]
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := Nat.pos_of_ne_zero hn
      exact_mod_cast this
    have hδ : (0 : ℝ) < 1 / (n : ℝ) ^ 4 := by positivity
    have hinv : 1 / (1 / (n : ℝ) ^ 4) = (n : ℝ) ^ 4 := by
      field_simp
    have h := confidence_of_supermartingale M hM hnn hstart (1 / (n : ℝ) ^ 4) hδ n
    rw [hinv] at h
    exact h

/-! ## The levels are summable, with an explicit constant -/

theorem inv_fourth_nonneg (n : ℕ) : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity

/-- `1/n^4 <= 1/(n-1) - 1/n` for `n >= 2`: the comparison that telescopes. -/
theorem inv_fourth_le_telescope (n : ℕ) (hn : 2 ≤ n) :
    1 / (n : ℝ) ^ 4 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hid : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) = 1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp
    ring
  rw [hid]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg ((n : ℝ) ^ 2)]

/-- The partial sums, with the telescoped remainder. -/
theorem sum_inv_fourth_tail (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ Finset.range N, 1 / (n : ℝ) ^ 4 ≤ 2 - 1 / ((N : ℝ) - 1) := by
  induction N, hN using Nat.le_induction with
  | base =>
      rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
      norm_num
  | succ N hN ih =>
      rw [Finset.sum_range_succ]
      have hstep := inv_fourth_le_telescope N hN
      have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hcast : ((N + 1 : ℕ) : ℝ) - 1 = (N : ℝ) := by push_cast; ring
      rw [hcast]
      linarith [ih, hstep]

/-- **The design is summable, with constant `2`.**  Every partial sum of the levels is at
most `2`, so the head the window pays is bounded however long the run is. -/
theorem sum_inv_fourth_le_two (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / (n : ℝ) ^ 4 ≤ 2 := by
  rcases Nat.lt_or_ge N 2 with hN | hN
  · interval_cases N
    · simp
    · rw [Finset.sum_range_one]; norm_num
  · have h := sum_inv_fourth_tail N hN
    have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have : (0 : ℝ) < 1 / ((N : ℝ) - 1) := by
      apply div_pos one_pos
      linarith
    linarith

theorem summable_inv_fourth : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
  summable_of_sum_range_le inv_fourth_nonneg sum_inv_fourth_le_two

/-- **And the whole tail is at most `2`.**  Contrast `fixed_level_gives_no_summable_tail`:
at a constant level the same sum diverges. -/
theorem tsum_inv_fourth_le_two : ∑' n : ℕ, 1 / (n : ℝ) ^ 4 ≤ 2 :=
  Real.tsum_le_of_sum_range_le inv_fourth_nonneg sum_inv_fourth_le_two

/-! ## The chain, with the confidence step discharged -/

/-- **A-H4 with `hstep` removed from the hypotheses.**  Everything else in `a7_chain_rate`
is unchanged; the confidence step is now supplied by the learner's own mixture
supermartingale rather than assumed of it. -/
theorem a7_chain_rate_constructed {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℕ m0} [SigmaFiniteFiltration μ 𝒢]
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M 𝒢 μ) (hnn : ∀ n ω, 0 ≤ M n ω)
    (hstart : ∫ ω, M 0 ω ∂μ ≤ 1)
    (z Z thr : ℝ → Ω → ℕ → ℝ) (τ : ℝ → Ω → ℕ)
    (Esum : ℝ → ℕ → ℝ) (Eτ s : ℝ → ℝ)
    (Γ G C ε : ℝ) (hG : 0 < G) (hε : 0 < ε) (hε1 : ε < 1)
    (hΓ : 0 ≤ Γ) (hGΓ : G ≤ Γ) (hC : 0 ≤ C)
    (hs : ∀ α, 0 ≤ s α)
    (hτ : ∀ α ω n, thr α ω n < Z α ω n → τ α ω ≤ n)
    (hhead : ∀ α ω n, -Γ ≤ z α ω n)
    (hgood : ∀ α ω n, ω ∈ goodRound M n → G ≤ z α ω n)
    (hinit : ∀ α ω n, (∑ r ∈ Finset.range n, z α ω r) - C ≤ Z α ω n)
    (hthr : ∀ α ω n, thr α ω n ≤ Real.log (1 / α) + s α)
    (hEsumα : ∀ α M', Esum α M'
        ≤ ((⌈(Real.log (1 / α) + s α + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2 : ℕ) : ℝ)
          + ∑ t ∈ Finset.Ico
              (⌈(Real.log (1 / α) + s α + winBudget Γ G C ε) / ((1 - ε) * G)⌉₊ + 2) M',
              (μ {ω | t < τ α ω}).toReal)
    (hsup : ∀ α y, (∀ M', Esum α M' ≤ y) → Eτ α ≤ y)
    (εr α0 : ℝ) (hα0 : 0 < α0) (hα01 : α0 < 1)
    (hsmall : ∀ α, 0 < α → α < α0 →
        0 < Real.log (1 / α) ∧
        (s α + winBudget Γ G C ε) + 19 * ((1 - ε) * G)
          ≤ εr * ((1 - ε) * G) * Real.log (1 / α)) :
    ∀ α, 0 < α → α < α0 → Eτ α / Real.log (1 / α) ≤ 1 / ((1 - ε) * G) + εr :=
  a7_chain_rate μ (fun _ n => goodRound M n) z Z thr τ Esum Eτ s Γ G C ε hG hε hε1 hΓ hGΓ hC
    hs (fun _ n => confidence_step_pow_four M hM hnn hstart n) hτ hhead hgood hinit hthr
    hEsumα hsup εr α0 hα0 hα01 hsmall

/-! ## Audit -/

#print axioms confidence_step_pow_four
#print axioms inv_fourth_le_telescope
#print axioms sum_inv_fourth_tail
#print axioms sum_inv_fourth_le_two
#print axioms summable_inv_fourth
#print axioms tsum_inv_fourth_le_two
#print axioms a7_chain_rate_constructed

end CIGAMF.P13.PaperAConfStep
