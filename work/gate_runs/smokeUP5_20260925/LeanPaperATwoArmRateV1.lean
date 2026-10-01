import «LeanPaperABudgetUpperV1»
import «LeanPaperARepairLawV1»

/-!
# Paper A: the repair law on two Gaussian arms, upper side instantiated

The two-arm class of `LeanPaperARepairLawV1` (decision: which of two unit-variance means is
larger; the frozen surrogate lets only the leader move) as a specification of the stream model
of `LeanPaperABudgetUpperV1`.

* `jw_two`: the stream model's true game at a design is the closed form `w₀w₁Δ²/2` of
  `jtrue2_eq`.
* `jf_two`: the frozen game is `w₀Δ²/2` (`jproxy2_eq`).
* `two_arm_budget_rate`: at a budget `b ∈ (0, 1/2]`, the design `(1-b, b)` has sacrifice `b`.
  - It attains the frontier `R(b) = b(1-b)Δ²/2`, and no design within the budget carries more
    (`two_arm_frontier`).
  - The tracking learner holding it, with the GLR stop, has
    `limsup E τ_δ / log(1/δ) ≤ 2/(b(1-b)Δ²)`, and is δ-correct.
* `two_arm_eventually`: for `b' < b`, the realised design of the learner holding `(1-b', b')`
  meets the budget `b` on every path after a deterministic time.
-/

namespace CIGAMF.P13.PaperATwoArmRate

open Finset MeasureTheory
open CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperABudgetUpper CIGAMF.P13.PaperARepairLaw CIGAMF.P13.PaperASacrificeDuality
open CIGAMF.P13.PaperA6OracleLearner CIGAMF.P13.PaperA7StoppedGen CIGAMF.P13.PaperA7Stream
open CIGAMF.P13.PaperA7Process

/-- **Two unit-variance arms.**  Answer `T` says that arm `T` has the larger mean. -/
noncomputable def twoSpec : Spec (Fin 2) (Fin 2) where
  σ := fun _ => 1
  σ_pos := fun _ => one_pos
  Alt := fun T => {l | l T ≤ l (1 - T)}
  Alt_ne := fun T => ⟨fun _ => 0, by simp⟩
  kf := fun s => s + 1
  kf_pos := fun s => Nat.succ_pos s

theorem sc_one (x : Fin 2 → ℝ) : sc (fun _ => (1 : ℝ)) x = x := funext fun e => div_one _

theorem image_sc_one (S : Set (Fin 2 → ℝ)) : sc (fun _ => (1 : ℝ)) '' S = S := by
  simp [sc_one]

theorem pen_eq_en2 (θ w l : Fin 2 → ℝ) : pen w θ l = en2 (θ 0) (θ 1) w l := by
  unfold pen en2
  simp [Fin.sum_univ_two]

theorem alt_zero : twoSpec.Alt 0 = altTrue := by
  ext l
  simp [twoSpec, altTrue]

/-- **The stream model's true game is the closed form.** -/
theorem jw_two (θ w : Fin 2 → ℝ) (hθ : θ 1 ≤ θ 0) (hw : IsAlloc w) :
    Jw twoSpec 0 θ w = w 0 * w 1 * (θ 0 - θ 1) ^ 2 / 2 := by
  rw [← jtrue2_eq (θ 0) (θ 1) hθ w ⟨hw.1, hw.2⟩]
  unfold Jw Jval jtrue2
  rw [show twoSpec.σ = fun _ => (1 : ℝ) from rfl, image_sc_one, sc_one, alt_zero,
    Set.image_eq_range]
  simp only [pen_eq_en2]
  rfl

/-- **The stream model's frozen game is the closed form.** -/
theorem jf_two (θ w : Fin 2 → ℝ) (hθ : θ 1 ≤ θ 0) (hw : IsAlloc w) :
    Jval (sc twoSpec.σ '' altFrozen (θ 1)) w (sc twoSpec.σ θ) = w 0 * (θ 0 - θ 1) ^ 2 / 2 := by
  rw [← jproxy2_eq (θ 0) (θ 1) hθ w ⟨hw.1, hw.2⟩]
  unfold Jval jproxy2
  rw [show twoSpec.σ = fun _ => (1 : ℝ) from rfl, image_sc_one, sc_one, Set.image_eq_range]
  simp only [pen_eq_en2]
  rfl

/-- The design that gives up `b` on the second arm. -/
noncomputable def wb (b : ℝ) : Fin 2 → ℝ := ![1 - b, b]

theorem wb_alloc (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : IsAlloc (wb b) :=
  ⟨fun i => by fin_cases i <;> simp [wb] <;> linarith, by simp [wb, Fin.sum_univ_two]⟩

/-- **The repair law on two arms, upper side.** -/
theorem two_arm_budget_rate (θ : Fin 2 → ℝ) (hθ : θ 1 < θ 0) (a : ℝ) (ha : 0 < a) (b : ℝ)
    (hb0 : 0 < b) (hb1 : b ≤ 1 / 2) :
    sac (jproxy2 (θ 0) (θ 1)) ((θ 0 - θ 1) ^ 2 / 2) (wb b) = b
      ∧ Jw twoSpec 0 θ (wb b) = b * (1 - b) * (θ 0 - θ 1) ^ 2 / 2
      ∧ (∀ w, IsAllocG w → sac (jproxy2 (θ 0) (θ 1)) ((θ 0 - θ 1) ^ 2 / 2) w ≤ b →
          jtrue2 (θ 0) (θ 1) w ≤ b * (1 - b) * (θ 0 - θ 1) ^ 2 / 2)
      ∧ CIGAMF.P13.PaperAEndgame.UpperRate
          (fun δ => (∫⁻ ω, (tauG twoSpec a δ (oLearner (constO (wb b)
            (wb_alloc b hb0.le (by linarith)))) θ ω).toENNReal ∂streamMeasure).toReal)
          (b * (1 - b) * (θ 0 - θ 1) ^ 2 / 2) := by
  have hw := wb_alloc b hb0.le (by linarith)
  have hJ : Jw twoSpec 0 θ (wb b) = b * (1 - b) * (θ 0 - θ 1) ^ 2 / 2 := by
    rw [jw_two θ (wb b) hθ.le hw]
    simp only [wb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    ring
  refine ⟨?_, hJ, (two_arm_frontier (θ 0) (θ 1) hθ b hb0.le hb1).1, ?_⟩
  · rw [two_arm_sac (θ 0) (θ 1) hθ (wb b) ⟨hw.1, hw.2⟩]; simp [wb]
  · rw [← hJ]
    refine fix_upper_rate twoSpec a ha 0 θ (wb b) hw ?_
    rw [hJ]
    have : 0 < θ 0 - θ 1 := by linarith
    have : 0 < 1 - b := by linarith
    positivity

/-- **The learner holding `(1-b', b')` enters the budget `b > b'` on every path.** -/
theorem two_arm_eventually (θ : Fin 2 → ℝ) (hθ : θ 1 < θ 0) (b' b : ℝ) (hb'0 : 0 ≤ b')
    (hb' : b' < b) (hb'1 : b' ≤ 1) :
    ∃ T : ℕ, ∀ t, T ≤ t → ∀ ω,
      1 - Jval (sc twoSpec.σ '' altFrozen (θ 1))
        (fun e => Nc (oLearner (constO (wb b') (wb_alloc b' hb'0 hb'1))) θ twoSpec.σ t ω e / t)
        (sc twoSpec.σ θ) / ((θ 0 - θ 1) ^ 2 / 2) ≤ b := by
  have hw := wb_alloc b' hb'0 hb'1
  have hΔ : 0 < (θ 0 - θ 1) ^ 2 / 2 := by
    have : 0 < θ 0 - θ 1 := by linarith
    positivity
  refine fix_budget_eventually twoSpec θ (wb b') hw (altFrozen (θ 1))
    ⟨fun _ => θ 1, by simp [altFrozen]⟩ _ hΔ b ?_
  rw [jf_two θ (wb b') hθ.le hw]
  simp only [wb, Matrix.cons_val_zero]
  rw [show (1 - b') * (θ 0 - θ 1) ^ 2 / 2 / ((θ 0 - θ 1) ^ 2 / 2) = 1 - b' by
    have hne : θ 0 - θ 1 ≠ 0 := (sub_pos.mpr hθ).ne'
    field_simp]
  linarith

#print axioms jw_two
#print axioms jf_two
#print axioms two_arm_budget_rate
#print axioms two_arm_eventually

end CIGAMF.P13.PaperATwoArmRate
