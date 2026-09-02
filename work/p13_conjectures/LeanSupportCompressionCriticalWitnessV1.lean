import Mathlib
import «LeanSupportGeometryV4»
import «LeanSupportCriticalIdentificationV1»

/-!
# Exact decision-critical support witness for CIG support compression

Two feasible-support worlds differ only in joint-action cell `2`.  For the
actual support-radius compression objective, the zero-regret retained choice
switches.  Thus a controller observing support only with cell `2` erased
cannot be universally zero-regret.
-/

namespace CIGAMF.P13.SupportCompressionCriticalWitness

open scoped BigOperators symmDiff
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.SupportCriticalIdentification

def smallSupport : Finset (Fin 3) := {0, 1}
def largeSupport : Finset (Fin 3) := {0, 1, 2}

/- `false` and `true` are two actual retained-complement response functions. -/
def supportResidual (decision : Bool) (a : Fin 3) : ℝ :=
  if decision then
    if a = 1 then 1 else 0
  else
    if a = 2 then 10 else 0

private theorem small_nonempty : smallSupport.Nonempty := by
  refine ⟨0, by simp [smallSupport]⟩

private theorem large_nonempty : largeSupport.Nonempty := by
  refine ⟨0, by simp [largeSupport]⟩

private theorem maxOn_exact
    (support : Finset (Fin 3)) (hne : support.Nonempty)
    (f : Fin 3 → ℝ) (hi : ℝ)
    (hupper : ∀ a ∈ support, f a ≤ hi)
    (xhi : Fin 3) (hxhi : xhi ∈ support) (hhi : f xhi = hi) :
    CIGAMF.V4.SupportGeometry.maxOn support hne f = hi := by
  apply le_antisymm
  · unfold CIGAMF.V4.SupportGeometry.maxOn
    apply (Finset.max'_le_iff _ _).2
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
    exact hupper a ha
  · have hle : f xhi ≤ CIGAMF.V4.SupportGeometry.maxOn support hne f := by
      unfold CIGAMF.V4.SupportGeometry.maxOn
      exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨xhi, hxhi, rfl⟩)
    simpa [hhi] using hle

private theorem minOn_exact
    (support : Finset (Fin 3)) (hne : support.Nonempty)
    (f : Fin 3 → ℝ) (lo : ℝ)
    (hlower : ∀ a ∈ support, lo ≤ f a)
    (xlo : Fin 3) (hxlo : xlo ∈ support) (hlo : f xlo = lo) :
    CIGAMF.V4.SupportGeometry.minOn support hne f = lo := by
  apply le_antisymm
  · have hle : CIGAMF.V4.SupportGeometry.minOn support hne f ≤ f xlo := by
      unfold CIGAMF.V4.SupportGeometry.minOn
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨xlo, hxlo, rfl⟩)
    simpa [hlo] using hle
  · unfold CIGAMF.V4.SupportGeometry.minOn
    apply (Finset.le_min'_iff _ _).2
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
    exact hlower a ha

private theorem radiusOn_exact
    (support : Finset (Fin 3)) (hne : support.Nonempty)
    (f : Fin 3 → ℝ) (lo hi : ℝ)
    (hlower : ∀ a ∈ support, lo ≤ f a)
    (hupper : ∀ a ∈ support, f a ≤ hi)
    (xlo xhi : Fin 3) (hxlo : xlo ∈ support) (hxhi : xhi ∈ support)
    (hlo : f xlo = lo) (hhi : f xhi = hi) :
    radiusOn support hne f = (hi - lo) / 2 := by
  unfold radiusOn oscOn
  rw [maxOn_exact support hne f hi hupper xhi hxhi hhi,
    minOn_exact support hne f lo hlower xlo hxlo hlo]

noncomputable def supportLoss (omega : Finset (Fin 3)) (decision : Bool) : ℝ :=
  if h : omega.Nonempty then radiusOn omega h (supportResidual decision) else 0

noncomputable def supportOptimal (omega : Finset (Fin 3)) : ℝ :=
  min (supportLoss omega false) (supportLoss omega true)

noncomputable def supportCompressionRegret
    (omega : Finset (Fin 3)) (decision : Bool) : ℝ :=
  supportLoss omega decision - supportOptimal omega

private theorem small_false_loss : supportLoss smallSupport false = 0 := by
  rw [supportLoss, dif_pos small_nonempty]
  convert radiusOn_exact smallSupport small_nonempty (supportResidual false) 0 0
    (by intro a ha; by_cases h : a = 2 <;> simp [supportResidual, h])
    (by
      intro a ha
      have hne : a ≠ 2 := by
        intro heq
        subst a
        simpa [smallSupport] using ha
      simp [supportResidual, hne])
    0 0 (by simp [smallSupport]) (by simp [smallSupport])
    (by norm_num [supportResidual, show (0 : Fin 3) ≠ 2 by decide])
    (by norm_num [supportResidual, show (0 : Fin 3) ≠ 2 by decide]) using 1 <;> norm_num

private theorem small_true_loss : supportLoss smallSupport true = 1 / 2 := by
  rw [supportLoss, dif_pos small_nonempty]
  convert radiusOn_exact smallSupport small_nonempty (supportResidual true) 0 1
    (by intro a ha; by_cases h : a = 1 <;> simp [supportResidual, h])
    (by intro a ha; by_cases h : a = 1 <;> simp [supportResidual, h])
    0 1 (by simp [smallSupport]) (by simp [smallSupport])
    (by norm_num [supportResidual, show (0 : Fin 3) ≠ 1 by decide])
    (by norm_num [supportResidual]) using 1 <;> norm_num

private theorem large_false_loss : supportLoss largeSupport false = 5 := by
  rw [supportLoss, dif_pos large_nonempty]
  convert radiusOn_exact largeSupport large_nonempty (supportResidual false) 0 10
    (by intro a ha; by_cases h : a = 2 <;> simp [supportResidual, h])
    (by intro a ha; by_cases h : a = 2 <;> simp [supportResidual, h])
    0 2 (by simp [largeSupport]) (by simp [largeSupport])
    (by norm_num [supportResidual, show (0 : Fin 3) ≠ 2 by decide])
    (by norm_num [supportResidual]) using 1 <;> norm_num

private theorem large_true_loss : supportLoss largeSupport true = 1 / 2 := by
  rw [supportLoss, dif_pos large_nonempty]
  convert radiusOn_exact largeSupport large_nonempty (supportResidual true) 0 1
    (by intro a ha; by_cases h : a = 1 <;> simp [supportResidual, h])
    (by intro a ha; by_cases h : a = 1 <;> simp [supportResidual, h])
    0 1 (by simp [largeSupport]) (by simp [largeSupport])
    (by norm_num [supportResidual, show (0 : Fin 3) ≠ 1 by decide])
    (by norm_num [supportResidual]) using 1 <;> norm_num

@[simp] theorem small_false_regret : supportCompressionRegret smallSupport false = 0 := by
  simp [supportCompressionRegret, supportOptimal, small_false_loss, small_true_loss]

@[simp] theorem small_true_regret : supportCompressionRegret smallSupport true = 1 / 2 := by
  simp [supportCompressionRegret, supportOptimal, small_false_loss, small_true_loss]

@[simp] theorem large_false_regret : supportCompressionRegret largeSupport false = 9 / 2 := by
  rw [supportCompressionRegret, supportOptimal,
    large_false_loss, large_true_loss]
  have hmin : min (5 : ℝ) (1 / 2) = 1 / 2 := min_eq_right (by norm_num)
  rw [hmin]
  norm_num

@[simp] theorem large_true_regret : supportCompressionRegret largeSupport true = 0 := by
  rw [supportCompressionRegret, supportOptimal,
    large_false_loss, large_true_loss]
  have hmin : min (5 : ℝ) (1 / 2) = 1 / 2 := min_eq_right (by norm_num)
  rw [hmin]
  norm_num

theorem actual_support_worlds_differ_only_at_cell2 :
    smallSupport ∆ largeSupport ⊆ ({2} : Finset (Fin 3)) := by
  decide

theorem actual_support_zero_good_sets_disjoint :
    Incompatible supportCompressionRegret 0 smallSupport largeSupport := by
  rw [Incompatible, Set.disjoint_left]
  intro d hs hl
  cases d
  · norm_num [SupportGood, supportCompressionRegret, supportOptimal,
      small_false_loss, small_true_loss, large_false_loss,
      large_true_loss] at hl
  · norm_num [SupportGood, supportCompressionRegret, supportOptimal,
      small_false_loss, small_true_loss, large_false_loss,
      large_true_loss] at hs

theorem actual_support_cell2_critical :
    CriticalCell supportCompressionRegret 0 2 :=
  ⟨smallSupport, largeSupport,
    actual_support_worlds_differ_only_at_cell2,
    actual_support_zero_good_sets_disjoint⟩

def eraseCell2Observation (omega : Finset (Fin 3)) : Finset (Fin 3) :=
  omega.erase 2

theorem eraseCell2_blind_to_cell2 :
    CannotDistinguishCell eraseCell2Observation 2 := by
  intro omega₁ omega₂ hdiff
  apply Finset.ext
  intro a
  by_cases h2 : a = 2
  · subst a
    simp [eraseCell2Observation]
  · have hiff : a ∈ omega₁ ↔ a ∈ omega₂ := by
      constructor
      · intro h₁
        by_contra hnot
        have hmem : a ∈ omega₁ ∆ omega₂ := by
          rw [Finset.mem_symmDiff]
          exact Or.inl ⟨h₁, hnot⟩
        have : a ∈ ({2} : Finset (Fin 3)) := hdiff hmem
        exact h2 (by simpa using this)
      · intro h₂
        by_contra hnot
        have hmem : a ∈ omega₁ ∆ omega₂ := by
          rw [Finset.mem_symmDiff]
          exact Or.inr ⟨h₂, hnot⟩
        have : a ∈ ({2} : Finset (Fin 3)) := hdiff hmem
        exact h2 (by simpa using this)
    simp [eraseCell2Observation, h2, hiff]

theorem actual_support_compression_blind_cell2_impossibility :
    ¬ ∃ controller : Finset (Fin 3) → Bool,
      ∀ omega : Finset (Fin 3),
        supportCompressionRegret omega
          (controller (eraseCell2Observation omega)) ≤ 0 := by
  exact SUP_B1_critical_cell_necessity supportCompressionRegret 0
    eraseCell2Observation 2 actual_support_cell2_critical
    eraseCell2_blind_to_cell2

end CIGAMF.P13.SupportCompressionCriticalWitness
