import Mathlib
import «LeanD6PAECExistence»

/-!
# Cost-aware completion of an available PAEC certificate

The theorems in this file are conditional on a supplied valid certificate.
They do not assume the still-open arbitrary Top-C-pair to PAEC existence
statement isolated in `LeanD6PAECExistence`.
-/

namespace CIGAMF.P13.D6CostAwarePAECCompletion

open scoped BigOperators

variable {R K : Type*} [Fintype R] [DecidableEq R]

structure AtomIntervals (R : Type*) where
  lower : R → ℝ
  upper : R → ℝ

def Covers (I : AtomIntervals R) (value : R → ℝ) : Prop :=
  ∀ r, I.lower r ≤ value r ∧ value r ≤ I.upper r

def Refines (new old : AtomIntervals R) : Prop :=
  ∀ r, old.lower r ≤ new.lower r ∧ new.upper r ≤ old.upper r

noncomputable def upperContribution (alpha lower upper : ℝ) : ℝ :=
  if 0 ≤ alpha then alpha * upper else alpha * lower

theorem contribution_le_upperContribution
    (alpha lower value upper : ℝ)
    (hLower : lower ≤ value) (hUpper : value ≤ upper) :
    alpha * value ≤ upperContribution alpha lower upper := by
  unfold upperContribution
  split
  · rename_i hAlpha
    exact mul_le_mul_of_nonneg_left hUpper hAlpha
  · rename_i hAlpha
    exact mul_le_mul_of_nonpos_left hLower (le_of_not_ge hAlpha)

theorem upperContribution_refinement
    (alpha oldLower oldUpper newLower newUpper : ℝ)
    (hLower : oldLower ≤ newLower) (hUpper : newUpper ≤ oldUpper) :
    upperContribution alpha newLower newUpper ≤
      upperContribution alpha oldLower oldUpper := by
  unfold upperContribution
  split
  · rename_i hAlpha
    exact mul_le_mul_of_nonneg_left hUpper hAlpha
  · rename_i hAlpha
    exact mul_le_mul_of_nonpos_left hLower (le_of_not_ge hAlpha)

structure ValidCertificate (R : Type*) [Fintype R]
    (atomValue : R → ℝ) (decisionGap : ℝ) where
  alpha : R → ℝ
  correction : ℝ
  correction_nonpos : correction ≤ 0
  sound : 2 * decisionGap ≤ ∑ r, alpha r * atomValue r + correction

noncomputable def robustBound
    {atomValue : R → ℝ} {decisionGap : ℝ}
    (C : ValidCertificate R atomValue decisionGap) (I : AtomIntervals R) : ℝ :=
  (∑ r, upperContribution (C.alpha r) (I.lower r) (I.upper r)) / 2

theorem D6_B1_certificate_specific_robust_bound
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (C : ValidCertificate R atomValue decisionGap) (I : AtomIntervals R)
    (hCovers : Covers I atomValue) :
    decisionGap ≤ robustBound C I := by
  have hTerms :
      (∑ r, C.alpha r * atomValue r) ≤
        ∑ r, upperContribution (C.alpha r) (I.lower r) (I.upper r) := by
    exact Finset.sum_le_sum fun r _ ↦
      contribution_le_upperContribution _ _ _ _
        (hCovers r).1 (hCovers r).2
  have hSound := C.sound
  have hCorrection := C.correction_nonpos
  unfold robustBound
  linarith

noncomputable def bestRobustBound
    [DecidableEq K] (family : Finset K) (hFamily : family.Nonempty)
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (certificate : K → ValidCertificate R atomValue decisionGap)
    (I : AtomIntervals R) : ℝ :=
  (family.image fun k ↦ robustBound (certificate k) I).min'
    (Finset.image_nonempty.mpr hFamily)

theorem D6_B2_best_available_certificate_sound
    [DecidableEq K] (family : Finset K) (hFamily : family.Nonempty)
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (certificate : K → ValidCertificate R atomValue decisionGap)
    (I : AtomIntervals R) (hCovers : Covers I atomValue) :
    decisionGap ≤
      bestRobustBound family hFamily atomValue decisionGap certificate I := by
  unfold bestRobustBound
  apply Finset.le_min'
  intro bound hBound
  rcases Finset.mem_image.1 hBound with ⟨k, hk, rfl⟩
  exact D6_B1_certificate_specific_robust_bound atomValue decisionGap
    (certificate k) I hCovers

theorem robustBound_refinement
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (C : ValidCertificate R atomValue decisionGap)
    (new old : AtomIntervals R) (hRefines : Refines new old) :
    robustBound C new ≤ robustBound C old := by
  unfold robustBound
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun r _ ↦
      upperContribution_refinement _ _ _ _ _
        (hRefines r).1 (hRefines r).2
  · norm_num

theorem D6_B3_best_certificate_refinement_monotonicity
    [DecidableEq K] (family : Finset K) (hFamily : family.Nonempty)
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (certificate : K → ValidCertificate R atomValue decisionGap)
    (new old : AtomIntervals R) (hRefines : Refines new old) :
    bestRobustBound family hFamily atomValue decisionGap certificate new ≤
      bestRobustBound family hFamily atomValue decisionGap certificate old := by
  rcases family.exists_min_image
      (fun k ↦ robustBound (certificate k) old) hFamily with
    ⟨k, hk, hkMin⟩
  have hNewLe :
      bestRobustBound family hFamily atomValue decisionGap certificate new ≤
        robustBound (certificate k) new := by
    unfold bestRobustBound
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  have hRefined := robustBound_refinement atomValue decisionGap
    (certificate k) new old hRefines
  have hOldEq :
      bestRobustBound family hFamily atomValue decisionGap certificate old =
        robustBound (certificate k) old := by
    unfold bestRobustBound
    apply le_antisymm
    · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
    · apply Finset.le_min'
      intro b hb
      rcases Finset.mem_image.1 hb with ⟨k', hk', rfl⟩
      exact hkMin k' hk'
  rw [hOldEq]
  exact le_trans hNewLe hRefined

noncomputable def certificateSupport
    {atomValue : R → ℝ} {decisionGap : ℝ}
    (C : ValidCertificate R atomValue decisionGap) : Finset R :=
  Finset.univ.filter fun r ↦ C.alpha r ≠ 0

noncomputable def remainingCost
    {atomValue : R → ℝ} {decisionGap : ℝ}
    (C : ValidCertificate R atomValue decisionGap)
    (measured : Finset R) (cost : R → ℝ) : ℝ :=
  ∑ r ∈ certificateSupport C \ measured, cost r

theorem D6_B4_minimum_remaining_cost_certificate_exists
    [DecidableEq K] (family : Finset K) (hFamily : family.Nonempty)
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (certificate : K → ValidCertificate R atomValue decisionGap)
    (measured : Finset R) (cost : R → ℝ) :
    ∃ k ∈ family, ∀ k' ∈ family,
      remainingCost (certificate k) measured cost ≤
        remainingCost (certificate k') measured cost := by
  exact family.exists_min_image
    (fun k ↦ remainingCost (certificate k) measured cost) hFamily

theorem certificate_sum_depends_only_on_support
    (atomValue₁ atomValue₂ : R → ℝ) (decisionGap : ℝ)
    (C : ValidCertificate R atomValue₁ decisionGap)
    (hSame : ∀ r ∈ certificateSupport C, atomValue₁ r = atomValue₂ r) :
    (∑ r, C.alpha r * atomValue₁ r) =
      ∑ r, C.alpha r * atomValue₂ r := by
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hAlpha : C.alpha r = 0
  · simp [hAlpha]
  · rw [hSame r (by simp [certificateSupport, hAlpha])]

noncomputable def uncertaintyWidth
    {atomValue : R → ℝ} {decisionGap : ℝ}
    (C : ValidCertificate R atomValue decisionGap) (I : AtomIntervals R) : ℝ :=
  ∑ r, |C.alpha r| * (I.upper r - I.lower r)

theorem uncertaintyWidth_refinement
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (C : ValidCertificate R atomValue decisionGap)
    (new old : AtomIntervals R) (hRefines : Refines new old) :
    uncertaintyWidth C new ≤ uncertaintyWidth C old := by
  unfold uncertaintyWidth
  apply Finset.sum_le_sum
  intro r hr
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  linarith [(hRefines r).1, (hRefines r).2]

theorem D6_B5_minimum_width_certificate_exists
    [DecidableEq K] (family : Finset K) (hFamily : family.Nonempty)
    (atomValue : R → ℝ) (decisionGap : ℝ)
    (certificate : K → ValidCertificate R atomValue decisionGap)
    (I : AtomIntervals R) :
    ∃ k ∈ family, ∀ k' ∈ family,
      uncertaintyWidth (certificate k) I ≤
        uncertaintyWidth (certificate k') I := by
  exact family.exists_min_image
    (fun k ↦ uncertaintyWidth (certificate k) I) hFamily

theorem D6_B6_certificate_switching_soundness
    [DecidableEq K] (family : Finset K)
    (atomValue : R → ℝ) (decisionGap eps : ℝ)
    (certificate : K → ValidCertificate R atomValue decisionGap)
    (I : AtomIntervals R) (hCovers : Covers I atomValue)
    (current : K) (hCurrent : current ∈ family)
    (hStop : robustBound (certificate current) I ≤ eps) :
    decisionGap ≤ eps := by
  exact le_trans
    (D6_B1_certificate_specific_robust_bound atomValue decisionGap
      (certificate current) I hCovers) hStop

/- Exact values outside the certificate support cannot affect evaluation of
that certificate.  Consequently probing every remaining support atom is
sufficient for exact evaluation of this fixed certificate. -/
theorem D6_B4_B6_support_sparsity
    (atomValue₁ atomValue₂ : R → ℝ) (decisionGap : ℝ)
    (C : ValidCertificate R atomValue₁ decisionGap)
    (hMeasured : ∀ r ∈ certificateSupport C, atomValue₁ r = atomValue₂ r) :
    (∑ r, C.alpha r * atomValue₁ r) =
      ∑ r, C.alpha r * atomValue₂ r :=
  certificate_sum_depends_only_on_support atomValue₁ atomValue₂
    decisionGap C hMeasured

/- D6-B8 remains deliberately separate: this definition is the precise open
existence dependency, not a hidden premise of B1--B6. -/
abbrev ArbitraryTopCPairHasPAEC :=
  @CIGAMF.P13.D6PAECExistence.EveryTopCPairHasPAEC

end CIGAMF.P13.D6CostAwarePAECCompletion
