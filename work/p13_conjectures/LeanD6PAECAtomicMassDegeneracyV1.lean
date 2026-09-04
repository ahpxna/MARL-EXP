import Mathlib
import «LeanD6PAECAtomicNormV1»

/-!
# Audit of the legacy instance-wise PAEC atomic mass

This module deliberately leaves the legacy certificate API unchanged.  It
shows that, whenever the observed decision gap and at least one cycle value
are nonzero, arbitrary real rescaling collapses its infimum to the observed
positive gap divided by the largest observed cycle magnitude.  Thus the API
is sound for certificates but is not a uniform decision-cell complexity.
-/

namespace CIGAMF.P13.D6PAECAtomicMassDegeneracy

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6PAECAtomicNorm

variable {U : Type*} [Fintype U] [Nonempty U]

abbrev CycleAtom (n : ℕ) (U : Type*) :=
  Fin (n + 1) × (Fin (n + 1) → U) × (Fin (n + 1) → U)

noncomputable def observedDecisionGap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) : ℝ :=
  productCompressionLoss F (productResponse q F) selected -
    productCompressionLoss F (productResponse q F) competitor

noncomputable def positiveObservedDecisionGap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1))) : ℝ :=
  max (observedDecisionGap q F selected competitor) 0

noncomputable def largestObservedCycleMagnitude {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  maxVal (fun a : CycleAtom n U ↦
    |cycleFunctional a.1 a.2.1 a.2.2 F|)

theorem cycleMagnitude_le_largest {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    |cycleFunctional i x c F| ≤ largestObservedCycleMagnitude F := by
  exact le_maxVal
    (fun a : CycleAtom n U ↦ |cycleFunctional a.1 a.2.1 a.2.2 F|)
    (i, x, c)

theorem largestObservedCycleMagnitude_nonnegative {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) :
    0 ≤ largestObservedCycleMagnitude F := by
  rcases exists_eq_maxVal
      (fun a : CycleAtom n U ↦ |cycleFunctional a.1 a.2.1 a.2.2 F|) with
    ⟨a, ha⟩
  unfold largestObservedCycleMagnitude
  rw [← ha]
  exact abs_nonneg _

theorem exists_cycle_attaining_largest {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) :
    ∃ a : CycleAtom n U,
      |cycleFunctional a.1 a.2.1 a.2.2 F| =
        largestObservedCycleMagnitude F := by
  exact exists_eq_maxVal _

private theorem feasible_mass_lower_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hGap : 0 < observedDecisionGap q F selected competitor)
    (hCycle : 0 < largestObservedCycleMagnitude F)
    {mass : ℝ}
    (h : HasPAECWithMass q F selected competitor mass) :
    2 * observedDecisionGap q F selected competitor /
        largestObservedCycleMagnitude F ≤ mass := by
  rcases h with ⟨r, i, x, c, alpha, correction,
    hCorrection, hCertificate, hMass⟩
  have hCombination := finite_cycle_combination_bound F
    (largestObservedCycleMagnitude F) i x c alpha
    (fun a ↦ cycleMagnitude_le_largest F (i a) (x a) (c a))
  have hSigned :
      (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) ≤
        largestObservedCycleMagnitude F * ∑ a, |alpha a| :=
    (le_abs_self _).trans hCombination
  have hGapMass :
      2 * observedDecisionGap q F selected competitor ≤
        largestObservedCycleMagnitude F * mass := by
    calc
      2 * observedDecisionGap q F selected competitor ≤
          (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) +
            correction := hCertificate
      _ ≤ largestObservedCycleMagnitude F * ∑ a, |alpha a| := by
        linarith
      _ ≤ largestObservedCycleMagnitude F * mass :=
        mul_le_mul_of_nonneg_left hMass (le_of_lt hCycle)
  apply (div_le_iff₀ hCycle).2
  simpa [mul_comm] using hGapMass

private theorem exact_rescaled_cycle_is_feasible {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hGap : 0 < observedDecisionGap q F selected competitor)
    (hCycle : 0 < largestObservedCycleMagnitude F) :
    HasPAECWithMass q F selected competitor
      (2 * observedDecisionGap q F selected competitor /
        largestObservedCycleMagnitude F) := by
  rcases exists_cycle_attaining_largest F with ⟨a, ha⟩
  let v := cycleFunctional a.1 a.2.1 a.2.2 F
  have hvAbs : |v| = largestObservedCycleMagnitude F := ha
  have hv : v ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hvAbs
    linarith
  refine ⟨1, (fun _ ↦ a.1), (fun _ ↦ a.2.1), (fun _ ↦ a.2.2),
    (fun _ ↦ 2 * observedDecisionGap q F selected competitor / v),
    0, by norm_num, ?_, ?_⟩
  · simp only [Fin.sum_univ_one, add_zero]
    change 2 * observedDecisionGap q F selected competitor ≤
      (2 * observedDecisionGap q F selected competitor / v) * v
    rw [div_mul_cancel₀ _ hv]
  · simp only [Fin.sum_univ_one]
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos hGap, hvAbs]

/-- Main degeneracy audit: in the nontrivial regime, the legacy atomic mass
is exactly a normalized observed gap.  Its coefficients may adapt to this
single numerical `F`, so it must not be marketed as uniform complexity. -/
theorem paecAtomicMass_eq_normalized_observed_gap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hGap : 0 < observedDecisionGap q F selected competitor)
    (hCycle : 0 < largestObservedCycleMagnitude F) :
    paecAtomicMass q F selected competitor =
      2 * positiveObservedDecisionGap q F selected competitor /
        largestObservedCycleMagnitude F := by
  have hPositive : positiveObservedDecisionGap q F selected competitor =
      observedDecisionGap q F selected competitor := by
    simp [positiveObservedDecisionGap, max_eq_left (le_of_lt hGap)]
  rw [hPositive]
  apply le_antisymm
  · exact paecAtomicMass_le_of_feasible q F selected competitor
      (exact_rescaled_cycle_is_feasible q F selected competitor hGap hCycle)
  · unfold paecAtomicMass
    apply le_csInf
    · exact ⟨_, exact_rescaled_cycle_is_feasible q F selected competitor
        hGap hCycle⟩
    · intro mass hmass
      exact feasible_mass_lower_bound q F selected competitor hGap hCycle hmass

/-- A nonpositive observed decision gap has a zero-mass empty certificate. -/
theorem zero_mass_feasible_of_nonpositive_gap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hGap : observedDecisionGap q F selected competitor ≤ 0) :
    HasPAECWithMass q F selected competitor 0 := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    0, by norm_num, ?_, ?_⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    change 2 * observedDecisionGap q F selected competitor ≤ 0
    linarith
  · simp

theorem paecAtomicMass_eq_zero_of_nonpositive_gap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hGap : observedDecisionGap q F selected competitor ≤ 0) :
    paecAtomicMass q F selected competitor = 0 := by
  have hzero := zero_mass_feasible_of_nonpositive_gap q F selected competitor hGap
  apply le_antisymm
  · exact paecAtomicMass_le_of_feasible q F selected competitor hzero
  · exact paecAtomicMass_nonnegative q F selected competitor ⟨0, hzero⟩

/-- If every observed cycle is zero while the observed gap is positive, no
legacy PAEC certificate exists.  This records the empty-feasible-set edge
case separately instead of treating `sInf ∅` as a scientific complexity. -/
theorem no_PAEC_of_positive_gap_and_zero_cycle_max {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hGap : 0 < observedDecisionGap q F selected competitor)
    (hCycle : largestObservedCycleMagnitude F = 0) :
    ¬ ∃ mass, HasPAECWithMass q F selected competitor mass := by
  rintro ⟨mass, r, i, x, c, alpha, correction,
    hCorrection, hCertificate, hMass⟩
  have hCombination := finite_cycle_combination_bound F 0 i x c alpha
    (fun a ↦ by
      have h := cycleMagnitude_le_largest F (i a) (x a) (c a)
      rw [← cycleFunctional_eq_mixedDifference]
      simpa [hCycle] using h)
  have hSigned :
      (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) ≤ 0 := by
    calc
      _ ≤ |∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F| :=
        le_abs_self _
      _ ≤ 0 * ∑ a, |alpha a| := hCombination
      _ = 0 := zero_mul _
  change 0 < productCompressionLoss F (productResponse q F) selected -
    productCompressionLoss F (productResponse q F) competitor at hGap
  linarith

/-- Because the legacy object uses `sInf` in `ℝ`, an empty certificate set is
assigned zero.  This is another reason it must not be used as a uniform
complexity without an explicit feasibility premise. -/
theorem paecAtomicMass_eq_zero_when_certificate_set_empty {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected competitor : Finset (Fin (n + 1)))
    (hEmpty : ¬ ∃ mass, HasPAECWithMass q F selected competitor mass) :
    paecAtomicMass q F selected competitor = 0 := by
  unfold paecAtomicMass
  have hSet : {mass : ℝ | HasPAECWithMass q F selected competitor mass} = ∅ := by
    ext mass
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hmass
    exact hEmpty ⟨mass, hmass⟩
  rw [hSet, Real.sInf_empty]

end CIGAMF.P13.D6PAECAtomicMassDegeneracy
