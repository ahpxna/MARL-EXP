import Mathlib
import «LeanD6OrderedAbelPAECV1»
import «LeanD6PAECFin4»
import «LeanD6PAECFin6»

/-!
# Canonical PAEC branches instantiate the ordered-Abel interface

This is a genuine compatibility check, not a universal construction.  The
already compiled point-mass `m=4` and `m=6` canonical branches have their
Top-C correction exactly equal to an Abel correction with constant weights.
Thus the ordered-Abel API represents real D6 certificate algebra rather than
an unrelated abstract interface.
-/

namespace CIGAMF.P13.D6CanonicalAbelAdapter

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6AbelSurplus
open CIGAMF.P13.D6OrderedAbelPAEC
open CIGAMF.P13.D6PAECFin4
open CIGAMF.P13.D6PAECFin6

private theorem point_sub_point_le_osc
    {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) (a b : A) : f a - f b ≤ osc f := by
  have ha := le_maxVal f a
  have hb := minVal_le f b
  simp only [osc]
  linarith

private theorem fin4_selected_loss_eq
    (F : (Fin 4 → Fin 2) → ℝ) :
    productCompressionLoss F (productResponse pointMass4 F) selected4 =
      osc (rS4 F) / 2 := by
  unfold productCompressionLoss
  rw [← rS4_eq_retained F]

private theorem fin4_rejected_loss_eq
    (F : (Fin 4 → Fin 2) → ℝ) :
    productCompressionLoss F (productResponse pointMass4 F) rejected4 =
      osc (rT4 F) / 2 := by
  unfold productCompressionLoss
  rw [← rT4_eq_retained F]

noncomputable def fin4Surplus (F : (Fin 4 → Fin 2) → ℝ) : ℕ → ℝ
  | 0 => (F z4 - F e40) - (F z4 - F e43)
  | 1 => (F z4 - F e41) - (F z4 - F e42)
  | _ => 0

noncomputable def unitWeight : ℕ → ℝ := fun _ ↦ 1

theorem fin4_correction_eq_abel
    (F : (Fin 4 → Fin 2) → ℝ) :
    abelCorrection (fin4Surplus F) unitWeight (2 - 1) = topCorrection4 F := by
  norm_num [abelCorrection, fin4Surplus, unitWeight, topCorrection4,
    Finset.sum_range_succ]
  ring

/-- The canonical `m=4` three-cycle branch is an actual ordered-Abel PAEC.
The `h03/h12` inequalities are exactly the two nonnegative ordered surpluses.
-/
theorem canonical_fin4_hasOrderedAbelPAEC
    (F : (Fin 4 → Fin 2) → ℝ)
    (h03 : F z4 - F e43 ≤ F z4 - F e40)
    (h12 : F z4 - F e42 ≤ F z4 - F e41)
    (hActive : osc (rS4 F) = rS4 F s4 - rS4 F t4) :
    HasOrderedAbelPAEC pointMass4 F selected4 rejected4 := by
  let i : Fin 3 → Fin 4 := ![1, 0, 1]
  let x : Fin 3 → Fin 4 → Fin 2 := ![s4, x4b, o4]
  let c : Fin 3 → Fin 4 → Fin 2 := fun _ ↦ z4
  let alpha : Fin 3 → ℝ := fun _ ↦ 1
  refine ⟨2, 3, i, x, c, alpha, fin4Surplus F, unitWeight,
    by norm_num, ?_, by simp [unitWeight], ?_, ?_, ?_⟩
  · intro r hr
    interval_cases r <;>
      simp [prefixSum, fin4Surplus, Finset.sum_range_succ] <;> linarith
  · intro j hj
    simp [unitWeight]
  · have hId := three_cycle_identity F
    have hT := point_sub_point_le_osc (rT4 F) z4 o4
    have hLossS := fin4_selected_loss_eq F
    have hLossT := fin4_rejected_loss_eq F
    have hCycles :
        (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) =
          cycleSum4 F := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      dsimp [alpha, i, x, c]
      simp only [one_mul, cycleFunctional_eq_mixedDifference]
      unfold cycleSum4
      ring
    rw [hCycles, fin4_correction_eq_abel]
    rw [hLossS, hLossT, hActive]
    linarith
  · norm_num [alpha]

private theorem fin6_selected_loss_eq
    (F : (Fin 6 → Fin 2) → ℝ) :
    productCompressionLoss F (productResponse pointMass6 F) selected6 =
      osc (rS6 F) / 2 := by
  unfold productCompressionLoss
  rw [← rS6_eq_retained F]

private theorem fin6_rejected_loss_eq
    (F : (Fin 6 → Fin 2) → ℝ) :
    productCompressionLoss F (productResponse pointMass6 F) rejected6 =
      osc (rT6 F) / 2 := by
  unfold productCompressionLoss
  rw [← rT6_eq_retained F]

noncomputable def fin6Surplus (F : (Fin 6 → Fin 2) → ℝ) : ℕ → ℝ
  | 0 => (F z6 - F e60) - (F z6 - F e65)
  | 1 => (F z6 - F e61) - (F z6 - F e64)
  | 2 => (F z6 - F e62) - (F z6 - F e63)
  | _ => 0

theorem fin6_correction_eq_abel
    (F : (Fin 6 → Fin 2) → ℝ) :
    abelCorrection (fin6Surplus F) unitWeight (3 - 1) = topCorrection6 F := by
  norm_num [abelCorrection, fin6Surplus, unitWeight, topCorrection6,
    Finset.sum_range_succ]
  ring

/-- The canonical `m=6` five-cycle branch is an actual ordered-Abel PAEC. -/
theorem canonical_fin6_hasOrderedAbelPAEC
    (F : (Fin 6 → Fin 2) → ℝ)
    (h05 : F z6 - F e65 ≤ F z6 - F e60)
    (h14 : F z6 - F e64 ≤ F z6 - F e61)
    (h23 : F z6 - F e63 ≤ F z6 - F e62)
    (hActive : osc (rS6 F) = rS6 F s6 - rS6 F t6) :
    HasOrderedAbelPAEC pointMass6 F selected6 rejected6 := by
  let i : Fin 5 → Fin 6 := ![1, 2, 0, 1, 2]
  let x : Fin 5 → Fin 6 → Fin 2 := ![p62, s6, b60, b61, o6]
  let c : Fin 5 → Fin 6 → Fin 2 := fun _ ↦ z6
  let alpha : Fin 5 → ℝ := fun _ ↦ 1
  refine ⟨3, 5, i, x, c, alpha, fin6Surplus F, unitWeight,
    by norm_num, ?_, by simp [unitWeight], ?_, ?_, ?_⟩
  · intro r hr
    interval_cases r <;>
      simp [prefixSum, fin6Surplus, Finset.sum_range_succ] <;> linarith
  · intro j hj
    simp [unitWeight]
  · have hId := five_cycle_identity F
    have hT := point_sub_point_le_osc (rT6 F) z6 o6
    have hLossS := fin6_selected_loss_eq F
    have hLossT := fin6_rejected_loss_eq F
    have hCycles :
        (∑ a, alpha a * cycleFunctional (i a) (x a) (c a) F) =
          cycleSum6 F := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      dsimp [alpha, i, x, c]
      simp only [one_mul, cycleFunctional_eq_mixedDifference]
      unfold cycleSum6
      ring
    rw [hCycles, fin6_correction_eq_abel]
    rw [hLossS, hLossT, hActive]
    linarith
  · norm_num [alpha]

end CIGAMF.P13.D6CanonicalAbelAdapter
