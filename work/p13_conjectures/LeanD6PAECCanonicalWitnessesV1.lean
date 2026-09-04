import Mathlib
import «LeanD6PAECExistence»
import «LeanD6PAECFin4»
import «LeanD6PAECFin6»
import «LeanD6H3Exchange»
import «LeanFunctionalRankingV6»

/-!
# Explicit PAEC witnesses for the compiled canonical branches

This module upgrades the symbolic `m = 4` and `m = 6` branch inequalities to
the actual `HasPAECForPair` object.  It deliberately does **not** claim that
an arbitrary Top-C pair can be reduced to either canonical branch: the
required branch/relabeling theorem remains the open universal PAEC-existence
step.
-/

namespace CIGAMF.P13.D6PAECCanonicalWitnesses

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6PAECExistence
open CIGAMF.P13.D6PAECFin4
open CIGAMF.P13.D6PAECFin6
open CIGAMF.P13.D6H3Exchange
open CIGAMF.V6.FunctionalRanking

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

/-- The three-cycle symbolic `m = 4` branch supplies an actual PAEC witness
of mass exactly `m - 1 = 3`. -/
theorem canonical_fin4_hasPAEC
    (F : (Fin 4 → Fin 2) → ℝ)
    (h03 : F z4 - F e43 ≤ F z4 - F e40)
    (h12 : F z4 - F e42 ≤ F z4 - F e41)
    (hActive : osc (rS4 F) = rS4 F s4 - rS4 F t4) :
    HasPAECForPair pointMass4 F selected4 rejected4 := by
  let i : Fin 3 → Fin 4 := ![1, 0, 1]
  let x : Fin 3 → Fin 4 → Fin 2 := ![s4, x4b, o4]
  let c : Fin 3 → Fin 4 → Fin 2 := fun _ ↦ z4
  let alpha : Fin 3 → ℝ := fun _ ↦ 1
  let correction : ℝ := topCorrection4 F
  refine ⟨3, i, x, c, alpha, correction, ?_, ?_, ?_⟩
  · exact topCorrection4_nonpos F h03 h12
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
    rw [hCycles]
    rw [hLossS, hLossT]
    rw [hActive]
    linarith
  · norm_num [alpha]

/-! ### A genuine Top-C branch reduction (`m = 4`) -/

private theorem pointMass4_span_of_nonpositive_row
    (F : (Fin 4 → Fin 2) → ℝ) (j : Fin 4)
    (hrow : productResponse pointMass4 F j 1 ≤
      productResponse pointMass4 F j 0) :
    osc (productResponse pointMass4 F j) =
      productResponse pointMass4 F j 0 - productResponse pointMass4 F j 1 := by
  rw [osc, maxVal_fin2, minVal_fin2]
  rw [max_eq_left hrow, min_eq_right hrow]

/-- In the negative-row point-mass sign branch, actual Top-C ordering derives
the two correction inequalities required by the symbolic three-cycle PAEC.

This is a real branch reduction, but it does not derive the active-extrema
assumption: selecting (or averaging over) arbitrary active extrema remains
the unresolved universal-PAEC step. -/
theorem canonical_fin4_hasPAEC_of_topC_negative_rows
    (F : (Fin 4 → Fin 2) → ℝ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse pointMass4 F j)) selected4 2)
    (hrow : ∀ j : Fin 4,
      productResponse pointMass4 F j 1 ≤ productResponse pointMass4 F j 0)
    (hActive : osc (rS4 F) = rS4 F s4 - rS4 F t4) :
    HasPAECForPair pointMass4 F selected4 rejected4 := by
  have h03score := topK_pairwise_score_order
    (fun j ↦ osc (productResponse pointMass4 F j)) selected4 2 hTop
    (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by simp [selected4])
    (by simp [selected4])
  have h12score := topK_pairwise_score_order
    (fun j ↦ osc (productResponse pointMass4 F j)) selected4 2 hTop
    (i := (1 : Fin 4)) (j := (2 : Fin 4)) (by simp [selected4])
    (by simp [selected4])
  rw [pointMass4_span_of_nonpositive_row F 3 (hrow 3),
    pointMass4_span_of_nonpositive_row F 0 (hrow 0)] at h03score
  rw [pointMass4_span_of_nonpositive_row F 2 (hrow 2),
    pointMass4_span_of_nonpositive_row F 1 (hrow 1)] at h12score
  have h03 : F z4 - F e43 ≤ F z4 - F e40 := by
    simpa using h03score
  have h12 : F z4 - F e42 ≤ F z4 - F e41 := by
    simpa using h12score
  exact canonical_fin4_hasPAEC F h03 h12 hActive

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

/-- The five-cycle symbolic `m = 6` branch supplies an actual PAEC witness
of mass exactly `m - 1 = 5`. -/
theorem canonical_fin6_hasPAEC
    (F : (Fin 6 → Fin 2) → ℝ)
    (h05 : F z6 - F e65 ≤ F z6 - F e60)
    (h14 : F z6 - F e64 ≤ F z6 - F e61)
    (h23 : F z6 - F e63 ≤ F z6 - F e62)
    (hActive : osc (rS6 F) = rS6 F s6 - rS6 F t6) :
    HasPAECForPair pointMass6 F selected6 rejected6 := by
  let i : Fin 5 → Fin 6 := ![1, 2, 0, 1, 2]
  let x : Fin 5 → Fin 6 → Fin 2 := ![p62, s6, b60, b61, o6]
  let c : Fin 5 → Fin 6 → Fin 2 := fun _ ↦ z6
  let alpha : Fin 5 → ℝ := fun _ ↦ 1
  let correction : ℝ := topCorrection6 F
  refine ⟨5, i, x, c, alpha, correction, ?_, ?_, ?_⟩
  · exact topCorrection6_nonpos F h05 h14 h23
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
    rw [hCycles]
    rw [hLossS, hLossT]
    rw [hActive]
    linarith
  · norm_num [alpha]

end CIGAMF.P13.D6PAECCanonicalWitnesses
