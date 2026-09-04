import Mathlib
import «LeanD6PAECFin4»

/-!
# Counterexample to the direct span-surplus-to-canonical-Abel bridge

This quarantine module does **not** refute the D6 half-factor conjecture or
the possibility of another PAEC construction.  It refutes only the proposed
direct bridge which tries to infer the sign of the current canonical Fin-4
raw-response correction from Top-C ordering of *unsigned response spans*.

The all-zero point-mass reference has response spans `(3,2,1,1)`, hence
`{0,1}` is strict Top-C.  Nevertheless the canonical correction is `+1`.
The optional finite check also establishes the canonical selected-residual
active endpoints `1100` and `0011`, so the failure is not caused by omitting
that active-extrema branch condition.
-/

namespace CIGAMF.P13.D6CanonicalAbelRouteCounterexampleV1

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6PAECFin4

/-! The only nonzero cells are
`1000 = 3`, `0100 = -2`, `0010 = 1`, `0001 = -1`,
`1100 = 30`, and `0011 = -30`. -/
def abelRouteWorld4 (x : Fin 4 → Fin 2) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then
      if x 2 = 0 then
        if x 3 = 0 then 0 else -1
      else
        if x 3 = 0 then 1 else -30
    else
      if x 2 = 0 then
        if x 3 = 0 then -2 else 0
      else 0
  else
    if x 1 = 0 then
      if x 2 = 0 then
        if x 3 = 0 then 3 else 0
      else 0
    else
      if x 2 = 0 then
        if x 3 = 0 then 30 else 0
      else 0

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

@[simp] theorem abel_response_zero (j : Fin 4) :
    productResponse pointMass4 abelRouteWorld4 j 0 = 0 := by
  rw [pointMass4_response_zero]
  simp [abelRouteWorld4, z4, a4]

@[simp] theorem abel_response_one (j : Fin 4) :
    productResponse pointMass4 abelRouteWorld4 j 1 =
      ![(3 : ℝ), -2, 1, -1] j := by
  rw [pointMass4_response_one]
  fin_cases j <;> norm_num [abelRouteWorld4, e40, e41, e42, e43, a4]

theorem abel_response_span (j : Fin 4) :
    osc (productResponse pointMass4 abelRouteWorld4 j) =
      ![(3 : ℝ), 2, 1, 1] j := by
  rw [osc, maxVal_fin2, minVal_fin2]
  fin_cases j <;> norm_num

/-! The selected two rows strictly dominate every rejected row by span. -/
theorem selected4_strict_span_dominance :
    ∀ i ∈ selected4, ∀ j ∉ selected4,
      osc (productResponse pointMass4 abelRouteWorld4 j) <
        osc (productResponse pointMass4 abelRouteWorld4 i) := by
  intro i hi j hj
  rw [abel_response_span i, abel_response_span j]
  fin_cases i <;> fin_cases j <;> simp_all [selected4] <;> norm_num

theorem selected4_is_topC :
    IsTopKByScore
      (fun j ↦ osc (productResponse pointMass4 abelRouteWorld4 j))
      selected4 2 := by
  constructor
  · simp [selected4]
  · intro candidate hcard
    simp_rw [abel_response_span]
    fin_cases candidate <;> simp_all [selected4] <;> norm_num at * <;> omega

theorem abel_topCorrection4_eq_one :
    topCorrection4 abelRouteWorld4 = 1 := by
  norm_num [topCorrection4, abelRouteWorld4, z4, e40, e41, e42, e43, a4]

theorem abel_topCorrection4_positive :
    0 < topCorrection4 abelRouteWorld4 := by
  rw [abel_topCorrection4_eq_one]
  norm_num

/-! The first raw signed canonical correction premise specifically fails. -/
theorem canonical_h03_fails :
    ¬ (abelRouteWorld4 z4 - abelRouteWorld4 e43 ≤
      abelRouteWorld4 z4 - abelRouteWorld4 e40) := by
  norm_num [abelRouteWorld4, z4, e40, e43, a4]

/-! A finite check of the selected residual, included to rule out the
presentation loophole that the counterexample lives outside the canonical
active-extrema branch. -/
private theorem abel_rS4_bounds (x : Fin 4 → Fin 2) :
    -30 ≤ rS4 abelRouteWorld4 x ∧ rS4 abelRouteWorld4 x ≤ 29 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    simp [rS4, abelRouteWorld4, h0, h1, h2, h3] <;> norm_num

private theorem abel_rS4_s4 : rS4 abelRouteWorld4 s4 = 29 := by
  norm_num [rS4, abelRouteWorld4, s4, a4]

private theorem abel_rS4_t4 : rS4 abelRouteWorld4 t4 = -30 := by
  norm_num [rS4, abelRouteWorld4, t4, a4]

theorem canonical_selected_active_extrema :
    osc (rS4 abelRouteWorld4) =
      rS4 abelRouteWorld4 s4 - rS4 abelRouteWorld4 t4 := by
  have hmax : maxVal (rS4 abelRouteWorld4) = 29 := by
    apply le_antisymm
    · exact maxVal_le _ (fun x ↦ (abel_rS4_bounds x).2)
    · rw [← abel_rS4_s4]
      exact le_maxVal _ s4
  have hmin : minVal (rS4 abelRouteWorld4) = -30 := by
    apply le_antisymm
    · rw [← abel_rS4_t4]
      exact minVal_le _ t4
    · exact le_minVal _ (fun x ↦ (abel_rS4_bounds x).1)
  rw [osc, hmax, hmin, abel_rS4_s4, abel_rS4_t4]

/-! Consequently, Top-C by response spans (even together with the canonical
selected-residual active-extrema identity) cannot imply nonpositivity of the
current raw canonical correction. -/
theorem no_topC_active_to_canonical_correction_nonpos :
    ¬ (∀ F : (Fin 4 → Fin 2) → ℝ,
      IsTopKByScore (fun j ↦ osc (productResponse pointMass4 F j)) selected4 2 →
      osc (rS4 F) = rS4 F s4 - rS4 F t4 →
      topCorrection4 F ≤ 0) := by
  intro h
  have hc := h abelRouteWorld4 selected4_is_topC canonical_selected_active_extrema
  linarith [abel_topCorrection4_positive]

end CIGAMF.P13.D6CanonicalAbelRouteCounterexampleV1
