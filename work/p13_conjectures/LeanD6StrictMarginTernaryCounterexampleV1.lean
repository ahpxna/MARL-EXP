import Mathlib
import «LeanD6NormalizedBalancedTernaryCounterexampleV1»
import «LeanD6InteractionContrastProfileV1»
import «LeanD6TernaryInteractionContrastRankV1»

/-!
# Strict-margin version of the normalized ternary D6 counterexample

The perturbation is coordinate-additive.  Thus it preserves every mixed
difference and every centered interaction profile, while separating the two
selected response spans from the two rejected spans by exactly `1 / 20`.
This is an exact rational calculation; no numerical approximation is used.
-/

namespace CIGAMF.P13.D6StrictMarginTernaryCounterexample

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6ResidualCentering
open CIGAMF.P13.D6NormalizedBalancedTernaryCounterexample

noncomputable def strictComponent (i : Fin 4) (u : Fin 3) : ℝ :=
  match i with
  | ⟨0, _⟩ => if u = 0 then 0 else 1 / 20
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => if u = 0 then 0 else 1 / 20
  | ⟨3, _⟩ => if u = 0 then 0 else 1 / 10

noncomputable def strictPerturbation (z : Fin 4 → Fin 3) : ℝ :=
  coordinateAdditiveWorld strictComponent 0 z

noncomputable def strictMarginWorld (z : Fin 4 → Fin 3) : ℝ :=
  ternaryBalancedWorld4 z + strictPerturbation z

private theorem strictPerturbation_eq (z : Fin 4 → Fin 3) :
    strictPerturbation z =
      (if z 0 = 0 then 0 else 1 / 20) +
      (if z 2 = 0 then 0 else 1 / 20) +
      (if z 3 = 0 then 0 else 1 / 10) := by
  unfold strictPerturbation coordinateAdditiveWorld strictComponent
  simp [Fin.sum_univ_succ]
  ring

private theorem strictPerturbation_is_coordinate_additive (z : Fin 4 → Fin 3) :
    strictPerturbation z = coordinateAdditiveWorld strictComponent 0 z := rfl

private theorem strict_mixedDifference_eq (i : Fin 4)
    (x c : Fin 4 → Fin 3) :
    mixedDifference strictMarginWorld i x c =
      mixedDifference ternaryBalancedWorld4 i x c := by
  have hzero := mixedDifference_sum_coordinates_zero strictComponent (0 : ℝ) i x c
  change mixedDifference
      (fun z ↦ ternaryBalancedWorld4 z +
        coordinateAdditiveWorld strictComponent 0 z) i x c = _
  unfold mixedDifference at hzero ⊢
  simp only [coordinateAdditiveWorld] at hzero ⊢
  linarith

theorem strictMarginTernary_delta_le_one :
    UnitInteractionBound strictMarginWorld := by
  intro i x c
  rw [strict_mixedDifference_eq]
  exact ternaryBalanced_unitInteraction i x c

theorem strictMarginTernary_profile_eq
    (i : Fin 4) (u0 u : Fin 3) (z : Fin 4 → Fin 3) :
    interactionContrastProfile pointMassTernary4 strictMarginWorld i u0 u z =
      interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4 i u0 u z := by
  change interactionContrastProfile pointMassTernary4
      (fun x ↦ ternaryBalancedWorld4 x +
        coordinateAdditiveWorld strictComponent 0 x) i u0 u z = _
  exact interactionContrastProfile_coordinateAdditive_invariant
    pointMassTernary4 ternaryBalancedWorld4 strictComponent 0
    pointMassTernary4_hNorm i u0 u z

private theorem update_z4t_strict_normal_form (i : Fin 4) (u : Fin 3) :
    Function.update z4t i u = ternaryInsertAtZero4 i u := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [z4t, a4t, ternaryInsertAtZero4, Function.update]

private theorem strictPerturbation_response (i : Fin 4) (u : Fin 3) :
    productResponse pointMassTernary4 strictPerturbation i u =
      strictComponent i u := by
  rw [pointMassTernary4_response, update_z4t_strict_normal_form]
  rw [strictPerturbation_eq]
  fin_cases i <;> fin_cases u <;>
    simp [ternaryInsertAtZero4, a4t, strictComponent] <;> norm_num

private theorem strictMargin_response_table (i : Fin 4) (u : Fin 3) :
    productResponse pointMassTernary4 strictMarginWorld i u =
      ternaryResponseTable4 i u + strictComponent i u := by
  rw [pointMassTernary4_response]
  unfold strictMarginWorld
  calc
    ternaryBalancedWorld4 (Function.update z4t i u) +
        strictPerturbation (Function.update z4t i u) =
      productResponse pointMassTernary4 ternaryBalancedWorld4 i u +
        productResponse pointMassTernary4 strictPerturbation i u := by
          rw [pointMassTernary4_response, pointMassTernary4_response]
    _ = _ := by rw [ternaryBalanced_response_table, strictPerturbation_response]

private theorem fin3_cases (u : Fin 3) : u = 0 ∨ u = 1 ∨ u = 2 := by
  fin_cases u <;> simp

private theorem selected_sum (g : Fin 4 → ℝ) :
    ternarySelected4.sum g = g 0 + g 2 := by
  simp [ternarySelected4]

private theorem competitor_sum (g : Fin 4 → ℝ) :
    ternaryCompetitor4.sum g = g 1 + g 3 := by
  simp [ternaryCompetitor4]

private theorem strictSelected_bounds (x : Fin 4 → Fin 3) :
    (-9 / 10 : ℝ) ≤ strictMarginWorld x - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (x j)) ∧
    strictMarginWorld x - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (x j)) ≤
      41 / 10 := by
  simp only [strictMargin_response_table]
  rw [selected_sum]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    simp [strictMarginWorld, strictPerturbation_eq,
      strictComponent, ternaryBalancedWorld4, ternaryResponseTable4,
      h0, h1, h2, h3, h20, h21] <;> norm_num

private theorem strictCompetitor_bounds (x : Fin 4 → Fin 3) :
    (2 : ℝ) ≤ strictMarginWorld x - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (x j)) ∧
    strictMarginWorld x - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (x j)) ≤
      31 / 10 := by
  simp only [strictMargin_response_table]
  rw [competitor_sum]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    simp [strictMarginWorld, strictPerturbation_eq,
      strictComponent, ternaryBalancedWorld4, ternaryResponseTable4,
      h0, h1, h2, h3, h20, h21] <;> norm_num

private theorem strictSelected_min_eval :
    strictMarginWorld ternarySelectedMin4 - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
        (ternarySelectedMin4 j)) = -9 / 10 := by
  simp only [strictMargin_response_table]
  rw [selected_sum]
  norm_num [strictMarginWorld, strictPerturbation_eq,
    strictComponent, ternaryBalancedWorld4, ternaryResponseTable4]

private theorem strictSelected_max_eval :
    strictMarginWorld ternarySelectedMax4 - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
        (ternarySelectedMax4 j)) = 41 / 10 := by
  simp only [strictMargin_response_table]
  rw [selected_sum]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [strictMarginWorld, strictPerturbation_eq,
    strictComponent, ternaryBalancedWorld4, ternaryResponseTable4, h20, h21]

def strictCompetitorMax : Fin 4 → Fin 3 := a4t 2 1 2 1
def strictCompetitorMin : Fin 4 → Fin 3 := z4t

/-- The additive strict-margin perturbation changes only the response maximizer
at coordinate three: action `2`, not the old tied action `0`, is now unique. -/
def strictResponseMax : Fin 4 → Fin 3 := a4t 1 2 1 2

@[simp] private theorem strictResponseMax_0 : strictResponseMax 0 = 1 := by rfl
@[simp] private theorem strictResponseMax_1 : strictResponseMax 1 = 2 := by rfl
@[simp] private theorem strictResponseMax_2 : strictResponseMax 2 = 1 := by rfl
@[simp] private theorem strictResponseMax_3 : strictResponseMax 3 = 2 := by rfl

private theorem strictCompetitor_min_eval :
    strictMarginWorld strictCompetitorMin - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
        (strictCompetitorMin j)) = 2 := by
  simp only [strictMargin_response_table]
  rw [competitor_sum]
  norm_num [strictCompetitorMin, z4t, strictMarginWorld,
    strictPerturbation_eq, strictComponent,
    ternaryBalancedWorld4, ternaryResponseTable4]

private theorem strictCompetitor_max_eval :
    strictMarginWorld strictCompetitorMax - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
        (strictCompetitorMax j)) = 31 / 10 := by
  simp only [strictMargin_response_table]
  rw [competitor_sum]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [strictCompetitorMax, strictMarginWorld, strictPerturbation_eq,
    strictComponent, ternaryBalancedWorld4,
    ternaryResponseTable4, h20, h21]

private theorem compressionLoss_eq_of_bounds
    (S : Finset (Fin 4)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ strictMarginWorld x -
        S.sum (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (x j)) ∧
      strictMarginWorld x -
        S.sum (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (x j)) ≤ hi)
    (xmin xmax : Fin 4 → Fin 3)
    (hmin : strictMarginWorld xmin -
        S.sum (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (xmin j)) = lo)
    (hmax : strictMarginWorld xmax -
        S.sum (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (xmax j)) = hi) :
    productCompressionLoss strictMarginWorld
      (productResponse pointMassTernary4 strictMarginWorld) S = (hi - lo) / 2 := by
  let r : (Fin 4 → Fin 3) → ℝ := fun x ↦ strictMarginWorld x -
    S.sum (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (x j))
  have hrmax : maxVal r = hi := by
    apply le_antisymm
    · exact maxVal_le r (fun x ↦ (hbound x).2)
    · calc
        hi = r xmax := hmax.symm
        _ ≤ maxVal r := le_maxVal r xmax
  have hrmin : minVal r = lo := by
    apply le_antisymm
    · calc
        minVal r ≤ r xmin := minVal_le r xmin
        _ = lo := hmin
    · exact le_minVal r (fun x ↦ (hbound x).1)
  unfold productCompressionLoss
  change (maxVal r - minVal r) / 2 = (hi - lo) / 2
  rw [hrmax, hrmin]

theorem strictMarginTernary_selected_loss :
    productCompressionLoss strictMarginWorld
      (productResponse pointMassTernary4 strictMarginWorld) ternarySelected4 = 5 / 2 := by
  convert compressionLoss_eq_of_bounds ternarySelected4 (-9 / 10) (41 / 10)
    strictSelected_bounds ternarySelectedMin4 ternarySelectedMax4
    strictSelected_min_eval strictSelected_max_eval using 1 <;> norm_num

theorem strictMarginTernary_competitor_loss :
    productCompressionLoss strictMarginWorld
      (productResponse pointMassTernary4 strictMarginWorld) ternaryCompetitor4 = 11 / 20 := by
  convert compressionLoss_eq_of_bounds ternaryCompetitor4 2 (31 / 10)
    strictCompetitor_bounds strictCompetitorMin strictCompetitorMax
    strictCompetitor_min_eval strictCompetitor_max_eval using 1 <;> norm_num

private theorem strict_response_max (i : Fin 4) (u : Fin 3) :
    productResponse pointMassTernary4 strictMarginWorld i u ≤
      productResponse pointMassTernary4 strictMarginWorld i (strictResponseMax i) := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i
  · change productResponse pointMassTernary4 strictMarginWorld 0 u ≤
      productResponse pointMassTernary4 strictMarginWorld 0 1
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]
  · change productResponse pointMassTernary4 strictMarginWorld 1 u ≤
      productResponse pointMassTernary4 strictMarginWorld 1 2
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]
  · change productResponse pointMassTernary4 strictMarginWorld 2 u ≤
      productResponse pointMassTernary4 strictMarginWorld 2 1
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]
  · change productResponse pointMassTernary4 strictMarginWorld 3 u ≤
      productResponse pointMassTernary4 strictMarginWorld 3 2
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]

private theorem strict_response_min (i : Fin 4) (u : Fin 3) :
    productResponse pointMassTernary4 strictMarginWorld i (ternaryResponseMin4 i) ≤
      productResponse pointMassTernary4 strictMarginWorld i u := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i
  · change productResponse pointMassTernary4 strictMarginWorld 0 0 ≤
      productResponse pointMassTernary4 strictMarginWorld 0 u
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]
  · change productResponse pointMassTernary4 strictMarginWorld 1 1 ≤
      productResponse pointMassTernary4 strictMarginWorld 1 u
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]
  · change productResponse pointMassTernary4 strictMarginWorld 2 0 ≤
      productResponse pointMassTernary4 strictMarginWorld 2 u
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]
  · change productResponse pointMassTernary4 strictMarginWorld 3 1 ≤
      productResponse pointMassTernary4 strictMarginWorld 3 u
    fin_cases u <;> norm_num [strictMargin_response_table, strictComponent,
      ternaryResponseTable4, h20, h21]

private theorem strict_response_osc (i : Fin 4) :
    osc (productResponse pointMassTernary4 strictMarginWorld i) =
      productResponse pointMassTernary4 strictMarginWorld i (strictResponseMax i) -
        productResponse pointMassTernary4 strictMarginWorld i (ternaryResponseMin4 i) := by
  unfold osc
  rw [le_antisymm (maxVal_le _ (strict_response_max i))
      (le_maxVal _ (strictResponseMax i)),
    le_antisymm (minVal_le _ (ternaryResponseMin4 i))
      (le_minVal _ (strict_response_min i))]

theorem strictMarginTernary_response_spans :
    osc (productResponse pointMassTernary4 strictMarginWorld 0) = 21 / 20 ∧
    osc (productResponse pointMassTernary4 strictMarginWorld 1) = 1 ∧
    osc (productResponse pointMassTernary4 strictMarginWorld 2) = 21 / 20 ∧
    osc (productResponse pointMassTernary4 strictMarginWorld 3) = 1 := by
  constructor
  · rw [strict_response_osc]
    change productResponse pointMassTernary4 strictMarginWorld 0 1 -
      productResponse pointMassTernary4 strictMarginWorld 0 0 = 21 / 20
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    norm_num [strictMargin_response_table, strictComponent,
      strictResponseMax_0, strictResponseMax_1, strictResponseMax_2,
      strictResponseMax_3, ternaryResponseMin4_0, ternaryResponseMin4_1,
      ternaryResponseMin4_2, ternaryResponseMin4_3,
      ternaryResponseTable4, h20, h21]
  constructor
  · rw [strict_response_osc]
    change productResponse pointMassTernary4 strictMarginWorld 1 2 -
      productResponse pointMassTernary4 strictMarginWorld 1 1 = 1
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    norm_num [strictMargin_response_table, strictComponent,
      strictResponseMax_0, strictResponseMax_1, strictResponseMax_2,
      strictResponseMax_3, ternaryResponseMin4_0, ternaryResponseMin4_1,
      ternaryResponseMin4_2, ternaryResponseMin4_3,
      ternaryResponseTable4, h20, h21]
  constructor
  · rw [strict_response_osc]
    change productResponse pointMassTernary4 strictMarginWorld 2 1 -
      productResponse pointMassTernary4 strictMarginWorld 2 0 = 21 / 20
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    norm_num [strictMargin_response_table, strictComponent,
      strictResponseMax_0, strictResponseMax_1, strictResponseMax_2,
      strictResponseMax_3, ternaryResponseMin4_0, ternaryResponseMin4_1,
      ternaryResponseMin4_2, ternaryResponseMin4_3,
      ternaryResponseTable4, h20, h21]
  · rw [strict_response_osc]
    change productResponse pointMassTernary4 strictMarginWorld 3 2 -
      productResponse pointMassTernary4 strictMarginWorld 3 1 = 1
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    norm_num [strictMargin_response_table, strictComponent,
      strictResponseMax_0, strictResponseMax_1, strictResponseMax_2,
      strictResponseMax_3, ternaryResponseMin4_0, ternaryResponseMin4_1,
      ternaryResponseMin4_2, ternaryResponseMin4_3,
      ternaryResponseTable4, h20, h21]

theorem strictMarginTernary_is_strict_topC :
    ∀ i ∈ ternarySelected4, ∀ j ∉ ternarySelected4,
      osc (productResponse pointMassTernary4 strictMarginWorld j) <
        osc (productResponse pointMassTernary4 strictMarginWorld i) := by
  intro i hi j hj
  rcases strictMarginTernary_response_spans with ⟨h0, h1, h2, h3⟩
  fin_cases i <;> fin_cases j <;>
    simp [ternarySelected4] at hi hj ⊢ <;>
    linarith

def strictMarginCell : ActiveDecisionCell 3 (Fin 3) where
  q := pointMassTernary4
  selected := ternarySelected4
  competitor := ternaryCompetitor4
  selectedMax := ternarySelectedMax4
  selectedMin := ternarySelectedMin4
  competitorMax := strictCompetitorMax
  competitorMin := strictCompetitorMin
  responseMax := strictResponseMax
  responseMin := ternaryResponseMin4

theorem strictMarginTernary_cell_valid : strictMarginCell.Valid strictMarginWorld := by
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨by simp [strictMarginCell, ternarySelected4, ternaryCompetitor4],
    ?_, ?_, ?_, ?_, strict_response_max, strict_response_min, ?_⟩
  · intro z
    change strictMarginWorld z - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (z j)) ≤
      strictMarginWorld ternarySelectedMax4 - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
          (ternarySelectedMax4 j))
    rw [strictSelected_max_eval]
    exact (strictSelected_bounds z).2
  · intro z
    change strictMarginWorld ternarySelectedMin4 - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
          (ternarySelectedMin4 j)) ≤ strictMarginWorld z - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (z j))
    rw [strictSelected_min_eval]
    exact (strictSelected_bounds z).1
  · intro z
    change strictMarginWorld z - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (z j)) ≤
      strictMarginWorld strictCompetitorMax - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
          (strictCompetitorMax j))
    rw [strictCompetitor_max_eval]
    exact (strictCompetitor_bounds z).2
  · intro z
    change strictMarginWorld strictCompetitorMin - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j
          (strictCompetitorMin j)) ≤ strictMarginWorld z - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 strictMarginWorld j (z j))
    rw [strictCompetitor_min_eval]
    exact (strictCompetitor_bounds z).1
  · intro i hi j hj
    have h := strictMarginTernary_is_strict_topC i hi j hj
    rw [strict_response_osc i, strict_response_osc j] at h
    exact h.le

theorem strictMarginTernary_violates_m_minus_one :
    2 * (productCompressionLoss strictMarginWorld
        (productResponse pointMassTernary4 strictMarginWorld) ternarySelected4 -
      productCompressionLoss strictMarginWorld
        (productResponse pointMassTernary4 strictMarginWorld) ternaryCompetitor4) =
      39 / 10 := by
  rw [strictMarginTernary_selected_loss, strictMarginTernary_competitor_loss]
  norm_num

theorem strictMarginTernary_not_atMost_three :
    ¬ DecisionInteractionConstantAtMost strictMarginCell 3 := by
  intro h
  have hbad := h strictMarginWorld strictMarginTernary_cell_valid
    strictMarginTernary_delta_le_one
  change 2 * (productCompressionLoss strictMarginWorld
      (productResponse pointMassTernary4 strictMarginWorld) ternarySelected4 -
    productCompressionLoss strictMarginWorld
      (productResponse pointMassTernary4 strictMarginWorld) ternaryCompetitor4) ≤ 3 at hbad
  rw [strictMarginTernary_violates_m_minus_one] at hbad
  norm_num at hbad

end CIGAMF.P13.D6StrictMarginTernaryCounterexample
