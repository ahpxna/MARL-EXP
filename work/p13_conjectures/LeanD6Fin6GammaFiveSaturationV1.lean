import Mathlib
import «LeanD6DecisionInteractionComplexityV1»
import «LeanD6PolyhedralActiveCellV1»
import «LeanD6CanonicalUniformDecisionCertificateV1»
import «LeanD6PAECFin6»
import «LeanFunctionalRankingV6»

/-!
# Exact Fin-6 saturation witness for the decision--interaction constant

This extension records the exact rational (in fact integer-valued) world
reconstructed from the authoritative active-cell LP run.  It proves that the
balanced coefficient `m - 1 = 5` is attained for the frozen point-mass cell.
It does not claim the still-open universal balanced-cell upper bound.
-/

namespace CIGAMF.P13.D6Fin6GammaFiveSaturation

set_option maxHeartbeats 2000000

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6PAECFin6
open CIGAMF.V6.FunctionalRanking

def gammaFiveWorld6 (x : Fin 6 → Fin 2) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then
      if x 2 = 0 then
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-3 : ℝ)
            else
              (-4 : ℝ)
          else
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-3 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-4 : ℝ)
          else
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-3 : ℝ)
      else
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-4 : ℝ)
          else
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-4 : ℝ)
          else
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
    else
      if x 2 = 0 then
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-4 : ℝ)
          else
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-3 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-4 : ℝ)
          else
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
      else
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-3 : ℝ)
          else
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-3 : ℝ)
          else
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
  else
    if x 1 = 0 then
      if x 2 = 0 then
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-2 : ℝ)
            else
              (-3 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-2 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-3 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-2 : ℝ)
      else
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-3 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-1 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-1 : ℝ)
    else
      if x 2 = 0 then
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-3 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-2 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-3 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-1 : ℝ)
      else
        if x 3 = 0 then
          if x 4 = 0 then
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-1 : ℝ)
        else
          if x 4 = 0 then
            if x 5 = 0 then
              (-1 : ℝ)
            else
              (-2 : ℝ)
          else
            if x 5 = 0 then
              (0 : ℝ)
            else
              (-1 : ℝ)

def gammaFiveSelected : Finset (Fin 6) := {1, 2, 3}
def gammaFiveCompetitor : Finset (Fin 6) := {0, 4, 5}

def gammaFiveSelectedMax : Fin 6 → Fin 2 := a6 1 0 0 0 1 0
def gammaFiveSelectedMin : Fin 6 → Fin 2 := a6 0 0 1 1 0 1
def gammaFiveCompetitorMax : Fin 6 → Fin 2 := a6 0 1 0 1 1 1
def gammaFiveCompetitorMin : Fin 6 → Fin 2 := a6 1 0 0 1 1 1

def gammaFiveResponseMax : Fin 6 → Fin 2 := a6 1 1 1 1 1 0
def gammaFiveResponseMin : Fin 6 → Fin 2 := a6 0 0 0 0 0 1

@[simp] theorem gammaFiveWorld6_z6 : gammaFiveWorld6 z6 = -3 := by
  rfl

@[simp] theorem gammaFiveWorld6_e60 : gammaFiveWorld6 e60 = -2 := by
  rfl

@[simp] theorem gammaFiveWorld6_e61 : gammaFiveWorld6 e61 = -2 := by
  rfl

@[simp] theorem gammaFiveWorld6_e62 : gammaFiveWorld6 e62 = -2 := by
  rfl

@[simp] theorem gammaFiveWorld6_e63 : gammaFiveWorld6 e63 = -2 := by
  rfl

@[simp] theorem gammaFiveWorld6_e64 : gammaFiveWorld6 e64 = -2 := by
  rfl

@[simp] theorem gammaFiveWorld6_e65 : gammaFiveWorld6 e65 = -4 := by
  rfl

@[simp] theorem gammaFiveWorld6_selectedMin :
    gammaFiveWorld6 gammaFiveSelectedMin = -4 := by
  rfl

@[simp] theorem gammaFiveWorld6_selectedMax :
    gammaFiveWorld6 gammaFiveSelectedMax = 0 := by
  rfl

@[simp] theorem gammaFiveWorld6_competitorMin :
    gammaFiveWorld6 gammaFiveCompetitorMin = -2 := by
  rfl

@[simp] theorem gammaFiveWorld6_competitorMax :
    gammaFiveWorld6 gammaFiveCompetitorMax = -2 := by
  rfl

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem gammaFive_hWeight :
    ∀ c, 0 ≤ jointWeight pointMass6 c := by
  intro c
  rw [pointMass6_jointWeight]
  split <;> norm_num

theorem gammaFive_hNorm :
    ∑ c, jointWeight pointMass6 c = 1 := by
  classical
  simp_rw [pointMass6_jointWeight]
  rw [Finset.sum_eq_single z6]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

@[simp] theorem gammaFive_response_zero (j : Fin 6) :
    productResponse pointMass6 gammaFiveWorld6 j 0 = -3 := by
  rw [pointMass6_response_zero]
  fin_cases j <;> simp [gammaFiveWorld6, z6, a6]

@[simp] theorem gammaFive_response_one (j : Fin 6) :
    productResponse pointMass6 gammaFiveWorld6 j 1 =
      ![(-2 : ℝ), -2, -2, -2, -2, -4] j := by
  rw [pointMass6_response_one]
  fin_cases j <;>
    simp [gammaFiveWorld6, e60, e61, e62, e63, e64, e65, a6]

theorem gammaFive_response_span (j : Fin 6) :
    osc (productResponse pointMass6 gammaFiveWorld6 j) = 1 := by
  rw [osc, maxVal_fin2, minVal_fin2]
  fin_cases j <;> simp <;> norm_num

theorem gammaFive_selected_is_topC :
    IsTopKByScore
      (fun j ↦ osc (productResponse pointMass6 gammaFiveWorld6 j))
      gammaFiveSelected 3 := by
  rw [isTopKByScore_iff_pairwise]
  refine ⟨by simp [gammaFiveSelected], ?_⟩
  intro i hi j hj
  simp_rw [gammaFive_response_span]
  exact le_rfl

noncomputable def gammaFiveContrast (i : Fin 6)
    (x : Fin 6 → Fin 2) : ℝ :=
  gammaFiveWorld6 (Function.update x i 1) -
    gammaFiveWorld6 (Function.update x i 0)

noncomputable def gammaFiveContrastLo (i : Fin 6) : ℝ :=
  ![(1 : ℝ), 0, 0, 0, 1, -2] i

noncomputable def gammaFiveContrastHi (i : Fin 6) : ℝ :=
  ![(2 : ℝ), 1, 1, 1, 2, -1] i

private theorem gammaFive_contrast_bounds (i : Fin 6)
    (x : Fin 6 → Fin 2) :
    gammaFiveContrastLo i ≤ gammaFiveContrast i x ∧
      gammaFiveContrast i x ≤ gammaFiveContrastHi i := by
  fin_cases i <;>
    rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    rcases fin2_zero_or_one (x 4) with h4 | h4 <;>
    rcases fin2_zero_or_one (x 5) with h5 | h5 <;>
    simp [gammaFiveContrast, gammaFiveContrastLo, gammaFiveContrastHi,
      gammaFiveWorld6, h0, h1, h2, h3, h4, h5, Function.update] <;>
    norm_num

private theorem gammaFive_contrast_width (i : Fin 6) :
    gammaFiveContrastHi i - gammaFiveContrastLo i = 1 := by
  fin_cases i <;>
    norm_num [gammaFiveContrastHi, gammaFiveContrastLo]

private theorem mixed_eq_zero_of_zero_zero
    (i : Fin 6) (x c : Fin 6 → Fin 2)
    (hx : x i = 0) (hc : c i = 0) :
    mixedDifference gammaFiveWorld6 i x c = 0 := by
  unfold mixedDifference
  have hxu : Function.update x i (0 : Fin 2) = x := by
    exact Function.update_eq_self_iff.mpr hx.symm
  have hcu : Function.update c i (0 : Fin 2) = c := by
    exact Function.update_eq_self_iff.mpr hc.symm
  rw [hx, hc, hxu, hcu]
  ring

private theorem mixed_eq_zero_of_one_one
    (i : Fin 6) (x c : Fin 6 → Fin 2)
    (hx : x i = 1) (hc : c i = 1) :
    mixedDifference gammaFiveWorld6 i x c = 0 := by
  unfold mixedDifference
  have hxu : Function.update x i (1 : Fin 2) = x := by
    exact Function.update_eq_self_iff.mpr hx.symm
  have hcu : Function.update c i (1 : Fin 2) = c := by
    exact Function.update_eq_self_iff.mpr hc.symm
  rw [hx, hc, hxu, hcu]
  ring

private theorem mixed_eq_c_minus_x
    (i : Fin 6) (x c : Fin 6 → Fin 2)
    (hx : x i = 0) (hc : c i = 1) :
    mixedDifference gammaFiveWorld6 i x c =
      gammaFiveContrast i c - gammaFiveContrast i x := by
  unfold mixedDifference gammaFiveContrast
  have hxu : Function.update x i (0 : Fin 2) = x := by
    exact Function.update_eq_self_iff.mpr hx.symm
  have hcu : Function.update c i (1 : Fin 2) = c := by
    exact Function.update_eq_self_iff.mpr hc.symm
  rw [hx, hc, hxu, hcu]
  ring

private theorem mixed_eq_x_minus_c
    (i : Fin 6) (x c : Fin 6 → Fin 2)
    (hx : x i = 1) (hc : c i = 0) :
    mixedDifference gammaFiveWorld6 i x c =
      gammaFiveContrast i x - gammaFiveContrast i c := by
  unfold mixedDifference gammaFiveContrast
  have hxu : Function.update x i (1 : Fin 2) = x := by
    exact Function.update_eq_self_iff.mpr hx.symm
  have hcu : Function.update c i (0 : Fin 2) = c := by
    exact Function.update_eq_self_iff.mpr hc.symm
  rw [hx, hc, hxu, hcu]
  ring

theorem gammaFive_mixed_difference_bound :
    ∀ (i : Fin 6) (x c : Fin 6 → Fin 2),
      |mixedDifference gammaFiveWorld6 i x c| ≤ 1 := by
  intro i x c
  rcases fin2_zero_or_one (x i) with hx | hx <;>
    rcases fin2_zero_or_one (c i) with hc | hc
  · rw [mixed_eq_zero_of_zero_zero i x c hx hc]
    norm_num
  · rw [mixed_eq_c_minus_x i x c hx hc, abs_le]
    have hxB := gammaFive_contrast_bounds i x
    have hcB := gammaFive_contrast_bounds i c
    have hw := gammaFive_contrast_width i
    constructor <;> linarith
  · rw [mixed_eq_x_minus_c i x c hx hc, abs_le]
    have hxB := gammaFive_contrast_bounds i x
    have hcB := gammaFive_contrast_bounds i c
    have hw := gammaFive_contrast_width i
    constructor <;> linarith
  · rw [mixed_eq_zero_of_one_one i x c hx hc]
    norm_num

private theorem compressionLoss_eq_of_bounds
    (S : Finset (Fin 6)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ gammaFiveWorld6 x -
        S.sum (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (x j)) ∧
      gammaFiveWorld6 x -
        S.sum (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (x j)) ≤ hi)
    (xmin xmax : Fin 6 → Fin 2)
    (hmin : gammaFiveWorld6 xmin -
        S.sum (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (xmin j)) = lo)
    (hmax : gammaFiveWorld6 xmax -
        S.sum (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (xmax j)) = hi) :
    productCompressionLoss gammaFiveWorld6
      (productResponse pointMass6 gammaFiveWorld6) S = (hi - lo) / 2 := by
  let r : (Fin 6 → Fin 2) → ℝ := fun x ↦ gammaFiveWorld6 x -
    S.sum (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (x j))
  have hrmax : maxVal r = hi := by
    apply le_antisymm
    · exact maxVal_le r (fun x ↦ (hbound x).2)
    · simpa [r, hmax] using le_maxVal r xmax
  have hrmin : minVal r = lo := by
    apply le_antisymm
    · simpa [r, hmin] using minVal_le r xmin
    · exact le_minVal r (fun x ↦ (hbound x).1)
  simp [productCompressionLoss, r, osc, hrmax, hrmin]

private theorem gammaFive_selected_bounds (x : Fin 6 → Fin 2) :
    3 ≤ gammaFiveWorld6 x - gammaFiveSelected.sum
      (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (x j)) ∧
    gammaFiveWorld6 x - gammaFiveSelected.sum
      (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (x j)) ≤ 9 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    rcases fin2_zero_or_one (x 4) with h4 | h4 <;>
    rcases fin2_zero_or_one (x 5) with h5 | h5 <;>
    simp [gammaFiveSelected, h0, h1, h2, h3, h4, h5] <;>
    simp [gammaFiveWorld6, h0, h1, h2, h3, h4, h5] <;> norm_num

private theorem gammaFive_competitor_bounds (x : Fin 6 → Fin 2) :
    6 ≤ gammaFiveWorld6 x - gammaFiveCompetitor.sum
      (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (x j)) ∧
    gammaFiveWorld6 x - gammaFiveCompetitor.sum
      (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (x j)) ≤ 7 := by
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    rcases fin2_zero_or_one (x 3) with h3 | h3 <;>
    rcases fin2_zero_or_one (x 4) with h4 | h4 <;>
    rcases fin2_zero_or_one (x 5) with h5 | h5 <;>
    simp [gammaFiveCompetitor, h0, h1, h2, h3, h4, h5] <;>
    simp [gammaFiveWorld6, h0, h1, h2, h3, h4, h5] <;> norm_num

private theorem gammaFive_selected_min :
    gammaFiveWorld6 gammaFiveSelectedMin -
      gammaFiveSelected.sum (fun j ↦
        productResponse pointMass6 gammaFiveWorld6 j (gammaFiveSelectedMin j)) = 3 := by
  rw [gammaFiveWorld6_selectedMin]
  simp [gammaFiveSelectedMin, gammaFiveSelected, a6] <;> norm_num

private theorem gammaFive_selected_max :
    gammaFiveWorld6 gammaFiveSelectedMax -
      gammaFiveSelected.sum (fun j ↦
        productResponse pointMass6 gammaFiveWorld6 j (gammaFiveSelectedMax j)) = 9 := by
  rw [gammaFiveWorld6_selectedMax]
  simp [gammaFiveSelectedMax, gammaFiveSelected, a6] <;> norm_num

private theorem gammaFive_competitor_min :
    gammaFiveWorld6 gammaFiveCompetitorMin -
      gammaFiveCompetitor.sum (fun j ↦
        productResponse pointMass6 gammaFiveWorld6 j (gammaFiveCompetitorMin j)) = 6 := by
  rw [gammaFiveWorld6_competitorMin]
  simp [gammaFiveCompetitorMin, gammaFiveCompetitor, a6] <;> norm_num

private theorem gammaFive_competitor_max :
    gammaFiveWorld6 gammaFiveCompetitorMax -
      gammaFiveCompetitor.sum (fun j ↦
        productResponse pointMass6 gammaFiveWorld6 j (gammaFiveCompetitorMax j)) = 7 := by
  rw [gammaFiveWorld6_competitorMax]
  simp [gammaFiveCompetitorMax, gammaFiveCompetitor, a6] <;> norm_num

theorem gammaFive_selected_loss :
    productCompressionLoss gammaFiveWorld6
      (productResponse pointMass6 gammaFiveWorld6) gammaFiveSelected = 3 := by
  convert compressionLoss_eq_of_bounds gammaFiveSelected 3 9
    gammaFive_selected_bounds gammaFiveSelectedMin gammaFiveSelectedMax
    gammaFive_selected_min gammaFive_selected_max using 1 <;> norm_num

theorem gammaFive_competitor_loss :
    productCompressionLoss gammaFiveWorld6
      (productResponse pointMass6 gammaFiveWorld6) gammaFiveCompetitor = 1 / 2 := by
  convert compressionLoss_eq_of_bounds gammaFiveCompetitor 6 7
    gammaFive_competitor_bounds gammaFiveCompetitorMin gammaFiveCompetitorMax
    gammaFive_competitor_min gammaFive_competitor_max using 1 <;> norm_num

theorem gammaFive_exact_saturation :
    2 * (productCompressionLoss gammaFiveWorld6
        (productResponse pointMass6 gammaFiveWorld6) gammaFiveSelected -
      productCompressionLoss gammaFiveWorld6
        (productResponse pointMass6 gammaFiveWorld6) gammaFiveCompetitor) = 5 := by
  rw [gammaFive_selected_loss, gammaFive_competitor_loss]
  norm_num

def gammaFiveCell : ActiveDecisionCell 5 (Fin 2) where
  q := pointMass6
  selected := gammaFiveSelected
  competitor := gammaFiveCompetitor
  selectedMax := gammaFiveSelectedMax
  selectedMin := gammaFiveSelectedMin
  competitorMax := gammaFiveCompetitorMax
  competitorMin := gammaFiveCompetitorMin
  responseMax := gammaFiveResponseMax
  responseMin := gammaFiveResponseMin

theorem gammaFiveCell_balanced : gammaFiveCell.BalancedComplement := by
  simp [gammaFiveCell, ActiveDecisionCell.BalancedComplement,
    gammaFiveSelected, gammaFiveCompetitor] <;> decide

theorem gammaFiveCell_valid : gammaFiveCell.Valid gammaFiveWorld6 := by
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨by simp [gammaFiveCell, gammaFiveSelected, gammaFiveCompetitor],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    change gammaFiveWorld6 z - gammaFiveSelected.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (z j)) ≤
      gammaFiveWorld6 gammaFiveSelectedMax - gammaFiveSelected.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j
          (gammaFiveSelectedMax j))
    rw [gammaFive_selected_max]
    exact (gammaFive_selected_bounds z).2
  · intro z
    change gammaFiveWorld6 gammaFiveSelectedMin - gammaFiveSelected.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j
          (gammaFiveSelectedMin j)) ≤
      gammaFiveWorld6 z - gammaFiveSelected.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (z j))
    rw [gammaFive_selected_min]
    exact (gammaFive_selected_bounds z).1
  · intro z
    change gammaFiveWorld6 z - gammaFiveCompetitor.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (z j)) ≤
      gammaFiveWorld6 gammaFiveCompetitorMax - gammaFiveCompetitor.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j
          (gammaFiveCompetitorMax j))
    rw [gammaFive_competitor_max]
    exact (gammaFive_competitor_bounds z).2
  · intro z
    change gammaFiveWorld6 gammaFiveCompetitorMin - gammaFiveCompetitor.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j
          (gammaFiveCompetitorMin j)) ≤
      gammaFiveWorld6 z - gammaFiveCompetitor.sum
        (fun j ↦ productResponse pointMass6 gammaFiveWorld6 j (z j))
    rw [gammaFive_competitor_min]
    exact (gammaFive_competitor_bounds z).1
  · intro j u
    fin_cases j <;> fin_cases u <;>
      simp [gammaFiveCell, gammaFiveResponseMax, a6] <;> norm_num
    all_goals norm_num
  · intro j u
    fin_cases j <;> fin_cases u <;>
      simp [gammaFiveCell, gammaFiveResponseMin, a6] <;> norm_num
    all_goals norm_num
  · intro i hi j hj
    have hSpan : ∀ t : Fin 6,
        responseWitnessSpan gammaFiveCell gammaFiveWorld6 t = 1 := by
      intro t
      fin_cases t <;>
        simp [responseWitnessSpan, gammaFiveCell, gammaFiveResponseMax,
          gammaFiveResponseMin, a6] <;> norm_num
      all_goals norm_num
    rw [hSpan j, hSpan i]

theorem gammaFiveCell_gap_mem :
    (5 : ℝ) ∈ admissibleDecisionGaps gammaFiveCell := by
  refine ⟨gammaFiveWorld6, gammaFiveCell_valid,
    gammaFive_mixed_difference_bound, ?_⟩
  simpa [gammaFiveCell] using gammaFive_exact_saturation.symm

/-- Exact finite evidence that the uniform balanced-cell coefficient cannot
be improved below five. -/
theorem gammaFiveCell_no_constant_below_five
    {c : ℝ} (hc : c < 5) :
    ¬ DecisionInteractionConstantAtMost gammaFiveCell c := by
  intro h
  have hbound := h gammaFiveWorld6 gammaFiveCell_valid
    gammaFive_mixed_difference_bound
  rw [show gammaFiveCell.q = pointMass6 by rfl,
      show gammaFiveCell.selected = gammaFiveSelected by rfl,
      show gammaFiveCell.competitor = gammaFiveCompetitor by rfl,
      gammaFive_selected_loss, gammaFive_competitor_loss] at hbound
  norm_num at hbound
  linarith

end CIGAMF.P13.D6Fin6GammaFiveSaturation
