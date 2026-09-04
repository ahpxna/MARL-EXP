import Mathlib
import «LeanD6DecisionInteractionComplexityV1»
import «LeanD6PolyhedralActiveCellV1»
import «LeanD6NormalizedBalancedTargetV1»

/-!
# Exact normalized ternary counterexample to the non-strict balanced D6 law

This file is intentionally separate from the frozen P12 corpus and from the
legacy unnormalised two-coordinate counterexample.  It records an exact
integer-valued `Fin 4 → Fin 3` world with a normalized point-mass product
reference.  All response spans tie, which is permitted by the current
non-strict `IsTopKByScore` semantics.  The file must compile before this
candidate is used to falsify the current universal normalized statement.
-/

namespace CIGAMF.P13.D6NormalizedBalancedTernaryCounterexample

set_option maxHeartbeats 12000000

open scoped BigOperators Matrix
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6NormalizedBalancedTarget

def a4t (a b c d : Fin 3) : Fin 4 → Fin 3 := ![a, b, c, d]
def z4t : Fin 4 → Fin 3 := a4t 0 0 0 0

@[simp] theorem a4t_apply_zero (a b c d : Fin 3) : a4t a b c d 0 = a := by rfl
@[simp] theorem a4t_apply_one (a b c d : Fin 3) : a4t a b c d 1 = b := by rfl
@[simp] theorem a4t_apply_two (a b c d : Fin 3) : a4t a b c d 2 = c := by rfl
@[simp] theorem a4t_apply_three (a b c d : Fin 3) : a4t a b c d 3 = d := by rfl

def pointMassTernary4 (_i : Fin 4) (u : Fin 3) : ℝ :=
  if u = 0 then 1 else 0

/-- A concrete normal form for changing one coordinate of the point-mass
anchor.  Keeping it separate avoids unfolding `Function.update` inside every
finite table calculation. -/
def ternaryInsertAtZero4 (i : Fin 4) (u : Fin 3) : Fin 4 → Fin 3 :=
  match i with
  | ⟨0, _⟩ => a4t u 0 0 0
  | ⟨1, _⟩ => a4t 0 u 0 0
  | ⟨2, _⟩ => a4t 0 0 u 0
  | ⟨3, _⟩ => a4t 0 0 0 u

private theorem update_z4t_normal_form (i : Fin 4) (u : Fin 3) :
    Function.update z4t i u = ternaryInsertAtZero4 i u := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [z4t, a4t, ternaryInsertAtZero4, Function.update, Fin.mk.injEq]

/-- The exact 81-cell integer LP witness, explicitly branched so that finite
case proofs reduce without relying on opaque list-index normalization. -/
def ternaryBalancedWorld4 (x : Fin 4 → Fin 3) : ℝ :=
  if x 0 = 0 then
    if x 1 = 0 then
      if x 2 = 0 then
        if x 3 = 0 then (-2 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-2 : ℝ)
      else if x 2 = 1 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
    else if x 1 = 1 then
      if x 2 = 0 then
        if x 3 = 0 then (-2 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else if x 2 = 1 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
    else
      if x 2 = 0 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-2 : ℝ) else 0
      else if x 2 = 1 then
        if x 3 = 0 then 0 else if x 3 = 1 then (-2 : ℝ) else 0
      else
        if x 3 = 0 then 0 else if x 3 = 1 then (-1 : ℝ) else 0
  else if x 0 = 1 then
    if x 1 = 0 then
      if x 2 = 0 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else if x 2 = 1 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-2 : ℝ) else (-1 : ℝ)
    else if x 1 = 1 then
      if x 2 = 0 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else if x 2 = 1 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-2 : ℝ) else (-1 : ℝ)
      else
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-2 : ℝ) else (-1 : ℝ)
    else
      if x 2 = 0 then
        if x 3 = 0 then 0 else if x 3 = 1 then (-2 : ℝ) else 0
      else if x 2 = 1 then
        if x 3 = 0 then 0 else if x 3 = 1 then (-1 : ℝ) else 0
      else
        if x 3 = 0 then 0 else if x 3 = 1 then (-1 : ℝ) else 0
  else
    if x 1 = 0 then
      if x 2 = 0 then
        if x 3 = 0 then (-2 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-2 : ℝ)
      else if x 2 = 1 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-2 : ℝ) else (-1 : ℝ)
    else if x 1 = 1 then
      if x 2 = 0 then
        if x 3 = 0 then (-2 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else if x 2 = 1 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-3 : ℝ) else (-1 : ℝ)
      else
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-2 : ℝ) else (-1 : ℝ)
    else
      if x 2 = 0 then
        if x 3 = 0 then (-1 : ℝ) else if x 3 = 1 then (-2 : ℝ) else 0
      else if x 2 = 1 then
        if x 3 = 0 then 0 else if x 3 = 1 then (-1 : ℝ) else 0
      else
        if x 3 = 0 then 0 else if x 3 = 1 then (-1 : ℝ) else 0

def ternarySelected4 : Finset (Fin 4) := {0, 2}
def ternaryCompetitor4 : Finset (Fin 4) := {1, 3}

def ternarySelectedMax4 : Fin 4 → Fin 3 := a4t 0 2 0 2
def ternarySelectedMin4 : Fin 4 → Fin 3 := a4t 1 0 1 1
def ternaryCompetitorMax4 : Fin 4 → Fin 3 := a4t 0 1 2 2
def ternaryCompetitorMin4 : Fin 4 → Fin 3 := a4t 0 2 0 0
def ternaryResponseMax4 : Fin 4 → Fin 3 := a4t 1 2 1 0
def ternaryResponseMin4 : Fin 4 → Fin 3 := a4t 0 1 0 1

/- Named selector lookups are intentionally kept separate from the 81-cell
world evaluator.  They prevent `simp` from unfolding vector literals beneath
finite sums, which otherwise leaves proof-term equalities on `Fin`. -/
@[simp] theorem ternarySelectedMax4_0 : ternarySelectedMax4 0 = 0 := by rfl
@[simp] theorem ternarySelectedMax4_1 : ternarySelectedMax4 1 = 2 := by rfl
@[simp] theorem ternarySelectedMax4_2 : ternarySelectedMax4 2 = 0 := by rfl
@[simp] theorem ternarySelectedMax4_3 : ternarySelectedMax4 3 = 2 := by rfl
@[simp] theorem ternarySelectedMin4_0 : ternarySelectedMin4 0 = 1 := by rfl
@[simp] theorem ternarySelectedMin4_1 : ternarySelectedMin4 1 = 0 := by rfl
@[simp] theorem ternarySelectedMin4_2 : ternarySelectedMin4 2 = 1 := by rfl
@[simp] theorem ternarySelectedMin4_3 : ternarySelectedMin4 3 = 1 := by rfl
@[simp] theorem ternaryCompetitorMax4_0 : ternaryCompetitorMax4 0 = 0 := by rfl
@[simp] theorem ternaryCompetitorMax4_1 : ternaryCompetitorMax4 1 = 1 := by rfl
@[simp] theorem ternaryCompetitorMax4_2 : ternaryCompetitorMax4 2 = 2 := by rfl
@[simp] theorem ternaryCompetitorMax4_3 : ternaryCompetitorMax4 3 = 2 := by rfl
@[simp] theorem ternaryCompetitorMin4_0 : ternaryCompetitorMin4 0 = 0 := by rfl
@[simp] theorem ternaryCompetitorMin4_1 : ternaryCompetitorMin4 1 = 2 := by rfl
@[simp] theorem ternaryCompetitorMin4_2 : ternaryCompetitorMin4 2 = 0 := by rfl
@[simp] theorem ternaryCompetitorMin4_3 : ternaryCompetitorMin4 3 = 0 := by rfl
@[simp] theorem ternaryResponseMax4_0 : ternaryResponseMax4 0 = 1 := by rfl
@[simp] theorem ternaryResponseMax4_1 : ternaryResponseMax4 1 = 2 := by rfl
@[simp] theorem ternaryResponseMax4_2 : ternaryResponseMax4 2 = 1 := by rfl
@[simp] theorem ternaryResponseMax4_3 : ternaryResponseMax4 3 = 0 := by rfl
@[simp] theorem ternaryResponseMin4_0 : ternaryResponseMin4 0 = 0 := by rfl
@[simp] theorem ternaryResponseMin4_1 : ternaryResponseMin4 1 = 1 := by rfl
@[simp] theorem ternaryResponseMin4_2 : ternaryResponseMin4 2 = 0 := by rfl
@[simp] theorem ternaryResponseMin4_3 : ternaryResponseMin4 3 = 1 := by rfl

def ternaryBalancedCell4 : ActiveDecisionCell 3 (Fin 3) where
  q := pointMassTernary4
  selected := ternarySelected4
  competitor := ternaryCompetitor4
  selectedMax := ternarySelectedMax4
  selectedMin := ternarySelectedMin4
  competitorMax := ternaryCompetitorMax4
  competitorMin := ternaryCompetitorMin4
  responseMax := ternaryResponseMax4
  responseMin := ternaryResponseMin4

@[simp] theorem ternaryBalancedWorld4_z4t : ternaryBalancedWorld4 z4t = -2 := by
  norm_num [ternaryBalancedWorld4, z4t]

private theorem fin3_cases (u : Fin 3) : u = 0 ∨ u = 1 ∨ u = 2 := by
  fin_cases u <;> simp

private theorem ternarySelected4_sum (g : Fin 4 → ℝ) :
    ternarySelected4.sum g = g 0 + g 2 := by
  simp [ternarySelected4, add_comm]

private theorem ternaryCompetitor4_sum (g : Fin 4 → ℝ) :
    ternaryCompetitor4.sum g = g 1 + g 3 := by
  simp [ternaryCompetitor4, add_comm]

theorem pointMassTernary4_jointWeight (c : Fin 4 → Fin 3) :
    jointWeight pointMassTernary4 c = if c = z4t then 1 else 0 := by
  classical
  by_cases h : c = z4t
  · subst c
    simp [jointWeight, pointMassTernary4, z4t,
      Fin.prod_univ_four]
  · have hcoord : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 ∨ c 3 ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;> simp [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, z4t]
    rcases hcoord with h0 | h1 | h2 | h3
    · simp [jointWeight, pointMassTernary4, Fin.prod_univ_four, h0, h]
    · simp [jointWeight, pointMassTernary4, Fin.prod_univ_four, h1, h]
    · simp [jointWeight, pointMassTernary4, Fin.prod_univ_four, h2, h]
    · simp [jointWeight, pointMassTernary4, Fin.prod_univ_four, h3, h]

theorem pointMassTernary4_hWeight :
    ∀ c, 0 ≤ jointWeight pointMassTernary4 c := by
  intro c
  rw [pointMassTernary4_jointWeight]
  split <;> norm_num

theorem pointMassTernary4_hNorm :
    ∑ c, jointWeight pointMassTernary4 c = 1 := by
  classical
  simp_rw [pointMassTernary4_jointWeight]
  rw [Finset.sum_eq_single z4t]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

theorem pointMassTernary4_expectation (G : (Fin 4 → Fin 3) → ℝ) :
    productExpectation pointMassTernary4 G = G z4t := by
  classical
  unfold productExpectation
  simp_rw [pointMassTernary4_jointWeight]
  rw [Finset.sum_eq_single z4t]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

theorem pointMassTernary4_response (F : (Fin 4 → Fin 3) → ℝ)
    (i : Fin 4) (u : Fin 3) :
    productResponse pointMassTernary4 F i u =
      F (Function.update z4t i u) := by
  unfold productResponse
  rw [pointMassTernary4_expectation]

def ternaryResponseTable4 (i : Fin 4) (u : Fin 3) : ℝ :=
  match i with
  | ⟨0, _⟩ =>
      if u = 0 then (-2 : ℝ) else if u = 1 then (-1 : ℝ) else (-2 : ℝ)
  | ⟨1, _⟩ =>
      if u = 0 then (-2 : ℝ) else if u = 1 then (-2 : ℝ) else (-1 : ℝ)
  | ⟨2, _⟩ =>
      if u = 0 then (-2 : ℝ) else if u = 1 then (-1 : ℝ) else (-1 : ℝ)
  | ⟨3, _⟩ =>
      if u = 0 then (-2 : ℝ) else if u = 1 then (-3 : ℝ) else (-2 : ℝ)

private theorem ternaryBalancedWorld4_insertAtZero (i : Fin 4) (u : Fin 3) :
    ternaryBalancedWorld4 (ternaryInsertAtZero4 i u) =
      ternaryResponseTable4 i u := by
  fin_cases i <;> fin_cases u <;>
    simp only [ternaryInsertAtZero4, a4t_apply_zero, a4t_apply_one,
      a4t_apply_two, a4t_apply_three] <;>
    norm_num [ternaryBalancedWorld4, ternaryResponseTable4]

@[simp] theorem ternaryBalanced_response_table (i : Fin 4) (u : Fin 3) :
    productResponse pointMassTernary4 ternaryBalancedWorld4 i u =
      ternaryResponseTable4 i u := by
  rw [pointMassTernary4_response, update_z4t_normal_form,
    ternaryBalancedWorld4_insertAtZero]

private def ternaryPairIndex (a b : Fin 3) : Fin 9 :=
  ⟨a.val * 3 + b.val, by omega⟩

private noncomputable def ternaryContrast
    (i : Fin 4) (a b : Fin 3) (x : Fin 4 → Fin 3) : ℝ :=
  ternaryBalancedWorld4 (Function.update x i a) -
    ternaryBalancedWorld4 (Function.update x i b)

/-- Exact lower coordinate-contrast table for the 81-cell witness. -/
private def ternaryContrastLo (i : Fin 4) (a b : Fin 3) : ℝ :=
  (![ (![ (0 : ℝ), -1, -1, 0, 0, 0, 0, -1, 0] : Fin 9 → ℝ),
      ![ (0 : ℝ), -1, -2, 0, 0, -2, 1, 1, 0],
      ![ (0 : ℝ), -1, -1, 0, 0, -1, 0, 0, 0],
      ![ (0 : ℝ), 1, -1, -2, 0, -2, 0, 1, 0]] :
      Fin 4 → Fin 9 → ℝ) i (ternaryPairIndex a b)

/-- Exact upper coordinate-contrast table for the 81-cell witness. -/
private def ternaryContrastHi (i : Fin 4) (a b : Fin 3) : ℝ :=
  (![ (![ (0 : ℝ), 0, 0, 1, 0, 1, 1, 0, 0] : Fin 9 → ℝ),
      ![ (0 : ℝ), 0, -1, 1, 0, -1, 2, 2, 0],
      ![ (0 : ℝ), 0, 0, 1, 0, 0, 1, 1, 0],
      ![ (0 : ℝ), 2, 0, -1, 0, -1, 1, 2, 0]] :
      Fin 4 → Fin 9 → ℝ) i (ternaryPairIndex a b)

private theorem ternaryContrast_bounds
    (i : Fin 4) (a b : Fin 3) (x : Fin 4 → Fin 3) :
    ternaryContrastLo i a b ≤ ternaryContrast i a b x ∧
      ternaryContrast i a b x ≤ ternaryContrastHi i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    simp [ternaryContrast, ternaryContrastLo, ternaryContrastHi,
      ternaryPairIndex, ternaryBalancedWorld4,
      h0, h1, h2, h3, Function.update] <;> norm_num

private theorem ternaryContrast_width
    (i : Fin 4) (a b : Fin 3) :
    ternaryContrastHi i a b - ternaryContrastLo i a b ≤ 1 := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [ternaryContrastLo, ternaryContrastHi, ternaryPairIndex]

private theorem mixed_eq_ternaryContrast_diff
    (i : Fin 4) (x c : Fin 4 → Fin 3) :
    mixedDifference ternaryBalancedWorld4 i x c =
      ternaryContrast i (x i) (c i) x -
        ternaryContrast i (x i) (c i) c := by
  unfold mixedDifference ternaryContrast
  have hxx : Function.update x i (x i) = x := by
    exact Function.update_eq_self_iff.mpr rfl
  have hcc : Function.update c i (c i) = c := by
    exact Function.update_eq_self_iff.mpr rfl
  rw [hxx, hcc]
  ring

theorem ternaryBalanced_unitInteraction :
    UnitInteractionBound ternaryBalancedWorld4 := by
  intro i x c
  rw [mixed_eq_ternaryContrast_diff]
  rw [abs_le]
  have hx := ternaryContrast_bounds i (x i) (c i) x
  have hc := ternaryContrast_bounds i (x i) (c i) c
  have hw := ternaryContrast_width i (x i) (c i)
  constructor <;> linarith

private theorem compressionLoss_eq_of_bounds
    (S : Finset (Fin 4)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ ternaryBalancedWorld4 x -
        S.sum (fun j ↦ productResponse pointMassTernary4
          ternaryBalancedWorld4 j (x j)) ∧
      ternaryBalancedWorld4 x -
        S.sum (fun j ↦ productResponse pointMassTernary4
          ternaryBalancedWorld4 j (x j)) ≤ hi)
    (xmin xmax : Fin 4 → Fin 3)
    (hmin : ternaryBalancedWorld4 xmin -
        S.sum (fun j ↦ productResponse pointMassTernary4
          ternaryBalancedWorld4 j (xmin j)) = lo)
    (hmax : ternaryBalancedWorld4 xmax -
        S.sum (fun j ↦ productResponse pointMassTernary4
          ternaryBalancedWorld4 j (xmax j)) = hi) :
    productCompressionLoss ternaryBalancedWorld4
      (productResponse pointMassTernary4 ternaryBalancedWorld4) S =
        (hi - lo) / 2 := by
  let r : (Fin 4 → Fin 3) → ℝ := fun x ↦ ternaryBalancedWorld4 x -
    S.sum (fun j ↦ productResponse pointMassTernary4
      ternaryBalancedWorld4 j (x j))
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

private theorem ternarySelected_bounds (x : Fin 4 → Fin 3) :
    (-1 : ℝ) ≤ ternaryBalancedWorld4 x - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (x j)) ∧
    ternaryBalancedWorld4 x - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (x j)) ≤ 4 := by
  simp only [ternaryBalanced_response_table]
  rw [ternarySelected4_sum]
  rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    simp [ternaryBalancedWorld4, ternaryResponseTable4,
      h0, h1, h2, h3] <;> norm_num

private theorem ternaryCompetitor_bounds (x : Fin 4 → Fin 3) :
    (2 : ℝ) ≤ ternaryBalancedWorld4 x - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (x j)) ∧
    ternaryBalancedWorld4 x - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (x j)) ≤ 3 := by
  simp only [ternaryBalanced_response_table]
  rw [ternaryCompetitor4_sum]
  rcases fin3_cases (x 0) with h0 | h0 | h0 <;>
    rcases fin3_cases (x 1) with h1 | h1 | h1 <;>
    rcases fin3_cases (x 2) with h2 | h2 | h2 <;>
    rcases fin3_cases (x 3) with h3 | h3 | h3 <;>
    simp [ternaryBalancedWorld4, ternaryResponseTable4,
      h0, h1, h2, h3] <;> norm_num

private theorem ternarySelected_min_eval :
    ternaryBalancedWorld4 ternarySelectedMin4 - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
        (ternarySelectedMin4 j)) = -1 := by
  simp only [ternaryBalanced_response_table]
  rw [ternarySelected4_sum]
  norm_num [ternaryBalancedWorld4, ternaryResponseTable4]

private theorem ternarySelected_max_eval :
    ternaryBalancedWorld4 ternarySelectedMax4 - ternarySelected4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
        (ternarySelectedMax4 j)) = 4 := by
  simp only [ternaryBalanced_response_table]
  rw [ternarySelected4_sum]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [ternaryBalancedWorld4, ternaryResponseTable4, h20, h21]

private theorem ternaryCompetitor_min_eval :
    ternaryBalancedWorld4 ternaryCompetitorMin4 - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
        (ternaryCompetitorMin4 j)) = 2 := by
  simp only [ternaryBalanced_response_table]
  rw [ternaryCompetitor4_sum]
  norm_num [ternaryBalancedWorld4, ternaryResponseTable4]

private theorem ternaryCompetitor_max_eval :
    ternaryBalancedWorld4 ternaryCompetitorMax4 - ternaryCompetitor4.sum
      (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
        (ternaryCompetitorMax4 j)) = 3 := by
  simp only [ternaryBalanced_response_table]
  rw [ternaryCompetitor4_sum]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [ternaryBalancedWorld4, ternaryResponseTable4, h20, h21]

theorem ternarySelected_loss :
    productCompressionLoss ternaryBalancedWorld4
      (productResponse pointMassTernary4 ternaryBalancedWorld4)
      ternarySelected4 = 5 / 2 := by
  convert compressionLoss_eq_of_bounds ternarySelected4 (-1) 4
    ternarySelected_bounds ternarySelectedMin4 ternarySelectedMax4
    ternarySelected_min_eval ternarySelected_max_eval using 1 <;> norm_num

theorem ternaryCompetitor_loss :
    productCompressionLoss ternaryBalancedWorld4
      (productResponse pointMassTernary4 ternaryBalancedWorld4)
      ternaryCompetitor4 = 1 / 2 := by
  convert compressionLoss_eq_of_bounds ternaryCompetitor4 2 3
    ternaryCompetitor_bounds ternaryCompetitorMin4 ternaryCompetitorMax4
    ternaryCompetitor_min_eval ternaryCompetitor_max_eval using 1 <;> norm_num

theorem ternaryBalancedCell4_balanced : ternaryBalancedCell4.BalancedComplement := by
  simp [ternaryBalancedCell4, ActiveDecisionCell.BalancedComplement,
    ternarySelected4, ternaryCompetitor4] <;> decide

private theorem ternaryResponseWitnessSpan_one (t : Fin 4) :
    responseWitnessSpan ternaryBalancedCell4 ternaryBalancedWorld4 t = 1 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases t <;>
    norm_num [responseWitnessSpan, ternaryBalancedCell4,
      ternaryResponseMax4, ternaryResponseMin4, a4t,
      ternaryResponseTable4, Fin.mk.injEq, h20, h21]

theorem ternaryBalancedCell4_valid :
    ternaryBalancedCell4.Valid ternaryBalancedWorld4 := by
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨by simp [ternaryBalancedCell4, ternarySelected4, ternaryCompetitor4],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    change ternaryBalancedWorld4 z - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (z j)) ≤
      ternaryBalancedWorld4 ternarySelectedMax4 - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
          (ternarySelectedMax4 j))
    rw [ternarySelected_max_eval]
    exact (ternarySelected_bounds z).2
  · intro z
    change ternaryBalancedWorld4 ternarySelectedMin4 - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
          (ternarySelectedMin4 j)) ≤
      ternaryBalancedWorld4 z - ternarySelected4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (z j))
    rw [ternarySelected_min_eval]
    exact (ternarySelected_bounds z).1
  · intro z
    change ternaryBalancedWorld4 z - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (z j)) ≤
      ternaryBalancedWorld4 ternaryCompetitorMax4 - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
          (ternaryCompetitorMax4 j))
    rw [ternaryCompetitor_max_eval]
    exact (ternaryCompetitor_bounds z).2
  · intro z
    change ternaryBalancedWorld4 ternaryCompetitorMin4 - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j
          (ternaryCompetitorMin4 j)) ≤
      ternaryBalancedWorld4 z - ternaryCompetitor4.sum
        (fun j ↦ productResponse pointMassTernary4 ternaryBalancedWorld4 j (z j))
    rw [ternaryCompetitor_min_eval]
    exact (ternaryCompetitor_bounds z).1
  · intro j u
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    fin_cases j <;> fin_cases u <;>
      norm_num [ternaryBalancedCell4, ternaryResponseMax4, a4t,
        ternaryResponseTable4, Fin.mk.injEq, h20, h21]
  · intro j u
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    fin_cases j <;> fin_cases u <;>
      norm_num [ternaryBalancedCell4, ternaryResponseMin4, a4t,
        ternaryResponseTable4, Fin.mk.injEq, h20, h21]
  · intro i hi j hj
    rw [ternaryResponseWitnessSpan_one j,
      ternaryResponseWitnessSpan_one i]

theorem ternaryBalanced_exact_gap :
    2 * (productCompressionLoss ternaryBalancedWorld4
        (productResponse pointMassTernary4 ternaryBalancedWorld4) ternarySelected4 -
      productCompressionLoss ternaryBalancedWorld4
        (productResponse pointMassTernary4 ternaryBalancedWorld4) ternaryCompetitor4) = 4 := by
  rw [ternarySelected_loss, ternaryCompetitor_loss]
  norm_num

/-- Exact refutation of the current normalized, non-strict balanced `m - 1`
law.  It is not a statement about a future strict-margin restriction. -/
theorem ternaryBalancedCell4_not_atMost_three :
    ¬ DecisionInteractionConstantAtMost ternaryBalancedCell4 3 := by
  intro h
  have hbad := h ternaryBalancedWorld4 ternaryBalancedCell4_valid
    ternaryBalanced_unitInteraction
  change 2 * (productCompressionLoss ternaryBalancedWorld4
      (productResponse pointMassTernary4 ternaryBalancedWorld4) ternarySelected4 -
    productCompressionLoss ternaryBalancedWorld4
      (productResponse pointMassTernary4 ternaryBalancedWorld4) ternaryCompetitor4) ≤ 3 at hbad
  rw [ternaryBalanced_exact_gap] at hbad
  norm_num at hbad

theorem exists_normalized_balanced_cell_violating_m_minus_one :
    ∃ (cell : ActiveDecisionCell 3 (Fin 3)),
      (∀ c, 0 ≤ jointWeight cell.q c) ∧
      (∑ c, jointWeight cell.q c = 1) ∧
      cell.BalancedComplement ∧ ¬ DecisionInteractionConstantAtMost cell 3 := by
  exact ⟨ternaryBalancedCell4, pointMassTernary4_hWeight,
    pointMassTernary4_hNorm, ternaryBalancedCell4_balanced,
    ternaryBalancedCell4_not_atMost_three⟩

/-- The current universe-zero normalized balanced law is false. -/
theorem normalizedBalancedDecisionInteractionBound_type0_false :
    ¬ NormalizedBalancedDecisionInteractionBound.{0} := by
  intro h
  have hc : DecisionInteractionConstantAtMost ternaryBalancedCell4 (3 : ℝ) := by
    simpa using h 3 (Fin 3) ternaryBalancedCell4
      pointMassTernary4_hWeight pointMassTernary4_hNorm
      ternaryBalancedCell4_balanced
  exact ternaryBalancedCell4_not_atMost_three hc

end CIGAMF.P13.D6NormalizedBalancedTernaryCounterexample
