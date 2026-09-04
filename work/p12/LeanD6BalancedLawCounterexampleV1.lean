import Mathlib
import «LeanD6DecisionInteractionComplexityV1»
import «LeanD6PolyhedralActiveCellV1»
import «LeanFunctionalRankingV6»

/-!
# Exact counterexample to the literal universal balanced-cell law

`ActiveDecisionCell` deliberately stores an arbitrary real-valued product
reference `q`; neither the structure nor `BalancedDecisionInteractionBound`
requires its rows to be probability distributions.  The two-coordinate cell
below uses a point mass of row mass two.  Its numerical world is additive, so
every mixed difference is zero, but the unnormalised product response expands
one coordinate by a factor four.  The resulting doubled decision gap is two,
strictly above the proposed coefficient `m - 1 = 1`.

This refutes the literal predicate currently exposed by
`LeanD6DecisionInteractionComplexityV1`.  It does not refute the scientifically
intended law under nonnegative, normalized product weights.
-/

namespace CIGAMF.P13.D6BalancedLawCounterexample

open scoped BigOperators Matrix
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.V6.FunctionalRanking

def a2 (a b : Fin 2) : Fin 2 → Fin 2 := ![a, b]
def z2 : Fin 2 → Fin 2 := a2 0 0
def e20 : Fin 2 → Fin 2 := a2 1 0

/-- A point mass at zero whose individual row mass is two. -/
def scaledPointMass2 (_i : Fin 2) (u : Fin 2) : ℝ :=
  if u = 0 then 2 else 0

/-- An additive one-coordinate world. -/
def additiveWorld2 (x : Fin 2 → Fin 2) : ℝ :=
  if x 0 = 0 then 0 else 1

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem scaledPointMass2_jointWeight (c : Fin 2 → Fin 2) :
    jointWeight scaledPointMass2 c = if c = z2 then 4 else 0 := by
  classical
  by_cases h : c = z2
  · subst c
    rw [show jointWeight scaledPointMass2 z2 =
      scaledPointMass2 0 (z2 0) * scaledPointMass2 1 (z2 1) by
        simp [jointWeight, Fin.prod_univ_two]]
    norm_num [scaledPointMass2, z2, a2]
  · have hc : c 0 ≠ z2 0 ∨ c 1 ≠ z2 1 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;> simp [hn.1, hn.2]
    rcases hc with hc | hc
    · have hc' : c 0 ≠ 0 := by simpa [z2, a2] using hc
      simp [jointWeight, scaledPointMass2, Fin.prod_univ_two, hc', h]
    · have hc' : c 1 ≠ 0 := by simpa [z2, a2] using hc
      simp [jointWeight, scaledPointMass2, Fin.prod_univ_two, hc', h]

theorem scaledPointMass2_expectation (G : (Fin 2 → Fin 2) → ℝ) :
    productExpectation scaledPointMass2 G = 4 * G z2 := by
  classical
  unfold productExpectation
  simp_rw [scaledPointMass2_jointWeight]
  rw [Finset.sum_eq_single z2]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

@[simp] theorem additiveWorld2_response_zero :
    productResponse scaledPointMass2 additiveWorld2 0 0 = 0 := by
  unfold productResponse
  rw [scaledPointMass2_expectation]
  norm_num [additiveWorld2, z2, a2, Function.update]

@[simp] theorem additiveWorld2_response_one :
    productResponse scaledPointMass2 additiveWorld2 0 1 = 4 := by
  unfold productResponse
  rw [scaledPointMass2_expectation]
  norm_num [additiveWorld2, z2, a2, Function.update]

@[simp] theorem additiveWorld2_response_coordinate_one (u : Fin 2) :
    productResponse scaledPointMass2 additiveWorld2 1 u = 0 := by
  unfold productResponse
  rw [scaledPointMass2_expectation]
  fin_cases u <;>
    norm_num [additiveWorld2, z2, a2, Function.update]

def badSelected2 : Finset (Fin 2) := {0}
def badCompetitor2 : Finset (Fin 2) := {1}

def badCell2 : ActiveDecisionCell 1 (Fin 2) where
  q := scaledPointMass2
  selected := badSelected2
  competitor := badCompetitor2
  selectedMax := z2
  selectedMin := e20
  competitorMax := e20
  competitorMin := z2
  responseMax := a2 1 0
  responseMin := z2

theorem badCell2_balanced : badCell2.BalancedComplement := by
  simp [ActiveDecisionCell.BalancedComplement, badCell2,
    badSelected2, badCompetitor2] <;> decide

private theorem additiveWorld2_selected_residual (x : Fin 2 → Fin 2) :
    retainedResidual scaledPointMass2 additiveWorld2 badSelected2 x =
      if x 0 = 0 then 0 else -3 := by
  rcases fin2_zero_or_one (x 0) with hx | hx <;>
    norm_num [retainedResidual, badSelected2, additiveWorld2, hx]

private theorem additiveWorld2_competitor_residual (x : Fin 2 → Fin 2) :
    retainedResidual scaledPointMass2 additiveWorld2 badCompetitor2 x =
      if x 0 = 0 then 0 else 1 := by
  rcases fin2_zero_or_one (x 0) with hx | hx <;>
    simp [retainedResidual, badCompetitor2, additiveWorld2, hx]

theorem badCell2_valid : badCell2.Valid additiveWorld2 := by
  rw [activeDecisionCell_valid_iff_polyhedral]
  refine ⟨by simp [badCell2, badSelected2, badCompetitor2],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [show badCell2.q = scaledPointMass2 by rfl,
      show badCell2.selected = badSelected2 by rfl,
      show badCell2.selectedMax = z2 by rfl,
      additiveWorld2_selected_residual,
      additiveWorld2_selected_residual]
    rcases fin2_zero_or_one (x 0) with hx | hx <;>
      simp [hx, z2, a2]
  · intro x
    rw [show badCell2.q = scaledPointMass2 by rfl,
      show badCell2.selected = badSelected2 by rfl,
      show badCell2.selectedMin = e20 by rfl,
      additiveWorld2_selected_residual,
      additiveWorld2_selected_residual]
    rcases fin2_zero_or_one (x 0) with hx | hx <;>
      simp [hx, e20, a2]
  · intro x
    rw [show badCell2.q = scaledPointMass2 by rfl,
      show badCell2.competitor = badCompetitor2 by rfl,
      show badCell2.competitorMax = e20 by rfl,
      additiveWorld2_competitor_residual,
      additiveWorld2_competitor_residual]
    rcases fin2_zero_or_one (x 0) with hx | hx <;>
      simp [hx, e20, a2]
  · intro x
    rw [show badCell2.q = scaledPointMass2 by rfl,
      show badCell2.competitor = badCompetitor2 by rfl,
      show badCell2.competitorMin = z2 by rfl,
      additiveWorld2_competitor_residual,
      additiveWorld2_competitor_residual]
    rcases fin2_zero_or_one (x 0) with hx | hx <;>
      simp [hx, z2, a2]
  · intro j u
    fin_cases j <;> fin_cases u <;>
      norm_num [badCell2, a2, z2]
  · intro j u
    fin_cases j <;> fin_cases u <;>
      norm_num [badCell2, a2, z2]
  · intro i hi j hj
    fin_cases i <;> fin_cases j <;>
      simp_all [badCell2, badSelected2, responseWitnessSpan, a2, z2] <;>
      norm_num

theorem additiveWorld2_unitInteraction : UnitInteractionBound additiveWorld2 := by
  intro i x c
  fin_cases i <;>
    rcases fin2_zero_or_one (x 0) with hx0 | hx0 <;>
    rcases fin2_zero_or_one (x 1) with hx1 | hx1 <;>
    rcases fin2_zero_or_one (c 0) with hc0 | hc0 <;>
    rcases fin2_zero_or_one (c 1) with hc1 | hc1 <;>
    simp [mixedDifference, additiveWorld2, hx0, hx1, hc0, hc1,
      Function.update]

private theorem compressionLoss_eq_of_bounds
    (S : Finset (Fin 2)) (lo hi : ℝ)
    (hbound : ∀ x, lo ≤ additiveWorld2 x -
        S.sum (fun j ↦ productResponse scaledPointMass2 additiveWorld2 j (x j)) ∧
      additiveWorld2 x -
        S.sum (fun j ↦ productResponse scaledPointMass2 additiveWorld2 j (x j)) ≤ hi)
    (xmin xmax : Fin 2 → Fin 2)
    (hmin : additiveWorld2 xmin -
        S.sum (fun j ↦ productResponse scaledPointMass2 additiveWorld2 j (xmin j)) = lo)
    (hmax : additiveWorld2 xmax -
        S.sum (fun j ↦ productResponse scaledPointMass2 additiveWorld2 j (xmax j)) = hi) :
    productCompressionLoss additiveWorld2
      (productResponse scaledPointMass2 additiveWorld2) S = (hi - lo) / 2 := by
  let r : (Fin 2 → Fin 2) → ℝ := fun x ↦ additiveWorld2 x -
    S.sum (fun j ↦ productResponse scaledPointMass2 additiveWorld2 j (x j))
  have hrmax : maxVal r = hi := by
    apply le_antisymm
    · exact maxVal_le r (fun x ↦ (hbound x).2)
    · simpa [r, hmax] using le_maxVal r xmax
  have hrmin : minVal r = lo := by
    apply le_antisymm
    · simpa [r, hmin] using minVal_le r xmin
    · exact le_minVal r (fun x ↦ (hbound x).1)
  simp [productCompressionLoss, r, osc, hrmax, hrmin]

theorem badSelected2_loss :
    productCompressionLoss additiveWorld2
      (productResponse scaledPointMass2 additiveWorld2) badSelected2 = 3 / 2 := by
  have h : productCompressionLoss additiveWorld2
      (productResponse scaledPointMass2 additiveWorld2) badSelected2 =
      (0 - (-3 : ℝ)) / 2 := by
    refine compressionLoss_eq_of_bounds badSelected2 (-3) 0 ?_ e20 z2 ?_ ?_
    · intro x
      change -3 ≤ retainedResidual scaledPointMass2 additiveWorld2
          badSelected2 x ∧
        retainedResidual scaledPointMass2 additiveWorld2 badSelected2 x ≤ 0
      rw [additiveWorld2_selected_residual]
      rcases fin2_zero_or_one (x 0) with hx | hx <;>
        simp [hx]
    · norm_num [badSelected2, additiveWorld2, e20, a2]
    · simp [badSelected2, additiveWorld2, z2, a2]
  norm_num at h ⊢
  exact h

theorem badCompetitor2_loss :
    productCompressionLoss additiveWorld2
      (productResponse scaledPointMass2 additiveWorld2) badCompetitor2 = 1 / 2 := by
  have h : productCompressionLoss additiveWorld2
      (productResponse scaledPointMass2 additiveWorld2) badCompetitor2 =
      ((1 : ℝ) - 0) / 2 := by
    refine compressionLoss_eq_of_bounds badCompetitor2 0 1 ?_ z2 e20 ?_ ?_
    · intro x
      change 0 ≤ retainedResidual scaledPointMass2 additiveWorld2
          badCompetitor2 x ∧
        retainedResidual scaledPointMass2 additiveWorld2 badCompetitor2 x ≤ 1
      rw [additiveWorld2_competitor_residual]
      rcases fin2_zero_or_one (x 0) with hx | hx <;>
        simp [hx]
    · simp [badCompetitor2, additiveWorld2, z2, a2]
    · simp [badCompetitor2, additiveWorld2, e20, a2]
  norm_num at h ⊢
  exact h

theorem badCell2_exact_gap :
    2 * (productCompressionLoss additiveWorld2
        (productResponse badCell2.q additiveWorld2) badCell2.selected -
      productCompressionLoss additiveWorld2
        (productResponse badCell2.q additiveWorld2) badCell2.competitor) = 2 := by
  change 2 * (productCompressionLoss additiveWorld2
        (productResponse scaledPointMass2 additiveWorld2) badSelected2 -
      productCompressionLoss additiveWorld2
        (productResponse scaledPointMass2 additiveWorld2) badCompetitor2) = 2
  rw [badSelected2_loss, badCompetitor2_loss]
  norm_num

/-- The proposed `m - 1` coefficient already fails at `m = 2`. -/
theorem badCell2_not_atMost_one :
    ¬ DecisionInteractionConstantAtMost badCell2 1 := by
  intro h
  have hbad := h additiveWorld2 badCell2_valid additiveWorld2_unitInteraction
  rw [badCell2_exact_gap] at hbad
  norm_num at hbad

/-- A universe-robust existential falsification of the body of the literal
un-normalised universal predicate.  (The nested `Type*` binder in the legacy
abbreviation `BalancedDecisionInteractionBound` fixes an inaccessible
universe, so this theorem states its scientific content directly.) -/
theorem exists_balanced_cell_violating_m_minus_one :
    ∃ (cell : ActiveDecisionCell 1 (Fin 2)),
      cell.BalancedComplement ∧ ¬ DecisionInteractionConstantAtMost cell 1 := by
  exact ⟨badCell2, badCell2_balanced, badCell2_not_atMost_one⟩

/-- The universe-zero instance of the legacy predicate is therefore false.
The universe annotation is intentional: the legacy definition quantifies its
action type at one fixed universe level. -/
theorem balancedDecisionInteractionBound_type0_false :
    ¬ BalancedDecisionInteractionBound.{0} := by
  intro h
  have hc : DecisionInteractionConstantAtMost badCell2 (1 : ℝ) := by
    simpa using h 1 (Fin 2) badCell2 badCell2_balanced
  exact badCell2_not_atMost_one hc

/-- The counterexample pinpoints normalization: its joint mass is four. -/
theorem scaledPointMass2_not_normalized :
    ∑ c, jointWeight scaledPointMass2 c = 4 := by
  classical
  simp_rw [scaledPointMass2_jointWeight]
  rw [Finset.sum_eq_single z2]
  · simp
  · intro c hc hne
    simp [hne]
  · simp

end CIGAMF.P13.D6BalancedLawCounterexample
