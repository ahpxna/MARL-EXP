import Mathlib
import «LeanD6ActiveDecisionCellV1»

/-!
# Explicit polyhedral active cells for D6

`ActiveDecisionCell.Valid` is convenient scientific notation, but it mentions
finite maxima, minima, oscillations, and a Top-K optimizer.  This file expands
those selectors into a finite family of linear inequalities after all active
witnesses have been fixed by the cell.
-/

namespace CIGAMF.P13.D6PolyhedralActiveCell

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def responseWitnessSpan {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) (j : Fin (n + 1)) : ℝ :=
  productResponse cell.q F j (cell.responseMax j) -
    productResponse cell.q F j (cell.responseMin j)

/-- A literal finite system of linear inequalities in `F`.  No finite
`maxVal`, `minVal`, `osc`, or optimization predicate occurs here. -/
def PolyhedralCellValid {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  cell.selected.card = cell.competitor.card ∧
  (∀ z, retainedResidual cell.q F cell.selected z ≤
    retainedResidual cell.q F cell.selected cell.selectedMax) ∧
  (∀ z, retainedResidual cell.q F cell.selected cell.selectedMin ≤
    retainedResidual cell.q F cell.selected z) ∧
  (∀ z, retainedResidual cell.q F cell.competitor z ≤
    retainedResidual cell.q F cell.competitor cell.competitorMax) ∧
  (∀ z, retainedResidual cell.q F cell.competitor cell.competitorMin ≤
    retainedResidual cell.q F cell.competitor z) ∧
  (∀ j u, productResponse cell.q F j u ≤
    productResponse cell.q F j (cell.responseMax j)) ∧
  (∀ j u, productResponse cell.q F j (cell.responseMin j) ≤
    productResponse cell.q F j u) ∧
  ∀ i ∈ cell.selected, ∀ j ∉ cell.selected,
    responseWitnessSpan cell F j ≤ responseWitnessSpan cell F i

private theorem max_eq_of_witness_ge {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (x : X) (h : ∀ z, f z ≤ f x) :
    maxVal f = f x := by
  exact le_antisymm (maxVal_le f h) (le_maxVal f x)

private theorem min_eq_of_witness_le {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (x : X) (h : ∀ z, f x ≤ f z) :
    minVal f = f x := by
  exact le_antisymm (minVal_le f x) (le_minVal f h)

private theorem sum_le_sum_of_disjoint_pairwise
    {I : Type*} [DecidableEq I] (score : I → ℝ)
    (A B : Finset I) (hCard : A.card = B.card)
    (hPair : ∀ a ∈ A, ∀ b ∈ B, score a ≤ score b) :
    A.sum score ≤ B.sum score := by
  classical
  induction A using Finset.induction_on generalizing B with
  | empty =>
      have hB : B = ∅ := Finset.card_eq_zero.mp (by simpa using hCard.symm)
      simp [hB]
  | @insert a A ha ih =>
      have hBpos : 0 < B.card := by
        rw [← hCard]
        simp [ha]
      rcases Finset.card_pos.mp hBpos with ⟨b, hb⟩
      have hCard' : A.card = (B.erase b).card := by
        simp [ha, hb] at hCard ⊢
        omega
      have hPair' : ∀ x ∈ A, ∀ y ∈ B.erase b, score x ≤ score y := by
        intro x hx y hy
        exact hPair x (by simp [hx]) y (Finset.mem_of_mem_erase hy)
      have hInd := ih (B.erase b) hCard' hPair'
      have hab : score a ≤ score b := hPair a (by simp) b hb
      have hBSum := Finset.sum_erase_add B score hb
      rw [Finset.sum_insert ha]
      linarith

/-- Pairwise cross-boundary ordering is equivalent to the finite Top-K sum
optimizer once the selected cardinality is fixed. -/
theorem isTopKByScore_iff_pairwise {I : Type*}
    [Fintype I] [DecidableEq I]
    (score : I → ℝ) (selected : Finset I) (k : ℕ) :
    IsTopKByScore score selected k ↔
      selected.card = k ∧
        ∀ i ∈ selected, ∀ j ∉ selected, score j ≤ score i := by
  constructor
  · intro h
    exact ⟨h.1, fun i hi j hj ↦
      topK_pairwise_score_order score selected k h hi hj⟩
  · rintro ⟨hCard, hPair⟩
    refine ⟨hCard, ?_⟩
    intro candidate hCandidate
    have hDiffCard : (candidate \ selected).card =
        (selected \ candidate).card := by
      exact Finset.card_sdiff_comm (by simpa [hCard] using hCandidate)
    have hDiffSum : (candidate \ selected).sum score ≤
        (selected \ candidate).sum score := by
      apply sum_le_sum_of_disjoint_pairwise score
        (candidate \ selected) (selected \ candidate) hDiffCard
      intro a ha b hb
      exact hPair b (Finset.mem_sdiff.mp hb).1
        a (Finset.mem_sdiff.mp ha).2
    have hCandidateSplit := candidate.sum_inter_add_sum_sdiff selected score
    have hSelectedSplit := selected.sum_inter_add_sum_sdiff candidate score
    have hInter : (candidate ∩ selected).sum score =
        (selected ∩ candidate).sum score := by
      rw [Finset.inter_comm]
    linarith

private theorem response_osc_eq_witnessSpan {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) (j : Fin (n + 1))
    (hMax : ∀ u, productResponse cell.q F j u ≤
      productResponse cell.q F j (cell.responseMax j))
    (hMin : ∀ u, productResponse cell.q F j (cell.responseMin j) ≤
      productResponse cell.q F j u) :
    osc (productResponse cell.q F j) = responseWitnessSpan cell F j := by
  simp only [osc, responseWitnessSpan,
    max_eq_of_witness_ge _ _ hMax, min_eq_of_witness_le _ _ hMin]

/-- Selector-based validity is exactly the explicit polyhedral cell. -/
theorem activeDecisionCell_valid_iff_polyhedral {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) :
    cell.Valid F ↔ PolyhedralCellValid cell F := by
  constructor
  · rintro ⟨hCard, hTop, hsMax, hsMin, htMax, htMin,
      hResponseMax, hResponseMin⟩
    refine ⟨hCard, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z
      rw [← hsMax]
      exact le_maxVal _ z
    · intro z
      rw [← hsMin]
      exact minVal_le _ z
    · intro z
      rw [← htMax]
      exact le_maxVal _ z
    · intro z
      rw [← htMin]
      exact minVal_le _ z
    · intro j u
      rw [← hResponseMax j]
      exact le_maxVal _ u
    · intro j u
      rw [← hResponseMin j]
      exact minVal_le _ u
    · intro i hi j hj
      have hPair := topK_pairwise_score_order
        (fun r ↦ osc (productResponse cell.q F r))
        cell.selected cell.selected.card hTop hi hj
      simpa [responseWitnessSpan, osc, hResponseMax, hResponseMin] using hPair
  · rintro ⟨hCard, hsMax, hsMin, htMax, htMin,
      hResponseMax, hResponseMin, hPair⟩
    have hsMaxEq := max_eq_of_witness_ge
      (retainedResidual cell.q F cell.selected) cell.selectedMax hsMax
    have hsMinEq := min_eq_of_witness_le
      (retainedResidual cell.q F cell.selected) cell.selectedMin hsMin
    have htMaxEq := max_eq_of_witness_ge
      (retainedResidual cell.q F cell.competitor) cell.competitorMax htMax
    have htMinEq := min_eq_of_witness_le
      (retainedResidual cell.q F cell.competitor) cell.competitorMin htMin
    have hRespMaxEq : ∀ j, maxVal (productResponse cell.q F j) =
        productResponse cell.q F j (cell.responseMax j) := by
      intro j
      exact max_eq_of_witness_ge _ _ (hResponseMax j)
    have hRespMinEq : ∀ j, minVal (productResponse cell.q F j) =
        productResponse cell.q F j (cell.responseMin j) := by
      intro j
      exact min_eq_of_witness_le _ _ (hResponseMin j)
    refine ⟨hCard, ?_, hsMaxEq, hsMinEq, htMaxEq, htMinEq,
      hRespMaxEq, hRespMinEq⟩
    rw [isTopKByScore_iff_pairwise]
    refine ⟨rfl, ?_⟩
    intro i hi j hj
    rw [response_osc_eq_witnessSpan cell F i (hResponseMax i) (hResponseMin i),
      response_osc_eq_witnessSpan cell F j (hResponseMax j) (hResponseMin j)]
    exact hPair i hi j hj

end CIGAMF.P13.D6PolyhedralActiveCell
