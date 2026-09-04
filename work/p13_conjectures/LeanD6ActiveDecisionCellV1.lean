import Mathlib
import «LeanD6H3Exchange»

/-!
# Uniform active decision cells for D6

The data below freezes the combinatorial/active-extremum regime before a
numerical world function is supplied.  In a valid cell the doubled
selected-versus-competitor loss gap is one fixed linear functional of `F`.
This is the non-instance-wise language needed by decision--interaction
complexity; it does not alter the legacy PAEC files.
-/

namespace CIGAMF.P13.D6ActiveDecisionCell

open scoped BigOperators
open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange

variable {U : Type*} [Fintype U] [Nonempty U]

structure ActiveDecisionCell (n : ℕ) (U : Type*) where
  q : Fin (n + 1) → U → ℝ
  selected : Finset (Fin (n + 1))
  competitor : Finset (Fin (n + 1))
  selectedMax : Fin (n + 1) → U
  selectedMin : Fin (n + 1) → U
  competitorMax : Fin (n + 1) → U
  competitorMin : Fin (n + 1) → U
  responseMax : Fin (n + 1) → U
  responseMin : Fin (n + 1) → U

def ActiveDecisionCell.Valid {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  cell.selected.card = cell.competitor.card ∧
  IsTopKByScore (fun j ↦ osc (productResponse cell.q F j))
    cell.selected cell.selected.card ∧
  maxVal (retainedResidual cell.q F cell.selected) =
    retainedResidual cell.q F cell.selected cell.selectedMax ∧
  minVal (retainedResidual cell.q F cell.selected) =
    retainedResidual cell.q F cell.selected cell.selectedMin ∧
  maxVal (retainedResidual cell.q F cell.competitor) =
    retainedResidual cell.q F cell.competitor cell.competitorMax ∧
  minVal (retainedResidual cell.q F cell.competitor) =
    retainedResidual cell.q F cell.competitor cell.competitorMin ∧
  (∀ j, maxVal (productResponse cell.q F j) =
    productResponse cell.q F j (cell.responseMax j)) ∧
  ∀ j, minVal (productResponse cell.q F j) =
    productResponse cell.q F j (cell.responseMin j)

def ActiveDecisionCell.BalancedComplement {n : ℕ}
    (cell : ActiveDecisionCell n U) : Prop :=
  n + 1 = 2 * cell.selected.card ∧
  Disjoint cell.selected cell.competitor ∧
  cell.selected ∪ cell.competitor = Finset.univ

noncomputable def decisionLinearFunctional {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  retainedResidual cell.q F cell.selected cell.selectedMax -
    retainedResidual cell.q F cell.selected cell.selectedMin -
    retainedResidual cell.q F cell.competitor cell.competitorMax +
    retainedResidual cell.q F cell.competitor cell.competitorMin

private theorem productResponse_add {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F G : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u : U) :
    productResponse q (fun z ↦ F z + G z) i u =
      productResponse q F i u + productResponse q G i u := by
  unfold productResponse productExpectation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring

private theorem productResponse_smul {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (a : ℝ) (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u : U) :
    productResponse q (a • F) i u = a * productResponse q F i u := by
  unfold productResponse productExpectation
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

private theorem retainedResidual_add {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F G : (Fin (n + 1) → U) → ℝ)
    (S : Finset (Fin (n + 1))) (z : Fin (n + 1) → U) :
    retainedResidual q (fun x ↦ F x + G x) S z =
      retainedResidual q F S z + retainedResidual q G S z := by
  unfold retainedResidual
  simp_rw [productResponse_add]
  rw [Finset.sum_add_distrib]
  ring

private theorem retainedResidual_smul {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (a : ℝ) (F : (Fin (n + 1) → U) → ℝ)
    (S : Finset (Fin (n + 1))) (z : Fin (n + 1) → U) :
    retainedResidual q (a • F) S z =
      a * retainedResidual q F S z := by
  unfold retainedResidual
  simp_rw [productResponse_smul]
  rw [← Finset.mul_sum]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem decisionLinearFunctional_add {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F G : (Fin (n + 1) → U) → ℝ) :
    decisionLinearFunctional cell (F + G) =
      decisionLinearFunctional cell F + decisionLinearFunctional cell G := by
  change decisionLinearFunctional cell (fun x ↦ F x + G x) = _
  unfold decisionLinearFunctional
  rw [retainedResidual_add, retainedResidual_add,
    retainedResidual_add, retainedResidual_add]
  ring

theorem decisionLinearFunctional_smul {n : ℕ}
    (cell : ActiveDecisionCell n U) (a : ℝ)
    (F : (Fin (n + 1) → U) → ℝ) :
    decisionLinearFunctional cell (a • F) =
      a * decisionLinearFunctional cell F := by
  simp only [decisionLinearFunctional, retainedResidual_smul]
  ring

noncomputable def decisionLinearMap {n : ℕ}
    (cell : ActiveDecisionCell n U) :
    ((Fin (n + 1) → U) → ℝ) →ₗ[ℝ] ℝ where
  toFun := decisionLinearFunctional cell
  map_add' := decisionLinearFunctional_add cell
  map_smul' := by
    intro a F
    simpa [smul_eq_mul] using decisionLinearFunctional_smul cell a F

/-- In a fixed valid active cell, the nonlinear oscillation selectors have
already been resolved, leaving one exact linear functional of `F`. -/
theorem doubledDecisionGap_eq_linear {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ)
    (hCell : cell.Valid F) :
    2 * (productCompressionLoss F (productResponse cell.q F) cell.selected -
      productCompressionLoss F (productResponse cell.q F) cell.competitor) =
      decisionLinearMap cell F := by
  rcases hCell with ⟨hCard, hTop, hsMax, hsMin, htMax, htMin,
    hResponseMax, hResponseMin⟩
  unfold productCompressionLoss
  change
    2 * (osc (retainedResidual cell.q F cell.selected) / 2 -
      osc (retainedResidual cell.q F cell.competitor) / 2) = _
  simp only [osc, hsMax, hsMin, htMax, htMin]
  change _ = decisionLinearFunctional cell F
  unfold decisionLinearFunctional
  ring

end CIGAMF.P13.D6ActiveDecisionCell
