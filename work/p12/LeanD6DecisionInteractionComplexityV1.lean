import Mathlib
import «LeanD6UniformDecisionCertificateV1»
import «LeanD6SymmetricDifferenceReductionV1»

/-!
# Predicate-level decision--interaction complexity

The primary definition avoids premature `sSup` engineering.  A constant is
uniform over every numerical world function in one fixed active decision
cell.  This is the correct layer at which a later sharp `m-1` theorem must be
proved or falsified.
-/

namespace CIGAMF.P13.D6DecisionInteractionComplexity

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6UniformDecisionCertificate
open CIGAMF.P13.D6SymmetricDifferenceReduction

variable {U : Type*} [Fintype U] [Nonempty U]

def UnitInteractionBound {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  ∀ i x c, |mixedDifference F i x c| ≤ 1

def DecisionInteractionConstantAtMost {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ) : Prop :=
  ∀ F, cell.Valid F → UnitInteractionBound F →
    2 * (productCompressionLoss F (productResponse cell.q F) cell.selected -
      productCompressionLoss F (productResponse cell.q F) cell.competitor) ≤
      constant

/-- The decision-cell feasible set whose supremum is the uniform
decision--interaction complexity.  Unlike the legacy instance-wise PAEC
mass, this set ranges over *all* numerical worlds compatible with the fixed
cell before taking a supremum. -/
def admissibleDecisionGaps {n : ℕ}
    (cell : ActiveDecisionCell n U) : Set ℝ :=
  {gap | ∃ F, cell.Valid F ∧ UnitInteractionBound F ∧
    gap = 2 * (productCompressionLoss F (productResponse cell.q F)
        cell.selected -
      productCompressionLoss F (productResponse cell.q F)
        cell.competitor)}

/-- Uniform decision--interaction constant for one active decision cell. -/
noncomputable def kappaDI {n : ℕ}
    (cell : ActiveDecisionCell n U) : ℝ :=
  sSup (admissibleDecisionGaps cell)

theorem kappaDI_le_of_constant {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ)
    (hNonempty : (admissibleDecisionGaps cell).Nonempty)
    (hConstant : DecisionInteractionConstantAtMost cell constant) :
    kappaDI cell ≤ constant := by
  unfold kappaDI
  apply csSup_le hNonempty
  intro gap hGap
  rcases hGap with ⟨F, hCell, hUnit, rfl⟩
  exact hConstant F hCell hUnit

theorem decisionInteractionConstant_mono {n : ℕ}
    (cell : ActiveDecisionCell n U) {c d : ℝ}
    (h : DecisionInteractionConstantAtMost cell c) (hcd : c ≤ d) :
    DecisionInteractionConstantAtMost cell d := by
  intro F hCell hUnit
  exact (h F hCell hUnit).trans hcd

/-- Any uniform certificate whose mass is at most `c` supplies a uniform
decision--interaction upper bound for the cell. -/
theorem decisionInteractionConstant_of_uniformCertificate {n : ℕ}
    (cell : ActiveDecisionCell n U)
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : UniformDecisionCertificate cell R J)
    (c : ℝ) (hMass : cert.mass ≤ c)
    (hConstraints : ∀ F, cell.Valid F → ConstraintsValid cert F) :
    DecisionInteractionConstantAtMost cell c := by
  intro F hCell hUnit
  have hSound := uniformDecisionCertificate_sound cell cert F 1
    (by norm_num) hCell (hConstraints F hCell) hUnit
  have hMassOne : cert.mass * 1 ≤ c := by simpa using hMass
  simpa using hSound.trans hMassOne

theorem kappaDI_le_certificate_mass {n : ℕ}
    (cell : ActiveDecisionCell n U)
    {R J : Type*} [Fintype R] [Fintype J]
    (cert : UniformDecisionCertificate cell R J)
    (hNonempty : (admissibleDecisionGaps cell).Nonempty)
    (hConstraints : ∀ F, cell.Valid F → ConstraintsValid cert F) :
    kappaDI cell ≤ cert.mass := by
  apply kappaDI_le_of_constant cell cert.mass hNonempty
  exact decisionInteractionConstant_of_uniformCertificate cell cert cert.mass
    (le_refl _) hConstraints

/-- NEW-1 gives the sharp target constant on every active cell except the
single balanced-complement geometry.  This is a uniform result over all
numerical worlds in the cell, not an instance-wise PAEC rescaling. -/
theorem nonbalanced_decisionInteractionConstant_atMost_n {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (hWeight : ∀ c, 0 ≤ jointWeight cell.q c)
    (hNorm : ∑ c, jointWeight cell.q c = 1)
    (hNotBalanced : ¬ cell.BalancedComplement) :
    DecisionInteractionConstantAtMost cell n := by
  intro F hCell hUnit
  rcases hCell with ⟨hCard, hTop, hsMax, hsMin, htMax, htMin,
    hResponseMax, hResponseMin⟩
  have hPair := pair_half_factor_except_balanced_complement
    cell.q F 1 hWeight hNorm (by norm_num) hUnit
    cell.selected cell.competitor cell.selected.card hTop hCard.symm
    hNotBalanced
  norm_num at hPair ⊢
  linarith

theorem nonbalanced_kappaDI_le_n {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (hWeight : ∀ c, 0 ≤ jointWeight cell.q c)
    (hNorm : ∑ c, jointWeight cell.q c = 1)
    (hNotBalanced : ¬ cell.BalancedComplement)
    (hNonempty : (admissibleDecisionGaps cell).Nonempty) :
    kappaDI cell ≤ n := by
  exact kappaDI_le_of_constant cell n hNonempty
    (nonbalanced_decisionInteractionConstant_atMost_n cell hWeight hNorm
      hNotBalanced)

/-- The uniform sharp problem has now been reduced exactly to the
balanced-complement cells. -/
theorem all_cells_bound_of_balanced_cells {n : ℕ}
    (hBalanced : ∀ (cell : ActiveDecisionCell n U),
      (∀ c, 0 ≤ jointWeight cell.q c) →
      (∑ c, jointWeight cell.q c = 1) →
      cell.BalancedComplement →
      DecisionInteractionConstantAtMost cell n)
    (cell : ActiveDecisionCell n U)
    (hWeight : ∀ c, 0 ≤ jointWeight cell.q c)
    (hNorm : ∑ c, jointWeight cell.q c = 1) :
    DecisionInteractionConstantAtMost cell n := by
  by_cases hCell : cell.BalancedComplement
  · exact hBalanced cell hWeight hNorm hCell
  · exact nonbalanced_decisionInteractionConstant_atMost_n cell hWeight
      hNorm hCell

theorem odd_coordinate_count_kappaDI_le_n {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (hWeight : ∀ c, 0 ≤ jointWeight cell.q c)
    (hNorm : ∑ c, jointWeight cell.q c = 1)
    (hOdd : Odd (n + 1))
    (hNonempty : (admissibleDecisionGaps cell).Nonempty) :
    kappaDI cell ≤ n := by
  apply nonbalanced_kappaDI_le_n cell hWeight hNorm
  · intro hBalanced
    rcases hBalanced with ⟨hEven, hDisjoint, hUnion⟩
    rcases hOdd with ⟨d, hd⟩
    omega
  · exact hNonempty

/-- The exact P0 target is deliberately exposed as a predicate, not assumed:
every balanced-complement active cell should have constant at most `n=m-1`.
No theorem in this file asserts that still-open statement. -/
def BalancedDecisionInteractionBound : Prop :=
  ∀ (n : ℕ) (U : Type*) [Fintype U] [Nonempty U]
    (cell : ActiveDecisionCell n U),
    cell.BalancedComplement → DecisionInteractionConstantAtMost cell n

end CIGAMF.P13.D6DecisionInteractionComplexity
