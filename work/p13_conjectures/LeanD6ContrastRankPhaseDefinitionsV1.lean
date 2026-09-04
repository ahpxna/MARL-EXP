import Mathlib
import «LeanD6InteractionContrastRankOneV1»
import «LeanD6NormalizedBalancedTargetV1»

/-!
# D6 interaction-contrast phase language

This file is deliberately definitional.  The prior universal normalized
balanced `m - 1` law is refuted by the ternary counterexample, so no result
here asserts that rank one implies any sharp decision constant.  These
predicates isolate that now-testable phase-transition question while keeping
the old, falsified universal route out of the active theorem path.
-/

namespace CIGAMF.P13.D6ContrastRankPhaseDefinitions

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6InteractionContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

/-- A numerical world in one fixed active cell, normalized at the product
reference and with all coordinate-local centered interaction profiles
collinear. -/
def RankOneNormalizedBalancedWorld {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  (∀ c, 0 ≤ jointWeight cell.q c) ∧
  (∑ c, jointWeight cell.q c = 1) ∧
  cell.BalancedComplement ∧
  cell.Valid F ∧
  UnitInteractionBound F ∧
  AllCoordinatesInteractionContrastRankOne cell.q F

/-- Restricted uniform decision constant for rank-one normalized balanced
worlds in one active decision cell. -/
def RankOneDecisionInteractionConstantAtMost {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ) : Prop :=
  ∀ F, RankOneNormalizedBalancedWorld cell F →
    2 * (productCompressionLoss F (productResponse cell.q F) cell.selected -
      productCompressionLoss F (productResponse cell.q F) cell.competitor) ≤
      constant

/-- The new phase-transition hypothesis.  It is a named `Prop`, not a
theorem: this archive makes no claim that it has been proved. -/
def RankOneMMinusOnePhaseConjecture : Prop :=
  ∀ (n : ℕ) (cell : ActiveDecisionCell n U),
    RankOneDecisionInteractionConstantAtMost cell n

/-- The complementary saturation direction is likewise only a research
target.  The existing ternary witness establishes one rank-at-least-two
instance, not this universal statement. -/
def RankAtLeastTwoSaturationPhaseConjecture : Prop :=
  ∀ (n : ℕ) (cell : ActiveDecisionCell n U),
    (∃ F, (∀ c, 0 ≤ jointWeight cell.q c) ∧
      (∑ c, jointWeight cell.q c = 1) ∧ cell.BalancedComplement ∧
      cell.Valid F ∧ UnitInteractionBound F ∧
      ¬ AllCoordinatesInteractionContrastRankOne cell.q F) →
    ¬ RankOneDecisionInteractionConstantAtMost cell n

end CIGAMF.P13.D6ContrastRankPhaseDefinitions
