import Mathlib
import «LeanD6BinaryAllCoordinatesRankOneV1»
import «LeanD6NormalizedBalancedTargetV1»

/-! Corrected, self-contained phase-language definitions.  The legacy V1
malformed non-rank implication is retained as history but is intentionally
not imported by this active V2 branch. -/

namespace CIGAMF.P13.D6ContrastRankPhaseDefinitionsV2

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6InteractionContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

def RankOneNormalizedBalancedWorld {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  (∀ c, 0 ≤ jointWeight cell.q c) ∧
  (∑ c, jointWeight cell.q c = 1) ∧
  cell.BalancedComplement ∧
  cell.Valid F ∧
  UnitInteractionBound F ∧
  AllCoordinatesInteractionContrastRankOne cell.q F

def RankOneDecisionInteractionConstantAtMost {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ) : Prop :=
  ∀ F, RankOneNormalizedBalancedWorld cell F →
    2 * (productCompressionLoss F (productResponse cell.q F) cell.selected -
      productCompressionLoss F (productResponse cell.q F) cell.competitor) ≤
      constant

def RankNonOneNormalizedBalancedWorld {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  (∀ c, 0 ≤ jointWeight cell.q c) ∧
  (∑ c, jointWeight cell.q c = 1) ∧
  cell.BalancedComplement ∧
  cell.Valid F ∧
  UnitInteractionBound F ∧
  ¬ AllCoordinatesInteractionContrastRankOne cell.q F

def RankNonOneDecisionInteractionConstantAtMost {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ) : Prop :=
  ∀ F, RankNonOneNormalizedBalancedWorld cell F →
    2 * (productCompressionLoss F (productResponse cell.q F) cell.selected -
      productCompressionLoss F (productResponse cell.q F) cell.competitor) ≤
      constant

def RankNonOneSaturates {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ) : Prop :=
  ∃ F, RankNonOneNormalizedBalancedWorld cell F ∧
    constant ≤ 2 *
      (productCompressionLoss F (productResponse cell.q F) cell.selected -
        productCompressionLoss F (productResponse cell.q F) cell.competitor)

def StrictTopC {n : ℕ}
    (cell : ActiveDecisionCell n U)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  ∀ i ∈ cell.selected, ∀ j ∉ cell.selected,
    CIGAMF.V4.SupportGeometry.osc (productResponse cell.q F j) <
      CIGAMF.V4.SupportGeometry.osc (productResponse cell.q F i)

def RankNonOneViolates {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ) : Prop :=
  ∃ F, RankNonOneNormalizedBalancedWorld cell F ∧
    constant < 2 *
      (productCompressionLoss F (productResponse cell.q F) cell.selected -
        productCompressionLoss F (productResponse cell.q F) cell.competitor)

def StrictRankNonOneViolates {n : ℕ}
    (cell : ActiveDecisionCell n U) (constant : ℝ) : Prop :=
  ∃ F, RankNonOneNormalizedBalancedWorld cell F ∧ StrictTopC cell F ∧
    constant < 2 *
      (productCompressionLoss F (productResponse cell.q F) cell.selected -
        productCompressionLoss F (productResponse cell.q F) cell.competitor)

/-- OPEN / NOT ATTEMPTED AFTER API REPAIR. -/
def RankOneNormalizedBalancedDecisionInteractionBound : Prop :=
  ∀ (n : ℕ) (cell : ActiveDecisionCell n U),
    RankOneDecisionInteractionConstantAtMost cell n

end CIGAMF.P13.D6ContrastRankPhaseDefinitionsV2
