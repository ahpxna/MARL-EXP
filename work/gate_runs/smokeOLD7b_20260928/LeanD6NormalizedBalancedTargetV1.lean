import Mathlib
import «LeanD6DecisionInteractionComplexityV1»

/-!
# Correct normalized statement of the balanced D6 target

The legacy `BalancedDecisionInteractionBound` omitted the reference-weight
premises and is refuted in `LeanD6BalancedLawCounterexampleV1`.  This module
states the scientifically intended normalized target and proves that it is
exactly the only missing branch of the normalized all-cell law.
-/

namespace CIGAMF.P13.D6NormalizedBalancedTarget

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6DecisionInteractionComplexity

universe u

def NormalizedBalancedDecisionInteractionBound : Prop :=
  ∀ (n : ℕ) (U : Type u) [Fintype U] [Nonempty U]
    (cell : ActiveDecisionCell n U),
    (∀ c, 0 ≤ jointWeight cell.q c) →
    (∑ c, jointWeight cell.q c = 1) →
    cell.BalancedComplement →
    DecisionInteractionConstantAtMost cell n

def NormalizedAllDecisionInteractionBound : Prop :=
  ∀ (n : ℕ) (U : Type u) [Fintype U] [Nonempty U]
    (cell : ActiveDecisionCell n U),
    (∀ c, 0 ≤ jointWeight cell.q c) →
    (∑ c, jointWeight cell.q c = 1) →
    DecisionInteractionConstantAtMost cell n

/-- Non-balanced cells are already closed; therefore the normalized global
law is logically equivalent to its balanced-complement restriction. -/
theorem normalized_all_iff_balanced :
    NormalizedAllDecisionInteractionBound.{u} ↔
      NormalizedBalancedDecisionInteractionBound.{u} := by
  constructor
  · intro h
    unfold NormalizedAllDecisionInteractionBound at h
    unfold NormalizedBalancedDecisionInteractionBound
    intro n U _ _ cell hWeight hNorm hBalanced
    exact h n U cell hWeight hNorm
  · intro h
    unfold NormalizedBalancedDecisionInteractionBound at h
    unfold NormalizedAllDecisionInteractionBound
    intro n U _ _ cell hWeight hNorm
    apply all_cells_bound_of_balanced_cells
      (fun candidate candidateWeight candidateNorm candidateBalanced =>
        h n U candidate candidateWeight candidateNorm candidateBalanced)
      cell hWeight hNorm

end CIGAMF.P13.D6NormalizedBalancedTarget
