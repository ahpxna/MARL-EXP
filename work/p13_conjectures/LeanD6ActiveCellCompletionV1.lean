import Mathlib
import «LeanD6ActiveCellRemainderDecompositionV1»
import «LeanD6NormalizedBalancedTargetV1»
import «LeanD6CanonicalPolyhedralCellsV1»
import «LeanD6Fin6WeightedDualCertificateV1»

/-!
# Canonical active-cell completion interface

This file isolates the exact remaining scientific obligation.  A completion
is an actual restricted canonical certificate of the requested mass.  Its
soundness and the normalized global consequence are proved; universal
existence for every balanced cell is intentionally not assumed or claimed.
-/

namespace CIGAMF.P13.D6ActiveCellCompletion

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6CanonicalUniformDecisionCertificate
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6NormalizedBalancedTarget
open CIGAMF.P13.D6CanonicalPolyhedralCells
open CIGAMF.P13.D6Fin6WeightedDualCertificate

universe u

variable {U : Type u} [Fintype U] [Nonempty U]

def HasCanonicalActiveCellCompletionAtMost {n : ℕ}
    (cell : ActiveDecisionCell n U) (bound : ℝ) : Prop :=
  ∃ (R J : Type) (_ : Fintype R) (_ : Fintype J)
      (cert : CanonicalUniformDecisionCertificate cell R J),
    cert.mass ≤ bound

theorem decisionInteractionConstant_of_canonical_completion {n : ℕ}
    (cell : ActiveDecisionCell n U) (bound : ℝ)
    (hCompletion : HasCanonicalActiveCellCompletionAtMost cell bound) :
    DecisionInteractionConstantAtMost cell bound := by
  rcases hCompletion with ⟨R, J, instR, instJ, cert, hMass⟩
  letI : Fintype R := instR
  letI : Fintype J := instJ
  intro F hCell hUnit
  have h := canonicalUniformDecisionCertificate_sound cell cert F 1
    (by norm_num) hCell hUnit
  have hBound : cert.mass * 1 ≤ bound := by simpa using hMass
  exact h.trans hBound

/-- This theorem is the exact zero-sorry bridge needed after the still-open
construction: canonical completion of every normalized balanced cell implies
the normalized balanced law. -/
theorem normalized_balanced_law_of_canonical_completion
    (hComplete : ∀ (n : ℕ) (U : Type u) [Fintype U] [Nonempty U]
      (cell : ActiveDecisionCell n U),
      (∀ c, 0 ≤ jointWeight cell.q c) →
      (∑ c, jointWeight cell.q c = 1) →
      cell.BalancedComplement →
      HasCanonicalActiveCellCompletionAtMost cell n) :
    NormalizedBalancedDecisionInteractionBound.{u} := by
  intro n U instF instN cell hWeight hNorm hBalanced
  exact decisionInteractionConstant_of_canonical_completion cell n
    (hComplete n U cell hWeight hNorm hBalanced)

theorem canonicalCell4_has_completion_atMost_three :
    HasCanonicalActiveCellCompletionAtMost canonicalCell4 3 := by
  exact ⟨Fin 3, Fin 2, inferInstance, inferInstance,
    canonicalCertificate4, by simp⟩

theorem gammaFiveCell_has_completion_atMost_five :
    HasCanonicalActiveCellCompletionAtMost
      CIGAMF.P13.D6Fin6GammaFiveSaturation.gammaFiveCell 5 := by
  exact ⟨Fin 6, Fin 7, inferInstance, inferInstance,
    gammaFiveWeightedCertificate, by simp⟩

end CIGAMF.P13.D6ActiveCellCompletion
