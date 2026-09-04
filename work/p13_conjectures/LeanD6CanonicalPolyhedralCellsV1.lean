import Mathlib
import «LeanD6CanonicalUniformDecisionCertificateV1»
import «LeanD6DecisionInteractionComplexityV1»
import «LeanD6PAECFin4»
import «LeanD6PAECFin6»

/-!
# Exact canonical polyhedral cells in dimensions four and six

The symbolic three- and five-cycle identities are instantiated in the new
restricted certificate language.  These theorems establish canonical-cell
upper bounds of mass `3` and `5`; they do not claim LP minimality or cover
arbitrary active-extrema branches.
-/

namespace CIGAMF.P13.D6CanonicalPolyhedralCells

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6PolyhedralActiveCell
open CIGAMF.P13.D6CanonicalUniformDecisionCertificate
open CIGAMF.P13.D6DecisionInteractionComplexity
open CIGAMF.P13.D6PAECFin4
open CIGAMF.P13.D6PAECFin6

def canonicalCell4 : ActiveDecisionCell 3 (Fin 2) where
  q := pointMass4
  selected := selected4
  competitor := rejected4
  selectedMax := s4
  selectedMin := t4
  competitorMax := z4
  competitorMin := o4
  responseMax := fun _ ↦ 0
  responseMin := fun _ ↦ 1

private def coordinate4 : Fin 3 → Fin 4 := ![1, 0, 1]
private def upper4 : Fin 3 → Fin 4 → Fin 2 := ![s4, x4b, o4]
private def anchor4 : Fin 3 → Fin 4 → Fin 2 := fun _ ↦ z4
private def constraint4 : Fin 2 → CanonicalConstraintAtom 3 (Fin 2) :=
  ![.topC 0 3, .topC 1 2]

noncomputable def canonicalCertificate4 :
    CanonicalUniformDecisionCertificate canonicalCell4 (Fin 3) (Fin 2) where
  coordinate := coordinate4
  upperWorld := upper4
  anchorWorld := anchor4
  alpha := fun _ ↦ 1
  constraintAtom := constraint4
  beta := fun _ ↦ 1
  beta_nonnegative := by intro j; norm_num
  functional_identity := by
    intro F
    change retainedResidual pointMass4 F selected4 s4 -
        retainedResidual pointMass4 F selected4 t4 -
        retainedResidual pointMass4 F rejected4 z4 +
        retainedResidual pointMass4 F rejected4 o4 = _
    unfold retainedResidual
    rw [← congrFun (rS4_eq_retained F) s4,
      ← congrFun (rS4_eq_retained F) t4,
      ← congrFun (rT4_eq_retained F) z4,
      ← congrFun (rT4_eq_retained F) o4]
    have hId :
        rS4 F s4 - rS4 F t4 - rT4 F z4 + rT4 F o4 =
          cycleSum4 F + topCorrection4 F := by
      linarith [three_cycle_identity F]
    rw [hId]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [coordinate4, upper4, anchor4, constraint4,
      canonicalConstraintValue, canonicalCell4, responseWitnessSpan,
      cycleSum4, topCorrection4, selected4,
      cycleFunctional_eq_mixedDifference]
    ring

@[simp] theorem canonicalCertificate4_mass : canonicalCertificate4.mass = 3 := by
  norm_num [canonicalCertificate4, CanonicalUniformDecisionCertificate.mass]

theorem canonicalCell4_balanced : canonicalCell4.BalancedComplement := by
  simp [ActiveDecisionCell.BalancedComplement, canonicalCell4,
    selected4, rejected4] <;> decide

theorem canonicalCell4_decisionInteraction_atMost_three :
    DecisionInteractionConstantAtMost canonicalCell4 3 := by
  intro F hCell hUnit
  have h := canonicalUniformDecisionCertificate_sound canonicalCell4
    canonicalCertificate4 F 1 (by norm_num) hCell hUnit
  simpa using h

def canonicalCell6 : ActiveDecisionCell 5 (Fin 2) where
  q := pointMass6
  selected := selected6
  competitor := rejected6
  selectedMax := s6
  selectedMin := t6
  competitorMax := z6
  competitorMin := o6
  responseMax := fun _ ↦ 0
  responseMin := fun _ ↦ 1

private def coordinate6 : Fin 5 → Fin 6 := ![1, 2, 0, 1, 2]
private def upper6 : Fin 5 → Fin 6 → Fin 2 := ![p62, s6, b60, b61, o6]
private def anchor6 : Fin 5 → Fin 6 → Fin 2 := fun _ ↦ z6
private def constraint6 : Fin 3 → CanonicalConstraintAtom 5 (Fin 2) :=
  ![.topC 0 5, .topC 1 4, .topC 2 3]

noncomputable def canonicalCertificate6 :
    CanonicalUniformDecisionCertificate canonicalCell6 (Fin 5) (Fin 3) where
  coordinate := coordinate6
  upperWorld := upper6
  anchorWorld := anchor6
  alpha := fun _ ↦ 1
  constraintAtom := constraint6
  beta := fun _ ↦ 1
  beta_nonnegative := by intro j; norm_num
  functional_identity := by
    intro F
    change retainedResidual pointMass6 F selected6 s6 -
        retainedResidual pointMass6 F selected6 t6 -
        retainedResidual pointMass6 F rejected6 z6 +
        retainedResidual pointMass6 F rejected6 o6 = _
    unfold retainedResidual
    rw [← congrFun (rS6_eq_retained F) s6,
      ← congrFun (rS6_eq_retained F) t6,
      ← congrFun (rT6_eq_retained F) z6,
      ← congrFun (rT6_eq_retained F) o6]
    have hId :
        rS6 F s6 - rS6 F t6 - rT6 F z6 + rT6 F o6 =
          cycleSum6 F + topCorrection6 F := by
      linarith [five_cycle_identity F]
    rw [hId]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [coordinate6, upper6, anchor6, constraint6,
      canonicalConstraintValue, canonicalCell6, responseWitnessSpan,
      cycleSum6, topCorrection6, selected6,
      cycleFunctional_eq_mixedDifference]
    ring

@[simp] theorem canonicalCertificate6_mass : canonicalCertificate6.mass = 5 := by
  norm_num [canonicalCertificate6, CanonicalUniformDecisionCertificate.mass]

theorem canonicalCell6_balanced : canonicalCell6.BalancedComplement := by
  simp [ActiveDecisionCell.BalancedComplement, canonicalCell6,
    selected6, rejected6] <;> decide

theorem canonicalCell6_decisionInteraction_atMost_five :
    DecisionInteractionConstantAtMost canonicalCell6 5 := by
  intro F hCell hUnit
  have h := canonicalUniformDecisionCertificate_sound canonicalCell6
    canonicalCertificate6 F 1 (by norm_num) hCell hUnit
  simpa using h

end CIGAMF.P13.D6CanonicalPolyhedralCells
