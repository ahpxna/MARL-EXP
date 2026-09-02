import Mathlib
import «LeanTypedCertificateCompletionV1»
import «LeanReferenceIdentifiabilityV1»

/-!
# Typed-certificate reference-evidence separation

The existing RI1/RI2 kernels agree on every observed source row but reverse a
reference-derived Top-1 decision.  This module instantiates TCC-2 with those
actual CIG reference objects.
-/

namespace CIGAMF.P13.TCCReferenceSeparation

open CIGAMF.P13.TypedCertificateCompletion
open CIGAMF.V7.ReferenceIdentifiability

abbrev ObservedKernelRows := Fin 2 → Fin 2 → ℝ

def referenceObservation (reactive : Bool) : ObservedKernelRows :=
  fun a u ↦
    if a ∈ observedSource then
      if reactive then kernelReactive a u else kernelFlat a u
    else 0

/- `false` selects relation 0 and `true` selects relation 1. -/
noncomputable def referenceScore (reactive : Bool) : Fin 2 → ℝ :=
  if reactive then scoreReactive else scoreFlat

noncomputable def referenceRegret (reactive chooseOne : Bool) : ℝ :=
  max (referenceScore reactive 0) (referenceScore reactive 1) -
    referenceScore reactive (if chooseOne then 1 else 0)

theorem RI_TCC_same_observed_reference_evidence :
    referenceObservation false = referenceObservation true := by
  funext a u
  fin_cases a <;> fin_cases u <;>
    norm_num [referenceObservation, observedSource, kernelFlat, kernelReactive]

@[simp] theorem flat_choose_zero_regret : referenceRegret false false = 1 / 2 := by
  norm_num [referenceRegret, referenceScore, scoreFlat]

@[simp] theorem flat_choose_one_regret : referenceRegret false true = 0 := by
  norm_num [referenceRegret, referenceScore, scoreFlat]

@[simp] theorem reactive_choose_zero_regret : referenceRegret true false = 0 := by
  norm_num [referenceRegret, referenceScore, scoreReactive]

@[simp] theorem reactive_choose_one_regret : referenceRegret true true = 1 / 2 := by
  norm_num [referenceRegret, referenceScore, scoreReactive]

theorem RI_TCC_zero_good_decisions_disjoint :
    Disjoint (Good referenceRegret 0 false) (Good referenceRegret 0 true) := by
  rw [Set.disjoint_left]
  intro d hFlat hReactive
  cases d
  · norm_num [Good, referenceRegret, referenceScore,
      scoreFlat, scoreReactive] at hFlat
  · norm_num [Good, referenceRegret, referenceScore,
      scoreFlat, scoreReactive] at hReactive

theorem RI_TCC_observed_reference_rows_not_universally_top1_sufficient :
    ¬ ∃ controller : ObservedKernelRows → Bool,
      referenceRegret false (controller (referenceObservation false)) ≤ 0 ∧
      referenceRegret true (controller (referenceObservation true)) ≤ 0 := by
  exact TCC2_indistinguishability_impossibility
    referenceObservation referenceRegret 0 false true
    RI_TCC_same_observed_reference_evidence
    RI_TCC_zero_good_decisions_disjoint

end CIGAMF.P13.TCCReferenceSeparation
