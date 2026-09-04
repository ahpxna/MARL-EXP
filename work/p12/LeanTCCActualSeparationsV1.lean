import «LeanTCCReferenceSeparationV1»
import «LeanSupportCompressionCriticalWitnessV1»
import «LeanD6FirstOrderInsufficiencyWitnessV2»

/-!
# Actual CIG heterogeneous-evidence separations

This is a compact theorem-family index, not a new abstract framework.  Each
conjunct imports an independently exact finite CIG witness and an application
of the generic TCC-2 indistinguishability theorem.
-/

namespace CIGAMF.P13.TCCActualSeparations

open CIGAMF.P13.TCCReferenceSeparation
open CIGAMF.P13.SupportCompressionCriticalWitness
open CIGAMF.P13.D6FirstOrderInsufficiencyWitness

theorem TCC_actual_evidence_types_not_interchangeable :
    (¬ ∃ controller : ObservedKernelRows → Bool,
      referenceRegret false (controller (referenceObservation false)) ≤ 0 ∧
      referenceRegret true (controller (referenceObservation true)) ≤ 0) ∧
    (¬ ∃ controller : Finset (Fin 3) → Bool,
      ∀ omega : Finset (Fin 3),
        supportCompressionRegret omega
          (controller (eraseCell2Observation omega)) ≤ 0) ∧
    (¬ ∃ controller : FirstOrderObservation3 → SingletonDecisionSpace3,
      fullSingletonRegret3 false
        (controller (firstOrderObservation3 false)) ≤ 0 ∧
      fullSingletonRegret3 true
        (controller (firstOrderObservation3 true)) ≤ 0) := by
  exact ⟨RI_TCC_observed_reference_rows_not_universally_top1_sufficient,
    actual_support_compression_blind_cell2_impossibility,
    D6_B7_full_singleton_response_only_not_universally_zero_regret⟩

end CIGAMF.P13.TCCActualSeparations
