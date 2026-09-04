import «LeanTCCActualSeparationsV1»
import «LeanTCCQuerySeparationV1»

/-!
# Typed obstruction family: actual CIG separations

This module keeps the generic TCC infrastructure separate from its scientific
instantiations.  Four exact finite obstructions are now connected: reference,
support, interaction, and query semantics.  No response/score obstruction is
claimed here until an admissible same-other-evidence witness is supplied.
-/

namespace CIGAMF.P13.TypedObstructionActualSeparations

open CIGAMF.P13.TCCReferenceSeparation
open CIGAMF.P13.SupportCompressionCriticalWitness
open CIGAMF.P13.D6FirstOrderInsufficiencyWitness
open CIGAMF.P13.TCCQuerySeparation

theorem four_actual_typed_obstructions_are_irreducible :
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
        (controller (firstOrderObservation3 true)) ≤ 0) ∧
    (¬ ∃ controller :
        CIGAMF.V7.QuerySufficiencyQuantitative.BoolPairwiseSummary → ℝ,
      interactionPredictionRegret false
          (controller (queryObservation false)) ≤ 1 ∧
      interactionPredictionRegret true
          (controller (queryObservation true)) ≤ 1) := by
  exact ⟨RI_TCC_observed_reference_rows_not_universally_top1_sufficient,
    actual_support_compression_blind_cell2_impossibility,
    D6_B7_full_singleton_response_only_not_universally_zero_regret,
    QUERY_TCC_pairwise_response_not_universally_unit_accurate⟩

end CIGAMF.P13.TypedObstructionActualSeparations
