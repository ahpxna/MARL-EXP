import «LeanTypedObstructionActualSeparationsV2»
import «LeanTCCResponseScoreSeparationV1»

/-!
# Five actual typed obstruction separations

This V3 index adds the response/score obstruction to the four V2 witnesses.
Each conjunct is an independently compiled finite CIG impossibility theorem.
-/

namespace CIGAMF.P13.TypedObstructionActualSeparationsV3

open CIGAMF.P13.TCCReferenceSeparation
open CIGAMF.P13.SupportCompressionCriticalWitness
open CIGAMF.P13.D6FirstOrderInsufficiencyWitness
open CIGAMF.P13.TCCQuerySeparation
open CIGAMF.P13.TCCResponseScoreSeparation

theorem all_five_typed_obstruction_witnesses :
    (¬ ∃ controller : Unit → Bool,
      responseScoreRegret false
          (controller (observationWithoutResponse false)) ≤ 0 ∧
      responseScoreRegret true
          (controller (observationWithoutResponse true)) ≤ 0) ∧
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
  exact ⟨RESPONSE_TCC_without_response_not_universally_zero_regret,
    RI_TCC_observed_reference_rows_not_universally_top1_sufficient,
    actual_support_compression_blind_cell2_impossibility,
    D6_B7_full_singleton_response_only_not_universally_zero_regret,
    QUERY_TCC_pairwise_response_not_universally_unit_accurate⟩

end CIGAMF.P13.TypedObstructionActualSeparationsV3
