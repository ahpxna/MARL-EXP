import Mathlib
import «LeanTypedCertificateCompletionV1»
import «LeanQuerySufficiencyQuantitativeV1»

/-!
# Actual query-semantics obstruction for typed certificate completion

The existing zero/interacting worlds have identical complete pairwise-response
summaries but interaction-query targets separated by four.  This file turns
that scalar collision into a TCC decision-level obstruction at error one.
-/

namespace CIGAMF.P13.TCCQuerySeparation

open CIGAMF.P13.TypedCertificateCompletion
open CIGAMF.V4.QuerySufficiency
open CIGAMF.V7.QuerySufficiencyQuantitative

def queryWorld (interacting : Bool) : Bool → Bool → ℝ :=
  if interacting then interactionWorld else zeroWorld

noncomputable def queryObservation (interacting : Bool) :
    BoolPairwiseSummary :=
  finitePairwiseSummary (queryWorld interacting)

noncomputable def interactionPredictionRegret
    (interacting : Bool) (prediction : ℝ) : ℝ :=
  |prediction - interactionQuery (queryWorld interacting)|

theorem QUERY_TCC_same_response_evidence :
    queryObservation false = queryObservation true := by
  simpa [queryObservation, queryWorld] using
    existing_worlds_same_finite_pairwise_summary

theorem QUERY_TCC_unit_good_predictions_disjoint :
    Disjoint (Good interactionPredictionRegret 1 false)
      (Good interactionPredictionRegret 1 true) := by
  rw [Set.disjoint_left]
  intro prediction hZero hInteraction
  change interactionPredictionRegret false prediction ≤ 1 at hZero
  change interactionPredictionRegret true prediction ≤ 1 at hInteraction
  norm_num [interactionPredictionRegret, queryWorld, interactionQuery,
    zeroWorld, interactionWorld] at hZero hInteraction
  rw [abs_le] at hZero hInteraction
  linarith

theorem QUERY_TCC_pairwise_response_not_universally_unit_accurate :
    ¬ ∃ controller : BoolPairwiseSummary → ℝ,
      interactionPredictionRegret false
          (controller (queryObservation false)) ≤ 1 ∧
      interactionPredictionRegret true
          (controller (queryObservation true)) ≤ 1 := by
  exact TCC2_indistinguishability_impossibility
    queryObservation interactionPredictionRegret 1 false true
    QUERY_TCC_same_response_evidence
    QUERY_TCC_unit_good_predictions_disjoint

end CIGAMF.P13.TCCQuerySeparation
