import Mathlib
import «LeanTypedCertificateCompletionV1»
import «LeanFunctionalRankingV6»

/-!
# Actual response/score obstruction for typed certificate completion

Two finite CIG response worlds keep all non-response evidence fixed and swap
the unique capacity-maximizing relation.  Therefore a controller that cannot
observe response/score evidence cannot be universally zero-regret.
-/

namespace CIGAMF.P13.TCCResponseScoreSeparation

open CIGAMF.P13.TypedCertificateCompletion
open CIGAMF.V6.FunctionalRanking
open CIGAMF.V4.FunctionalBoundary
open CIGAMF.V4.SupportGeometry

def responseScoreWorld (flipped : Bool) (j a : Fin 2) : ℝ :=
  if flipped then
    if j = 1 then if a = 1 then 2 else 0 else 0
  else
    if j = 0 then if a = 1 then 2 else 0 else 0

/-- All evidence except the response/score table is fixed. -/
def observationWithoutResponse (_ : Bool) : Unit := ()

noncomputable def responseScoreRegret
    (flipped chooseOne : Bool) : ℝ :=
  max (capacity (responseScoreWorld flipped 0))
      (capacity (responseScoreWorld flipped 1)) -
    capacity (responseScoreWorld flipped (if chooseOne then 1 else 0))

@[simp] theorem response_world_zero_choice_zero :
    responseScoreRegret false false = 0 := by
  norm_num [responseScoreRegret, responseScoreWorld, capacity, osc,
    maxVal_fin2, minVal_fin2]

@[simp] theorem response_world_zero_choice_one :
    responseScoreRegret false true = 2 := by
  norm_num [responseScoreRegret, responseScoreWorld, capacity, osc,
    maxVal_fin2, minVal_fin2]

@[simp] theorem response_world_one_choice_zero :
    responseScoreRegret true false = 2 := by
  norm_num [responseScoreRegret, responseScoreWorld, capacity, osc,
    maxVal_fin2, minVal_fin2]

@[simp] theorem response_world_one_choice_one :
    responseScoreRegret true true = 0 := by
  norm_num [responseScoreRegret, responseScoreWorld, capacity, osc,
    maxVal_fin2, minVal_fin2]

theorem RESPONSE_TCC_zero_good_decisions_disjoint :
    Disjoint (Good responseScoreRegret 0 false)
      (Good responseScoreRegret 0 true) := by
  rw [Set.disjoint_left]
  intro decision hFalse hTrue
  cases decision
  · norm_num [Good, responseScoreRegret, responseScoreWorld, capacity, osc,
      maxVal_fin2, minVal_fin2] at hTrue
  · norm_num [Good, responseScoreRegret, responseScoreWorld, capacity, osc,
      maxVal_fin2, minVal_fin2] at hFalse

theorem RESPONSE_TCC_without_response_not_universally_zero_regret :
    ¬ ∃ controller : Unit → Bool,
      responseScoreRegret false (controller (observationWithoutResponse false)) ≤ 0 ∧
      responseScoreRegret true (controller (observationWithoutResponse true)) ≤ 0 := by
  exact TCC2_indistinguishability_impossibility
    observationWithoutResponse responseScoreRegret 0 false true rfl
    RESPONSE_TCC_zero_good_decisions_disjoint

end CIGAMF.P13.TCCResponseScoreSeparation
