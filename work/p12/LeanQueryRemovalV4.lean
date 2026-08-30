import Mathlib
import «LeanQuerySufficiencyV4»

/-! Exact finite removal/necessity witness for Chain E. -/
namespace CIGAMF.V4.QueryRemoval

open QuerySufficiency

def removalEffect (F : Bool → Bool → ℝ) (a : Bool) : ℝ :=
  F a false - F false false

theorem E5_same_pairwise_different_removal :
    (∀ a, responseFirst zeroWorld a = responseFirst interactionWorld a) ∧
      (∀ b, responseSecond zeroWorld b = responseSecond interactionWorld b) ∧
      removalEffect zeroWorld true ≠ removalEffect interactionWorld true := by
  refine ⟨E1_same_pairwise_response.1, E1_same_pairwise_response.2, ?_⟩
  norm_num [removalEffect, zeroWorld, interactionWorld]

theorem E6_removal_not_identified_by_pairwise_summary :
    ∃ F G : Bool → Bool → ℝ,
      (∀ a, responseFirst F a = responseFirst G a) ∧
      (∀ b, responseSecond F b = responseSecond G b) ∧
      removalEffect F true ≠ removalEffect G true := by
  exact ⟨zeroWorld, interactionWorld, E5_same_pairwise_different_removal.1,
    E5_same_pairwise_different_removal.2.1,
    E5_same_pairwise_different_removal.2.2⟩

end CIGAMF.V4.QueryRemoval
