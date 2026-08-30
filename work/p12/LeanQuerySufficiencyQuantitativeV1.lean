import Mathlib
import «LeanQuerySufficiencyV4»

/-! Quantitative consequence of a response-summary collision.

This is a deterministic minimax lower bound, not a statistical asymptotic
claim and not a novelty claim. -/

namespace CIGAMF.V7.QuerySufficiencyQuantitative

open CIGAMF.V4.QuerySufficiency

theorem E5_response_only_minimax_lower_bound
    {M S : Type*}
    (summary : M → S) (T : M → ℝ) (psi : S → ℝ)
    (m1 m2 : M) (hsummary : summary m1 = summary m2) :
    |T m1 - T m2| / 2 ≤
      max |psi (summary m1) - T m1| |psi (summary m2) - T m2| := by
  have htri : |T m1 - T m2| ≤
      |psi (summary m1) - T m1| + |psi (summary m2) - T m2| := by
    rw [← hsummary]
    calc
      |T m1 - T m2| ≤ |T m1 - psi (summary m1)| +
          |psi (summary m1) - T m2| := abs_sub_le _ _ _
      _ = |psi (summary m1) - T m1| +
          |psi (summary m1) - T m2| := by rw [abs_sub_comm (T m1)]
  have hleft : |psi (summary m1) - T m1| ≤
      max |psi (summary m1) - T m1| |psi (summary m2) - T m2| :=
    le_max_left _ _
  have hright : |psi (summary m2) - T m2| ≤
      max |psi (summary m1) - T m1| |psi (summary m2) - T m2| :=
    le_max_right _ _
  linarith

@[ext] structure BoolPairwiseSummary where
  firstFalse : ℝ
  firstTrue : ℝ
  secondFalse : ℝ
  secondTrue : ℝ

noncomputable def finitePairwiseSummary
    (F : Bool → Bool → ℝ) : BoolPairwiseSummary where
  firstFalse := responseFirst F false
  firstTrue := responseFirst F true
  secondFalse := responseSecond F false
  secondTrue := responseSecond F true

theorem existing_worlds_same_finite_pairwise_summary :
    finitePairwiseSummary zeroWorld = finitePairwiseSummary interactionWorld := by
  ext <;>
    norm_num [finitePairwiseSummary, responseFirst, responseSecond,
      zeroWorld, interactionWorld]

theorem E6_existing_same_response_error_floor
    (psi : BoolPairwiseSummary → ℝ) :
    2 ≤ max
      |psi (finitePairwiseSummary zeroWorld) - interactionQuery zeroWorld|
      |psi (finitePairwiseSummary interactionWorld) -
        interactionQuery interactionWorld| := by
  have h := E5_response_only_minimax_lower_bound finitePairwiseSummary
    interactionQuery psi zeroWorld interactionWorld
    existing_worlds_same_finite_pairwise_summary
  norm_num [interactionQuery, zeroWorld, interactionWorld] at h ⊢
  exact h

end CIGAMF.V7.QuerySufficiencyQuantitative
