import Mathlib
import «LeanFunctionalRankingV6»

/-! QUARANTINED / OPEN.

This is the bridge from a certified response/reference acquisition radius to
the already verified Functional Top-K margin theorem.  It does not prove a
concentration inequality or the still-open 2/3-power allocation optimum.
-/
namespace CIGAMF.P13.ReferenceResponseTopKBudget

open CIGAMF.V6.FunctionalRanking

noncomputable def optimizedTotalRadius (chi A B N : ℝ) : ℝ :=
  chi + (A ^ (2 / 3 : ℝ) + B ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) / Real.sqrt N

/-- A certified optimized response/reference radius smaller than half of every
    true selected-vs-rejected capacity gap is sufficient for exact Top-K.

    The difficult statistical premise is the simultaneous score-coverage
    statement at the displayed radius.  No concentration inequality is
    invented here. -/
theorem reference_response_budget_implies_strictTopK
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C Chat : ι → ℝ) (S : Finset ι) (k : ℕ)
    (chi A B N : ℝ)
    (hcard : S.card = k)
    (hcoverage : ∀ j,
      |Chat j - C j| ≤ optimizedTotalRadius chi A B N)
    (hbudgetMargin : ∀ j ∈ S, ∀ l ∉ S,
      2 * optimizedTotalRadius chi A B N < C j - C l) :
    StrictTopK Chat S k := by
  exact A9_uniform_topK_margin C Chat S k
    (optimizedTotalRadius chi A B N) hcard hcoverage hbudgetMargin

end CIGAMF.P13.ReferenceResponseTopKBudget
