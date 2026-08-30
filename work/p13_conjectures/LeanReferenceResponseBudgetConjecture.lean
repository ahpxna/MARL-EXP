import Mathlib

/-! QUARANTINED / OPEN. MASTER↔FUNCTIONAL budget-splitting calculus. -/
namespace CIGAMF.P13.ReferenceResponseBudget

noncomputable def twoSourceRadius (A B N x : ℝ) : ℝ :=
  A / Real.sqrt x + B / Real.sqrt (N - x)

noncomputable def optimalResponseBudget (A B N : ℝ) : ℝ :=
  N * (A ^ (2/3 : ℝ)) / (A ^ (2/3 : ℝ) + B ^ (2/3 : ℝ))

/-- Continuous relaxation target: response/reference errors with `1/sqrt(n)`
    envelopes imply a 2/3-power optimal allocation law. -/
theorem two_source_budget_split_conjecture
    (A B N x : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hN : 0 < N)
    (hx0 : 0 < x) (hxN : x < N) :
    twoSourceRadius A B N (optimalResponseBudget A B N) ≤
      twoSourceRadius A B N x := by
  sorry

/-- Closed-form minimum corresponding to the same continuous relaxation. -/
theorem two_source_budget_minimum_conjecture
    (A B N : ℝ) (hA : 0 < A) (hB : 0 < B) (hN : 0 < N) :
    twoSourceRadius A B N (optimalResponseBudget A B N) =
      (A ^ (2/3 : ℝ) + B ^ (2/3 : ℝ)) ^ (3/2 : ℝ) / Real.sqrt N := by
  sorry

end CIGAMF.P13.ReferenceResponseBudget
