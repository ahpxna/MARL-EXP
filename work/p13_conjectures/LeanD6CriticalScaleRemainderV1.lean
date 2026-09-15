import «LeanD6LocalCurvatureLimitV1»

/-! A nonvanishing curvature coefficient does not imply a nonvanishing
matching-risk remainder on the critical scale. At q^3*epsilon^2<=a^2,
the full quadratic term, normalized by the target q^-2, is O(a^2/q). -/
namespace CIGAMF.P13.D6CriticalScaleRemainder
open CIGAMF.P13.D6LocalCurvatureLimit CIGAMF.P13.D6LocalMatchingDesign
open CIGAMF.P13.D6FrozenQuadraticBound CIGAMF.P13.D6UniformPhaseThreeRemainder
noncomputable section

/-- Full coefficient, including the nonvanishing curvature summand. -/
theorem critical_remainder_bound (q mu eps a : ℝ) (hq : 8 ≤ q)
    (hm : mu ∈ phaseInterval q) (hscale : q^3*eps^2 ≤ a^2) :
    q^2*((remainderConstant q mu+|localCurvature q mu|)*eps^2) ≤ 3*a^2/(2*q) := by
  have hc := (matching_coefficient_theta_one hq hm).2
  have hq0 : 0 < q := by linarith
  have hs : 64/q^2 ≤ 1 := (div_le_one (by positivity : 0 < q^2)).mpr (by nlinarith)
  have hcoef : remainderConstant q mu+|localCurvature q mu| ≤ 3/2 := by linarith
  have hh := mul_le_mul_of_nonneg_right hcoef (show 0 ≤ q^3*eps^2 by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 2*q)).mpr
  nlinarith

/-- An explicit threshold makes the normalized quadratic contribution smaller
than any prescribed positive tolerance, uniformly over phase-III margins. -/
theorem critical_remainder_eventually_small (a tol : ℝ) (htol : 0 < tol) :
    ∃ Q : ℝ, 8 ≤ Q ∧ ∀ q mu eps : ℝ, Q ≤ q → mu ∈ phaseInterval q →
      q^3*eps^2 ≤ a^2 →
      q^2*((remainderConstant q mu+|localCurvature q mu|)*eps^2) ≤ tol := by
  refine ⟨max 8 (3*a^2/(2*tol)),le_max_left _ _,?_⟩
  intro q mu eps hq hm hs
  have h8 : 8 ≤ q := (le_max_left _ _).trans hq
  have hthreshold : 3*a^2/(2*tol) ≤ q := (le_max_right _ _).trans hq
  have hh := (div_le_iff₀ (by positivity : 0 < 2*tol)).mp hthreshold
  apply (critical_remainder_bound q mu eps a h8 hm hs).trans
  apply (div_le_iff₀ (by positivity : 0 < 2*q)).mpr
  nlinarith

#print axioms critical_remainder_bound
#print axioms critical_remainder_eventually_small
end
end CIGAMF.P13.D6CriticalScaleRemainder
