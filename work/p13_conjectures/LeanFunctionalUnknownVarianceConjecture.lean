import Mathlib

/-! QUARANTINED / OPEN. Deterministic robustness target for learned variances. -/
namespace CIGAMF.P13.UnknownVariance
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def varianceObjective
    (c sigma n : ι → ℝ) : ℝ :=
  ∑ i, (c i * sigma i) ^ 2 / n i

/-- If every learned standard deviation is relatively accurate and `nHat`
    minimizes the plug-in objective against `nStar`, the true variance cost
    should degrade by at most the squared relative-error condition number. -/
theorem variance_plugin_relative_robustness
    (c sigma sigmaHat nHat nStar : ι → ℝ) (rho : ℝ)
    (hRho : 0 ≤ rho ∧ rho < 1)
    (hC : ∀ i, 0 ≤ c i)
    (hSigma : ∀ i, 0 ≤ sigma i)
    (hNhat : ∀ i, 0 < nHat i)
    (hNstar : ∀ i, 0 < nStar i)
    (hApprox : ∀ i,
      (1 - rho) * sigma i ≤ sigmaHat i ∧
      sigmaHat i ≤ (1 + rho) * sigma i)
    (hPluginOptimal :
      varianceObjective c sigmaHat nHat ≤ varianceObjective c sigmaHat nStar) :
    varianceObjective c sigma nHat ≤
      (((1 + rho) / (1 - rho)) ^ 2) * varianceObjective c sigma nStar := by
  sorry

/-- Selection error is a separate term: even perfect variance estimation does
    not help if the currently identified extrema are wrong.  This theorem is
    intentionally left open until the exact stable-extrema premises are chosen. -/
theorem stable_extrema_plus_variance_error_conjecture : True := by
  sorry

end CIGAMF.P13.UnknownVariance
