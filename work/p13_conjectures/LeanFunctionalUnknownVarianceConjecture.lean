import Mathlib
import «LeanFunctionalCovarianceDesignV1»

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
  have hOneMinus : 0 < 1 - rho := by linarith [hRho.2]
  have hOnePlus : 0 ≤ 1 + rho := by linarith [hRho.1]
  have hLower : (1 - rho) ^ 2 * varianceObjective c sigma nHat ≤
      varianceObjective c sigmaHat nHat := by
    unfold varianceObjective
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hci : 0 ≤ c i := hC i
    have hsi : 0 ≤ sigma i := hSigma i
    have hshi : 0 ≤ sigmaHat i := by
      exact le_trans (mul_nonneg (le_of_lt hOneMinus) hsi) (hApprox i).1
    have hmul : (1 - rho) * (c i * sigma i) ≤ c i * sigmaHat i := by
      nlinarith [(hApprox i).1]
    have hsq : ((1 - rho) * (c i * sigma i)) ^ 2 ≤
        (c i * sigmaHat i) ^ 2 := by
      exact (sq_le_sq₀
        (mul_nonneg (le_of_lt hOneMinus) (mul_nonneg hci hsi))
        (mul_nonneg hci hshi)).2 hmul
    have hn := hNhat i
    calc
      (1 - rho) ^ 2 * ((c i * sigma i) ^ 2 / nHat i) =
          (((1 - rho) * (c i * sigma i)) ^ 2) / nHat i := by ring
      _ ≤ (c i * sigmaHat i) ^ 2 / nHat i :=
        div_le_div_of_nonneg_right hsq (le_of_lt hn)
  have hUpper : varianceObjective c sigmaHat nStar ≤
      (1 + rho) ^ 2 * varianceObjective c sigma nStar := by
    unfold varianceObjective
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hci : 0 ≤ c i := hC i
    have hsi : 0 ≤ sigma i := hSigma i
    have hshi : 0 ≤ sigmaHat i := by
      exact le_trans (mul_nonneg (le_of_lt hOneMinus) hsi) (hApprox i).1
    have hmul : c i * sigmaHat i ≤ (1 + rho) * (c i * sigma i) := by
      nlinarith [(hApprox i).2]
    have hsq : (c i * sigmaHat i) ^ 2 ≤
        ((1 + rho) * (c i * sigma i)) ^ 2 := by
      exact (sq_le_sq₀ (mul_nonneg hci hshi)
        (mul_nonneg hOnePlus (mul_nonneg hci hsi))).2 hmul
    have hn := hNstar i
    calc
      (c i * sigmaHat i) ^ 2 / nStar i ≤
          (((1 + rho) * (c i * sigma i)) ^ 2) / nStar i :=
        div_le_div_of_nonneg_right hsq (le_of_lt hn)
      _ = (1 + rho) ^ 2 * ((c i * sigma i) ^ 2 / nStar i) := by ring
  have hSandwich : (1 - rho) ^ 2 * varianceObjective c sigma nHat ≤
      (1 + rho) ^ 2 * varianceObjective c sigma nStar :=
    le_trans hLower (le_trans hPluginOptimal hUpper)
  have hden : (1 - rho) ^ 2 > 0 := sq_pos_of_pos hOneMinus
  calc
    varianceObjective c sigma nHat ≤
        ((1 + rho) ^ 2 / (1 - rho) ^ 2) *
          varianceObjective c sigma nStar := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hSandwich)
    _ = (((1 + rho) / (1 - rho)) ^ 2) *
          varianceObjective c sigma nStar := by
      field_simp
      <;> ring

theorem D_plugin_relative_robustness
    (w sigma sigmaHat nHat nStar : ι → ℝ) (rho : ℝ)
    (hRho : 0 ≤ rho ∧ rho < 1)
    (hSigma : ∀ i, 0 ≤ sigma i)
    (hNhat : ∀ i, 0 < nHat i) (hNstar : ∀ i, 0 < nStar i)
    (hApprox : ∀ i,
      (1 - rho) * sigma i ≤ sigmaHat i ∧
      sigmaHat i ≤ (1 + rho) * sigma i)
    (hPluginOptimal : varianceObjective (fun i => |w i|) sigmaHat nHat ≤
      varianceObjective (fun i => |w i|) sigmaHat nStar) :
    varianceObjective (fun i => |w i|) sigma nHat ≤
      (((1 + rho) / (1 - rho)) ^ 2) *
        varianceObjective (fun i => |w i|) sigma nStar := by
  exact variance_plugin_relative_robustness (fun i => |w i|) sigma sigmaHat
    nHat nStar rho hRho (fun i => abs_nonneg _) hSigma hNhat hNstar
    hApprox hPluginOptimal

theorem stable_extrema_C_plugin_relative_robustness
    {n : ℕ} (aPlus aMinus : Fin n)
    (sigma sigmaHat nHat nStar : Fin n → ℝ) (rho : ℝ)
    (hRho : 0 ≤ rho ∧ rho < 1)
    (hSigma : ∀ i, 0 ≤ sigma i)
    (hNhat : ∀ i, 0 < nHat i) (hNstar : ∀ i, 0 < nStar i)
    (hApprox : ∀ i,
      (1 - rho) * sigma i ≤ sigmaHat i ∧
      sigmaHat i ≤ (1 + rho) * sigma i)
    (hPluginOptimal :
      varianceObjective
        (fun i => |CIGAMF.V7.FunctionalCovarianceDesign.unitContrast aPlus aMinus i|)
        sigmaHat nHat ≤
      varianceObjective
        (fun i => |CIGAMF.V7.FunctionalCovarianceDesign.unitContrast aPlus aMinus i|)
        sigmaHat nStar) :
    varianceObjective
        (fun i => |CIGAMF.V7.FunctionalCovarianceDesign.unitContrast aPlus aMinus i|)
        sigma nHat ≤
      (((1 + rho) / (1 - rho)) ^ 2) *
        varianceObjective
          (fun i => |CIGAMF.V7.FunctionalCovarianceDesign.unitContrast aPlus aMinus i|)
          sigma nStar := by
  exact variance_plugin_relative_robustness
    (fun i => |CIGAMF.V7.FunctionalCovarianceDesign.unitContrast aPlus aMinus i|)
    sigma sigmaHat nHat nStar rho hRho (fun i => abs_nonneg _)
    hSigma hNhat hNstar hApprox hPluginOptimal

end CIGAMF.P13.UnknownVariance
