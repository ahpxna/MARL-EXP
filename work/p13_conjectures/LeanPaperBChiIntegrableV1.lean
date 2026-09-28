import «LeanPaperBAssemblyV1»

/-!
# Paper B: the chi-square integrands are integrable (task T9)

`hellinger_rate_bound`, `chi2_uniform` and `chi2_worlds_le` bound Bochner integrals
`∫ (P - Q)^2 / ℓ` without proving the integrand integrable. By Mathlib's convention a
non-integrable integrand has integral `0`, so on their own those bounds could hold vacuously.
This module closes that gap.

* `rate_integrand_integrable`: under the hypotheses of `hellinger_rate_bound`, plus
  measurability of the integrand, `(Δ y)^2 / ℓ y` is integrable. It is dominated by
  `(∏ |h a_i|)^2 · envUp^2 / envLo`, which is integrable (`envRatio_integrable`).
* `worldP_continuous`, `worldQ_continuous`: the two worlds are continuous.
* `chi2_worlds_integrable`: `(P - Q)^2 / Q` is integrable, for every probe in the box.
* `chi2_uniform_integrable`: so is the envelope form `(P - Q)^2 / envLo` of `chi2_uniform`.
* `chi2_worlds_le'`: **the chi-square statement with its integrability**: the integrand is
  integrable, the integrand of `klConst` is integrable (so `klConst` is a genuine finite
  integral, and it is non-negative), and `∫ (P - Q)^2 / Q ≤ h^{2r} r^{-2r} klConst`.
-/

namespace CIGAMF.P13.PaperBChiIntegrable

open MeasureTheory Finset
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBKL CIGAMF.P13.PaperBWorlds
open CIGAMF.P13.PaperBAssembly

variable {r : ℕ}

/-- **The integrand of `hellinger_rate_bound` is integrable**, given its measurability. -/
theorem rate_integrand_integrable (σ R h : ℝ) (r : ℕ) (hσ : 0 < σ) (hR : 0 ≤ R)
    (a : Fin r → ℝ) (Δ ℓ : ℝ → ℝ)
    (hΔ : ∀ y, |Δ y| ≤ (∏ i, |h * a i|) * envUp σ R r y)
    (hℓ : ∀ y, envLo σ R y ≤ ℓ y)
    (hmeas : AEStronglyMeasurable (fun y => (Δ y) ^ 2 / ℓ y) volume) :
    Integrable (fun y => (Δ y) ^ 2 / ℓ y) := by
  set c : ℝ := (∏ i, |h * a i|) ^ 2 with hc
  have hP : (0 : ℝ) ≤ ∏ i, |h * a i| := Finset.prod_nonneg fun i _ => abs_nonneg _
  have hg : Integrable (fun y => c * (envUp σ R r y ^ 2 / envLo σ R y)) :=
    (envRatio_integrable σ R hσ hR r).const_mul c
  refine hg.mono' hmeas (Filter.Eventually.of_forall fun y => ?_)
  have hlo := envLo_pos σ R y
  have hlpos : 0 < ℓ y := lt_of_lt_of_le hlo (hℓ y)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hlpos.le)]
  have hE : (0 : ℝ) ≤ envUp σ R r y := envUp_nonneg σ R r y hR
  have hnum : (Δ y) ^ 2 ≤ c * envUp σ R r y ^ 2 := by
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hΔ y) 2
    rw [sq_abs, mul_pow] at h2
    exact h2
  calc (Δ y) ^ 2 / ℓ y ≤ (c * envUp σ R r y ^ 2) / envLo σ R y :=
        div_le_div₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hnum hlo (hℓ y)
    _ = c * (envUp σ R r y ^ 2 / envLo σ R y) := by ring

theorem worldQ_continuous (M : ℝ → ℝ) (hM : Continuous M) (b : Fin r → ℝ) :
    Continuous (worldQ M b) := by
  unfold worldQ
  exact continuous_const.mul
    (continuous_finsetSum _ fun z _ => hM.comp (continuous_id.sub continuous_const))

theorem worldP_continuous (M : ℝ → ℝ) (hM : Continuous M) (b : Fin r → ℝ) :
    Continuous (worldP M b) := by
  unfold worldP
  exact continuous_const.mul (continuous_finsetSum _ fun z _ =>
    continuous_const.mul (hM.comp (continuous_id.sub continuous_const)))

/-- **`(P - Q)^2 / Q` is integrable**, for every probe in the box. -/
theorem chi2_worlds_integrable (σ R h₀ h : ℝ) (r n : ℕ) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh₀ : 0 ≤ h₀) (a : Fin r → ℝ) (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hcs : ∀ j, |cs j| ≤ R) :
    Integrable (fun y => (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / worldQ (mixDens σ n w cs) (fun i => h * a i) y) := by
  have hRh : 0 ≤ R + h₀ := by linarith
  have hfloor : ∀ y, envLo σ (R + h₀) y
      ≤ worldQ (mixDens σ n w cs) (fun i => h * a i) y := fun y =>
    worldQ_floor _ _ _ h₀ hscale
      (fun v y' hv => mixDens_floor σ R h₀ hσ hR hh₀ n w cs hw hw1 hcs v y' hv) y
  have hQpos : ∀ y, 0 < worldQ (mixDens σ n w cs) (fun i => h * a i) y :=
    fun y => lt_of_lt_of_le (envLo_pos σ (R + h₀) y) (hfloor y)
  have hMc := mixDens_continuous σ hσ n w cs
  have hPc := worldP_continuous _ hMc (fun i => h * a i)
  have hQc := worldQ_continuous _ hMc (fun i => h * a i)
  have hcont : Continuous (fun y => (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / worldQ (mixDens σ n w cs) (fun i => h * a i) y) :=
    ((hPc.sub hQc).pow 2).div hQc (fun y => (hQpos y).ne')
  refine rate_integrand_integrable σ (R + h₀) h r hσ hRh a _ _ (fun y => ?_) hfloor
    hcont.aestronglyMeasurable
  rw [worlds_diff]
  exact iterDiff_mixture_envelope σ R h₀ hσ hR hh₀ r n w hw (le_of_eq hw1) cs hcs
    (fun i => h * a i) hscale y

/-- **The envelope form `(P - Q)^2 / envLo` of `chi2_uniform` is integrable.** -/
theorem chi2_uniform_integrable (σ R h₀ h : ℝ) (r n : ℕ) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh₀ : 0 ≤ h₀) (a : Fin r → ℝ) (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hcs : ∀ j, |cs j| ≤ R) :
    Integrable (fun y => (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / envLo σ (R + h₀) y) := by
  have hRh : 0 ≤ R + h₀ := by linarith
  have hMc := mixDens_continuous σ hσ n w cs
  have hPc := worldP_continuous _ hMc (fun i => h * a i)
  have hQc := worldQ_continuous _ hMc (fun i => h * a i)
  have hcont : Continuous (fun y => (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / envLo σ (R + h₀) y) :=
    ((hPc.sub hQc).pow 2).div (envLo_continuous σ (R + h₀))
      (fun y => (envLo_pos σ (R + h₀) y).ne')
  refine rate_integrand_integrable σ (R + h₀) h r hσ hRh a _ _ (fun y => ?_) (fun y => le_rfl)
    hcont.aestronglyMeasurable
  rw [worlds_diff]
  exact iterDiff_mixture_envelope σ R h₀ hσ hR hh₀ r n w hw (le_of_eq hw1) cs hcs
    (fun i => h * a i) hscale y

/-- **T9: the chi-square bound together with its integrability.** The integrand is
integrable, `klConst` is the integral of an integrable non-negative function, and
`∫ (P - Q)^2 / Q ≤ h^{2r} r^{-2r} klConst`. -/
theorem chi2_worlds_le' (σ R h₀ h : ℝ) (r n : ℕ) (hr : 0 < r) (hσ : 0 < σ) (hR : 0 ≤ R)
    (hh₀ : 0 ≤ h₀) (hh : 0 ≤ h) (a : Fin r → ℝ) (ha : ∑ i, |a i| ≤ 1)
    (hscale : ∑ i, |h * a i| ≤ h₀)
    (w cs : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) (hcs : ∀ j, |cs j| ≤ R) :
    Integrable (fun y => (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / worldQ (mixDens σ n w cs) (fun i => h * a i) y)
    ∧ Integrable (fun y => envUp σ (R + h₀) r y ^ 2 / envLo σ (R + h₀) y)
    ∧ 0 ≤ klConst σ R h₀ r
    ∧ ∫ y, (worldP (mixDens σ n w cs) (fun i => h * a i) y
            - worldQ (mixDens σ n w cs) (fun i => h * a i) y) ^ 2
          / worldQ (mixDens σ n w cs) (fun i => h * a i) y
      ≤ h ^ (2 * r) * ((1 / (r : ℝ)) ^ r) ^ 2 * klConst σ R h₀ r := by
  have hRh : 0 ≤ R + h₀ := by linarith
  exact ⟨chi2_worlds_integrable σ R h₀ h r n hσ hR hh₀ a hscale w cs hw hw1 hcs,
    envRatio_integrable σ (R + h₀) hσ hRh r, envRatio_integral_nonneg σ (R + h₀) r,
    chi2_worlds_le σ R h₀ h r n hr hσ hR hh₀ hh a ha hscale w cs hw hw1 hcs⟩

#print axioms rate_integrand_integrable
#print axioms worldQ_continuous
#print axioms worldP_continuous
#print axioms chi2_worlds_integrable
#print axioms chi2_uniform_integrable
#print axioms chi2_worlds_le'

end CIGAMF.P13.PaperBChiIntegrable
