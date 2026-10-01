import «LeanPaperBChangeV1»
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Paper B: the Gaussian policy's own per-step likelihood ratio and divergence

`LeanPaperBChangeV1` proves the transcript bound for an abstract `L` on a filtration,
assuming

* `hdens` -- that `P` restricted to `F t` is `Q` restricted to `F t` with density `L t`, and
* a bound on each `klIncr`.

`PROOFS.md` recorded the blocker as building those two from a Gaussian policy's own kernels.
This module builds them AT ONE STEP, exactly, with no estimate anywhere.

* `gauss_ratio` -- the likelihood ratio between two Gaussian steps of the same variance is
  `exp((mP - mQ)(2y - mP - mQ)/(2v))`, an identity of densities.
* `gauss_step_withDensity` -- hence the one-step change of measure in the very form `hdens`
  asks for: `N(mP, v) = (N(mQ, v)).withDensity (ratio)`.
* `gauss_step_kl` -- the per-step divergence is `(mP - mQ)^2 / (2v)`, computed from
  `integral_id_gaussianReal`, not bounded.
* `gauss_step_kl_le` -- so a policy whose mean shift is at most `delta` at every step has
  every `klIncr` at most `delta^2/(2v)`, which is what `kl_le_horizon` consumes, and the
  horizon bound is `n delta^2/(2v)`.

WHAT REMAINS OF THE CONTINUOUS CASE.  The composition: turning these one-step identities
into `hdens` for the FILTRATION of an `n`-step adaptive transcript needs the kernel
composition and its restriction to the first `t` coordinates.  The finite-alphabet analogue
of exactly that composition is proved and constructive in `LeanPaperBTranscriptV1`
(`change_of_measure`, `expect_Lr_eq_one`), so what is missing is the measure-theoretic
plumbing, not the argument.
-/

namespace CIGAMF.P13.PaperBGaussStep

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

/-- The per-step likelihood ratio of two Gaussian steps of the same variance. -/
noncomputable def gaussRatio (mP mQ : ℝ) (v : ℝ≥0) (y : ℝ) : ℝ :=
  Real.exp ((mP - mQ) * (2 * y - mP - mQ) / (2 * v))

/-- **The ratio is an identity of densities**, not an approximation. -/
theorem gauss_ratio (mP mQ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (y : ℝ) :
    gaussianPDFReal mP v y = gaussRatio mP mQ v y * gaussianPDFReal mQ v y := by
  have hvR : (0 : ℝ) < (v : ℝ) :=
    lt_of_le_of_ne v.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  have hexp : Real.exp (-(y - mP) ^ 2 / (2 * (v : ℝ)))
      = Real.exp ((mP - mQ) * (2 * y - mP - mQ) / (2 * (v : ℝ)))
        * Real.exp (-(y - mQ) ^ 2 / (2 * (v : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  unfold gaussRatio gaussianPDFReal
  rw [hexp]
  ring

theorem gaussRatio_pos (mP mQ : ℝ) (v : ℝ≥0) (y : ℝ) : 0 < gaussRatio mP mQ v y :=
  Real.exp_pos _

/-- **The per-step divergence, computed exactly.**  The log-ratio is affine in `y`, so the
`P`-mean of it is `(mP - mQ)^2/(2v)` by `integral_id_gaussianReal`. -/
theorem gauss_step_kl (mP mQ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    ∫ y, Real.log (gaussRatio mP mQ v y) ∂(gaussianReal mP v)
      = (mP - mQ) ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) :=
    lt_of_le_of_ne v.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  have hlog : ∀ y : ℝ, Real.log (gaussRatio mP mQ v y)
      = ((mP - mQ) / ((v : ℝ))) * y - (mP - mQ) * (mP + mQ) / (2 * v) := by
    intro y
    unfold gaussRatio
    rw [Real.log_exp]
    field_simp
    ring
  have hint : Integrable (fun y : ℝ => y) (gaussianReal mP v) :=
    (memLp_id_gaussianReal (μ := mP) (v := v) 1).integrable (by norm_num)
  have hone : (∫ (_ : ℝ), ((mP - mQ) * (mP + mQ) / (2 * (v : ℝ)))
      ∂(gaussianReal mP v)) = (mP - mQ) * (mP + mQ) / (2 * (v : ℝ)) := by
    simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hlog)]
  rw [integral_sub ((hint.const_mul _)) (integrable_const _)]
  rw [integral_const_mul, integral_id_gaussianReal, hone]
  field_simp
  ring

/-- **The bound `kl_le_horizon` consumes.**  A policy whose per-step mean shift never
exceeds `delta` has every increment at most `delta^2/(2v)`, hence a transcript divergence at
most `n delta^2/(2v)`. -/
theorem gauss_step_kl_le (mP mQ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (δ : ℝ)
    (hshift : |mP - mQ| ≤ δ) :
    ∫ y, Real.log (gaussRatio mP mQ v y) ∂(gaussianReal mP v) ≤ δ ^ 2 / (2 * v) := by
  have hvR : (0 : ℝ) < (v : ℝ) :=
    lt_of_le_of_ne v.coe_nonneg (Ne.symm (NNReal.coe_ne_zero.mpr hv))
  rw [gauss_step_kl mP mQ v hv]
  have hsq : (mP - mQ) ^ 2 ≤ δ ^ 2 := by
    have h := abs_nonneg (mP - mQ)
    nlinarith [sq_abs (mP - mQ), hshift, h]
  have hden : (0 : ℝ) < 2 * (v : ℝ) := by linarith
  have hdiff : 0 ≤ (δ ^ 2 - (mP - mQ) ^ 2) / (2 * (v : ℝ)) :=
    div_nonneg (by linarith) hden.le
  have hsplit : (δ ^ 2 - (mP - mQ) ^ 2) / (2 * (v : ℝ))
      = δ ^ 2 / (2 * (v : ℝ)) - (mP - mQ) ^ 2 / (2 * (v : ℝ)) := by ring
  linarith [hdiff, hsplit]

/-- **The horizon bound, from the per-step one.** -/
theorem gauss_horizon_bound (n : ℕ) (v : ℝ≥0) (δ : ℝ) (hv : v ≠ 0) (hδ : 0 ≤ δ)
    (kl : ℕ → ℝ) (hkl : ∀ t, kl t ≤ δ ^ 2 / (2 * v)) :
    ∑ t ∈ Finset.range n, kl t ≤ (n : ℝ) * (δ ^ 2 / (2 * v)) := by
  have h := Finset.sum_le_sum (fun t (_ : t ∈ Finset.range n) => hkl t)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  exact h

/-! ## Audit -/

#print axioms gauss_ratio
#print axioms gauss_step_kl
#print axioms gauss_step_kl_le
#print axioms gauss_horizon_bound

end CIGAMF.P13.PaperBGaussStep
