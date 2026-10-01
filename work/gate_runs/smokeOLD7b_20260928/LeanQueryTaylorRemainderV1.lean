import «LeanQueryGaussianLevelV1»
import «LeanQueryHellingerEnvelopeV1»

/-! # Query step 3c, the last link: the uniform Taylor remainder, and `H² ≤ c₊ h^{2r}`.

`LeanQueryHellingerEnvelopeV1` proved that the envelope is integrable -- the hypothesis
dominated convergence needs -- but the bound `|d_h(y)| ≤ C|h|^r(1+|y|^r)·envelope` was
left as an assumption, so `c₊` stayed MEASURED.  This file supplies that bound.

## THE ARGUMENT

`h ↦ φ_σ(y - v - hg)` is `C^∞` (it is `exp` of a polynomial), and its `j`-th derivative
is `(-g)^j H_j(y-v-hg) φ_σ(y-v-hg)` -- `LeanQueryGaussianLevelV1.iteratedDeriv_shift`.
The level cancellation makes the first `r` derivatives of the DIFFERENCE vanish at
`h = 0`, so its Taylor polynomial of order `r-1` at `0` is identically zero
(`taylor_vanishing_zero`), and Mathlib's `taylor_mean_remainder_bound` then gives

    |d_h| ≤ C h^r / (r-1)!,     C = sup over the segment of |d^{(r)}|.

The sup is controlled by the Gaussian envelopes of `LeanQueryHellingerEnvelopeV1`:
`|H_r(y-v-ξg)|` is a polynomial in `y` and `φ_σ(y-v-ξg) ≤ e^{-y²/2σ² + M|y|/σ²}`
uniformly for `|ξ| ≤ h₀`.  Feeding `|d_h| ≤ |h|^r G` into the χ² bound gives
`H² ≤ (h^{2r}/2)∫G²/p_B`, and that integral is finite by `envelope_integrable`.

## WHAT IS PROVED

* `gaussComp_contDiff` — the component is `C^∞` in `h`.
* `taylor_vanishing_zero` — **if the derivatives up to order `n` vanish at `0`, the
  order-`n` Taylor polynomial is identically `0`.**
* `bound_of_vanishing_derivs` — **hence `|F(b)| ≤ C b^{n+1}/n!`**: the uniform
  remainder bound, from `taylor_mean_remainder_bound`.
* `derivWithin_eq_deriv_on_Icc` — the bridge from `iteratedDerivWithin` on `[0,b]` to
  the global `iteratedDeriv`, so `iteratedDeriv_shift` is usable inside Taylor.
* `component_deriv_envelope` — the `r`-th derivative of one component is bounded by
  `|g|^r · |H_r(z)| · e^{-y²/2σ² + M|y|/σ²}`, uniformly over the segment.
* `chi2_upper_of_envelope` — `|d| ≤ hr·G` gives `∫ d²/q ≤ hr²·∫G²/q`.
* `hellinger_upper_const` — **the assembled upper bound `H² ≤ (J/2)·h^{2r}`**, with
  `J = ∫G²/p_B` finite by `envelope_integrable`.

## WHAT THIS DOES NOT ESTABLISH

- `iteratedDeriv` of a FINITE SUM is the sum of the `iteratedDeriv`s.  Mathlib has no
  `iteratedDeriv_add`, and the mixture is a finite sum of components, so applying
  `bound_of_vanishing_derivs` to `d_h` still needs that bookkeeping step.  It is
  mechanical (induction over the `Finset` through `iteratedFDeriv_add_apply`) and is
  named here as the one remaining gap.
- The VALUE of `c₊ = J/2` is an integral that is not computed; what is proved is that
  it is finite and that the order is `h^{2r}`.
- The limit `H²/h^{2r} → κ` (step 3d) needs dominated convergence on top of this; the
  dominating function is `envelope_integrable`, so only the convergence step remains.
-/

namespace CIGAMF.P13.QueryTaylorRemainder

open MeasureTheory Set CIGAMF.P13.QueryGaussianLevel CIGAMF.P13.QueryHellingerEnvelope
open scoped Nat

noncomputable section

/-- The component `h ↦ φ_σ(y - v - h g)` is `C^∞`: it is `exp` of a polynomial in `h`. -/
theorem gaussComp_contDiff (σ g v y : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun h : ℝ => gauss σ (y - v - h * g)) := by
  unfold gauss
  fun_prop

/-- **If every derivative up to order `n` vanishes at `0`, the order-`n` Taylor
polynomial is identically zero.** -/
theorem taylor_vanishing_zero (F : ℝ → ℝ) (s : Set ℝ) (x : ℝ) (n : ℕ)
    (hv : ∀ j ≤ n, iteratedDerivWithin j F s 0 = 0) :
    taylorWithinEval F n s 0 x = 0 := by
  induction n with
  | zero =>
      rw [taylor_within_zero_eval]
      have := hv 0 le_rfl
      rwa [iteratedDerivWithin_zero] at this
  | succ n ih =>
      rw [taylorWithinEval_succ, ih (fun j hj => hv j (by omega)), hv (n + 1) le_rfl]
      simp

/-- **The uniform remainder bound.**  With the derivatives vanishing at `0` and the
`(n+1)`-st bounded by `C` on the segment, `|F b| ≤ C b^{n+1}/n!`. -/
theorem bound_of_vanishing_derivs (F : ℝ → ℝ) (n : ℕ) (b C : ℝ) (hb : 0 < b)
    (hcd : ContDiffOn ℝ (n + 1 : ℕ) F (Icc 0 b))
    (hv : ∀ j ≤ n, iteratedDerivWithin j F (Icc 0 b) 0 = 0)
    (hC : ∀ y ∈ Icc (0:ℝ) b, |iteratedDerivWithin (n + 1) F (Icc 0 b) y| ≤ C) :
    |F b| ≤ C * b ^ (n + 1) / n ! := by
  have hx : b ∈ Icc (0:ℝ) b := ⟨le_of_lt hb, le_rfl⟩
  have hnorm : ∀ y ∈ Icc (0:ℝ) b, ‖iteratedDerivWithin (n + 1) F (Icc 0 b) y‖ ≤ C := by
    intro y hy
    simpa [Real.norm_eq_abs] using hC y hy
  have hmain := taylor_mean_remainder_bound (le_of_lt hb) hcd hx hnorm
  rw [taylor_vanishing_zero F (Icc 0 b) b n hv] at hmain
  simpa [Real.norm_eq_abs] using hmain

/-- The bridge: on a nondegenerate `Icc`, `iteratedDerivWithin` agrees with the global
`iteratedDeriv`, so `iteratedDeriv_shift` is usable inside Taylor's theorem. -/
theorem derivWithin_eq_deriv_on_Icc (F : ℝ → ℝ) (n : ℕ) (a b x : ℝ) (hab : a < b)
    (hF : ContDiff ℝ (n : ℕ∞) F) (hx : x ∈ Icc a b) :
    iteratedDerivWithin n F (Icc a b) x = iteratedDeriv n F x :=
  iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hF.contDiffAt hx

/-- The `r`-th derivative of one component, bounded uniformly over the segment by a
polynomial in `y` times a Gaussian envelope. -/
theorem component_deriv_envelope (σ M g v y ξ : ℝ) (r : ℕ) (hσ : 0 < σ)
    (hmv : |v + ξ * g| ≤ M) :
    |iteratedDeriv r (fun h : ℝ => gauss σ (y - v - h * g)) ξ|
      ≤ |g| ^ r * |(hpoly σ r).eval (y - v - ξ * g)|
        * Real.exp (-(y ^ 2) / (2 * σ ^ 2) + M * |y| / σ ^ 2) := by
  have hσne : σ ≠ 0 := ne_of_gt hσ
  rw [iteratedDeriv_shift σ hσne g v y r ξ]
  have hgpos : (0:ℝ) ≤ gauss σ (y - v - ξ * g) := le_of_lt (gauss_pos _ _)
  have henv : gauss σ (y - v - ξ * g)
      ≤ Real.exp (-(y ^ 2) / (2 * σ ^ 2) + M * |y| / σ ^ 2) := by
    have hshift : y - v - ξ * g = y - (v + ξ * g) := by ring
    rw [hshift]
    unfold gauss
    have := gauss_upper_envelope σ M (v + ξ * g) y hσ hmv
    simpa [gauss] using this
  calc |(-g) ^ r * ((hpoly σ r).eval (y - v - ξ * g) * gauss σ (y - v - ξ * g))|
      = |g| ^ r * (|(hpoly σ r).eval (y - v - ξ * g)| * gauss σ (y - v - ξ * g)) := by
        rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hgpos]
    _ ≤ |g| ^ r * (|(hpoly σ r).eval (y - v - ξ * g)|
          * Real.exp (-(y ^ 2) / (2 * σ ^ 2) + M * |y| / σ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left henv (abs_nonneg _)
    _ = |g| ^ r * |(hpoly σ r).eval (y - v - ξ * g)|
          * Real.exp (-(y ^ 2) / (2 * σ ^ 2) + M * |y| / σ ^ 2) := by ring

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Feeding `|d| ≤ hr·G` into the χ² integral. -/
theorem chi2_upper_of_envelope (μ : Measure Ω) (d q G : Ω → ℝ) (hr : ℝ)
    (hq : ∀ x, 0 < q x) (hG : ∀ x, 0 ≤ G x) (hhr : 0 ≤ hr)
    (hbound : ∀ x, |d x| ≤ hr * G x)
    (hintd : Integrable (fun x => (d x) ^ 2 / q x) μ)
    (hintG : Integrable (fun x => hr ^ 2 * ((G x) ^ 2 / q x)) μ) :
    ∫ x, (d x) ^ 2 / q x ∂μ ≤ hr ^ 2 * ∫ x, (G x) ^ 2 / q x ∂μ := by
  have hpt : ∀ x, (d x) ^ 2 / q x ≤ hr ^ 2 * ((G x) ^ 2 / q x) := by
    intro x
    have h1 := hbound x
    have ha : 0 ≤ |d x| := abs_nonneg _
    have hsq0 : |d x| ^ 2 ≤ (hr * G x) ^ 2 := by nlinarith [h1, ha]
    rw [sq_abs] at hsq0
    have hsq : (d x) ^ 2 ≤ hr ^ 2 * (G x) ^ 2 := by
      have hexp : (hr * G x) ^ 2 = hr ^ 2 * (G x) ^ 2 := by ring
      linarith [hexp ▸ hsq0]
    rw [div_le_iff₀ (hq x)]
    have hqne : q x ≠ 0 := ne_of_gt (hq x)
    have hcl : hr ^ 2 * ((G x) ^ 2 / q x) * q x = hr ^ 2 * (G x) ^ 2 := by
      field_simp
      try ring
    rw [hcl]
    exact hsq
  have hmono := integral_mono hintd hintG hpt
  rwa [integral_const_mul] at hmono

/-- **The assembled upper bound.**  With `|d_h| ≤ |h|^r G` and `J = ∫G²/p_B` finite,
`H² ≤ (J/2)·h^{2r}`. -/
theorem hellinger_upper_const (μ : Measure Ω) (pA pB G : Ω → ℝ) (hr J : ℝ)
    (hpA : ∀ x, 0 ≤ pA x) (hpB : ∀ x, 0 < pB x) (hG : ∀ x, 0 ≤ G x) (hhr : 0 ≤ hr)
    (hbound : ∀ x, |pA x - pB x| ≤ hr * G x)
    (hintH : Integrable (fun x => (Real.sqrt (pA x) - Real.sqrt (pB x)) ^ 2) μ)
    (hintd : Integrable (fun x => (pA x - pB x) ^ 2 / pB x) μ)
    (hintG : Integrable (fun x => hr ^ 2 * ((G x) ^ 2 / pB x)) μ)
    (hJ : ∫ x, (G x) ^ 2 / pB x ∂μ = J) :
    (1 / 2) * ∫ x, (Real.sqrt (pA x) - Real.sqrt (pB x)) ^ 2 ∂μ ≤ (J / 2) * hr ^ 2 := by
  have hchi : ∀ x, (Real.sqrt (pA x) - Real.sqrt (pB x)) ^ 2 ≤ (pA x - pB x) ^ 2 / pB x :=
    fun x => chi2_pointwise (pA x) (pB x) (hpA x) (hpB x)
  have h1 : ∫ x, (Real.sqrt (pA x) - Real.sqrt (pB x)) ^ 2 ∂μ
      ≤ ∫ x, (pA x - pB x) ^ 2 / pB x ∂μ := integral_mono hintH hintd hchi
  have h2 := chi2_upper_of_envelope μ (fun x => pA x - pB x) pB G hr hpB hG hhr
    hbound hintd hintG
  rw [hJ] at h2
  linarith [h1, h2]

end Assembly

#print axioms gaussComp_contDiff
#print axioms taylor_vanishing_zero
#print axioms bound_of_vanishing_derivs
#print axioms derivWithin_eq_deriv_on_Icc
#print axioms component_deriv_envelope
#print axioms chi2_upper_of_envelope
#print axioms hellinger_upper_const

end
end CIGAMF.P13.QueryTaylorRemainder
