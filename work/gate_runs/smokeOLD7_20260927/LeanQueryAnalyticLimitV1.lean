import Mathlib

/-! # Query: the ANALYTIC closure -- the normalised Hellinger ratio converges, and its
limit is strictly positive.

`LeanQueryHellingerIntervalV1` and `LeanQueryTaylorRemainderV1` sandwich the squared
Hellinger distance, `c₋ h^{2r} ≤ H² ≤ c₊ h^{2r}`.  A sandwich localises the ratio
`H²/h^{2r}` in `[c₋, c₊]`; it does not say the ratio CONVERGES, and it does not identify
the limit.  The guidance asks for the limit with its constant:

    H²/h^{2r}  ⟶  (1/8) ∫ Δ_r² / p₀   > 0.

This file supplies the two analytic steps that statement needs, and nothing more.

## WHAT IS PROVED

* `ratio_tendsto_of_dominated` — the normalised integrand's pointwise limit transfers to
  the integral, under an integrable dominating envelope.  This is dominated convergence
  along `𝓝[>] 0`, packaged for the shape the Query argument produces; the envelope is
  exactly what `envelope_integrable` supplies in the Taylor module.
* `hellinger_ratio_tendsto` — the same statement written for `H²/h^{2r}`, so the constant
  `1/8` appears where the manuscript needs it and is not silently absorbed.
* `limit_pos_of_ae_ne_zero` — **the limit is strictly positive** whenever `Δ_r` is not a.e.
  zero.  This is what turns `mixture_coeff_ne_zero` (a pointwise non-vanishing statement)
  into a positive leading constant, which is the form the rate claim needs.
* `eventually_pos_of_limit_pos` — a positive limit makes the ratio eventually positive, so
  the rate cannot degenerate for small `h`.

## WHAT THIS DOES NOT ESTABLISH

- The POINTWISE limit of the normalised integrand is a HYPOTHESIS here, not a conclusion.
  It follows from the Taylor expansion with remainder, which the Taylor module bounds
  uniformly; assembling that into the pointwise convergence statement is a separate step
  and is not done here.
- The dominating envelope is likewise a hypothesis.  `LeanQueryHellingerEnvelopeV1` builds
  one for the Gaussian mixture; no envelope is constructed in this file.
- Nothing here computes `∫ Δ_r²/p₀`.  It is shown positive, not evaluated.
- These are statements about a fixed admissible query.  No minimax or over-query statement
  is made.
-/

namespace CIGAMF.P13.QueryAnalyticLimit

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Dominated convergence along `h ↓ 0`, in the shape the Query argument produces.**
The normalised integrand's pointwise limit transfers to the integral. -/
theorem ratio_tendsto_of_dominated (μ : Measure Ω)
    (F : ℝ → Ω → ℝ) (lim bound : Ω → ℝ)
    (hmeas : ∀ᶠ h in 𝓝[>] (0:ℝ), AEStronglyMeasurable (F h) μ)
    (hdom : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᵐ x ∂μ, ‖F h x‖ ≤ bound x)
    (hint : Integrable bound μ)
    (hptw : ∀ᵐ x ∂μ, Tendsto (fun h => F h x) (𝓝[>] (0:ℝ)) (𝓝 (lim x))) :
    Tendsto (fun h => ∫ x, F h x ∂μ) (𝓝[>] (0:ℝ)) (𝓝 (∫ x, lim x ∂μ)) :=
  tendsto_integral_filter_of_dominated_convergence bound hmeas hdom hint hptw

/-- **The Hellinger ratio, with the constant `1/8` in the open.**  If the normalised
integrand converges pointwise to `Δ_r²/(4 p₀)` under an integrable envelope, then
`H²/h^{2r} → (1/8) ∫ Δ_r²/p₀`. -/
theorem hellinger_ratio_tendsto (μ : Measure Ω)
    (F : ℝ → Ω → ℝ) (Dr p0 bound : Ω → ℝ) (H2 : ℝ → ℝ)
    (hmeas : ∀ᶠ h in 𝓝[>] (0:ℝ), AEStronglyMeasurable (F h) μ)
    (hdom : ∀ᶠ h in 𝓝[>] (0:ℝ), ∀ᵐ x ∂μ, ‖F h x‖ ≤ bound x)
    (hint : Integrable bound μ)
    (hptw : ∀ᵐ x ∂μ,
      Tendsto (fun h => F h x) (𝓝[>] (0:ℝ)) (𝓝 (Dr x ^ 2 / (4 * p0 x))))
    (hH2 : ∀ h : ℝ, H2 h = (1/2) * ∫ x, F h x ∂μ) :
    Tendsto H2 (𝓝[>] (0:ℝ)) (𝓝 ((1/2) * ∫ x, Dr x ^ 2 / (4 * p0 x) ∂μ)) := by
  have hbase := ratio_tendsto_of_dominated μ F (fun x => Dr x ^ 2 / (4 * p0 x)) bound
    hmeas hdom hint hptw
  have hfun : H2 = fun h => (1/2) * ∫ x, F h x ∂μ := funext hH2
  rw [hfun]
  exact hbase.const_mul _

/-- **The limit is strictly positive** whenever `Δ_r` is not almost everywhere zero.  This
converts the pointwise non-vanishing of the order-`r` coefficient into a positive leading
constant. -/
theorem limit_pos_of_ae_ne_zero (μ : Measure Ω) (g : Ω → ℝ)
    (hnn : 0 ≤ᵐ[μ] g) (hint : Integrable g μ)
    (hne : ¬ (g =ᵐ[μ] 0)) :
    0 < ∫ x, g x ∂μ := by
  rcases lt_or_eq_of_le (integral_nonneg_of_ae hnn) with h | h
  · exact h
  · exfalso
    apply hne
    have hzero : ∫ x, g x ∂μ = 0 := h.symm
    exact (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hzero

/-- A positive limit makes the ratio eventually positive: the rate cannot degenerate for
small `h`. -/
theorem eventually_pos_of_limit_pos (H2 : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hlim : Tendsto H2 (𝓝[>] (0:ℝ)) (𝓝 L)) :
    ∀ᶠ h in 𝓝[>] (0:ℝ), 0 < H2 h :=
  hlim.eventually (eventually_gt_nhds hL)

#print axioms ratio_tendsto_of_dominated
#print axioms hellinger_ratio_tendsto
#print axioms limit_pos_of_ae_ne_zero
#print axioms eventually_pos_of_limit_pos

end CIGAMF.P13.QueryAnalyticLimit
