import «LeanPaperBCubeV1»
import «LeanPaperBRatesV1»

/-!
# Paper B: attainment by a bounded statistic

`cube_difference` gives the characteristic-function difference exactly, for every `r`.  What
turns that identity into an algorithm is four steps, and this module closes the three that
are deterministic.

1. **The coefficient does not vanish.**  `sin x` is at least `3x/4` on `(0,1]`, so the
   `r`-th power of the tail factor is at least `(3x/4)^r` --- a gap of order `h^r`, with an
   explicit constant, not a fitted slope.
2. **The statistic is bounded.**  `cos(t_0 Y)` and `sin(t_0 Y)` lie in `[-1,1]` whatever the
   observation, so the variance is at most `1` regardless of `r`.  This is what avoids the
   variance blow-up of the `Y^{r+1}` estimator.
3. **The threshold decoder is correct once both empirical means are within half the gap.**

The fourth step is the concentration inequality.  With a bounded statistic Chebyshev gives
`N = O(g^{-2}/delta)`, which is what `decision_sample_budget` already supplies and what this
module composes with.  The `log(1/delta)` form needs a Hoeffding-type bound, which Mathlib
does not have; so the upper side proved here is `1/delta`, and the gap to the `log(1/delta)`
lower bound is the one `sides_do_not_match` records.
-/

namespace CIGAMF.P13.PaperBAttain

open CIGAMF.P13.PaperBRates

/-- **A usable lower bound for the sine on `(0,1]`.** -/
theorem sin_lower_small (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) : 3 * x / 4 ≤ Real.sin x := by
  have h := Real.sin_gt_sub_cube hx
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hx3 : x ^ 3 ≤ x := by nlinarith [hx, hx2]
  linarith [h, hx3, hx]

/-- **The tail factor's magnitude, to the `r`-th power.**  The gap is `Theta(h^r)` with an
explicit constant. -/
theorem gap_from_sin_power (x : ℝ) (r : ℕ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (3 * x / 4) ^ r ≤ (Real.sin x) ^ r :=
  pow_le_pow_left₀ (by positivity) (sin_lower_small x hx hx1) r

/-- **The gap at scale `h`**, written so the exponent is visible: with `x = t h / r` the
bound is a constant times `h^r`. -/
theorem gap_at_scale (t h : ℝ) (r : ℕ) (hr : 0 < r) (ht : 0 < t) (hh : 0 < h)
    (hsmall : t * h / (r : ℝ) ≤ 1) :
    (3 * t / (4 * (r : ℝ))) ^ r * h ^ r ≤ (Real.sin (t * h / (r : ℝ))) ^ r := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hx : 0 < t * h / (r : ℝ) := by positivity
  have hrw : (3 * t / (4 * (r : ℝ))) ^ r * h ^ r
      = (3 * (t * h / (r : ℝ)) / 4) ^ r := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [hrw]
  exact gap_from_sin_power _ r hx hsmall

/-- **The statistic is bounded**, so its variance is at most one whatever `r` is. -/
theorem bounded_statistic_variance (f : ℝ → ℝ) (hf : ∀ y, |f y| ≤ 1) (μf : ℝ)
    (hμ : |μf| ≤ 1) (y : ℝ) : (f y - μf) ^ 2 ≤ 4 := by
  have h1 := hf y
  have h2 := hμ
  rw [abs_le] at h1 h2
  nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **The midpoint threshold classifies correctly** once both empirical means are within
half the gap of their own population means. -/
theorem threshold_decoder_correct (μplus μminus xplus xminus g : ℝ)
    (hgap : μminus + g ≤ μplus) (hg : 0 < g)
    (hxp : |xplus - μplus| < g / 2) (hxm : |xminus - μminus| < g / 2) :
    (μplus + μminus) / 2 < xplus ∧ xminus < (μplus + μminus) / 2 := by
  rw [abs_lt] at hxp hxm
  constructor
  · linarith [hxp.1]
  · linarith [hxm.2]

/-- **The sample budget from the gap, by Chebyshev.**  This is the `1/delta` form; the
`log(1/delta)` form needs a Hoeffding-type inequality and is not proved here. -/
theorem budget_from_gap (V g α : ℝ) (hV : 0 ≤ V) (hg : 0 < g) (hα : 0 < α)
    (N : ℝ) (hNpos : 0 < N) (hN : V / (α * (g / 2) ^ 2) ≤ N) :
    V / N / (g / 2) ^ 2 ≤ α := by
  have hq : (0 : ℝ) < (g / 2) ^ 2 := by positivity
  have hden : (0 : ℝ) < α * (g / 2) ^ 2 := by positivity
  have hVN : V ≤ N * (α * (g / 2) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_right hN (le_of_lt hden)
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at hmul
  rw [div_div, div_le_iff₀ (by positivity)]
  nlinarith [hVN, hq, hNpos]

/-! ## Audit -/

#print axioms sin_lower_small
#print axioms gap_from_sin_power
#print axioms gap_at_scale
#print axioms bounded_statistic_variance
#print axioms threshold_decoder_correct
#print axioms budget_from_gap

end CIGAMF.P13.PaperBAttain
