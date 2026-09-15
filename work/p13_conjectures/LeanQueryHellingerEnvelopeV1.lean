import Mathlib

/-! # Query step 3c: the Gaussian ENVELOPE, and why the naive small-`h` argument fails.

The upper bound on `H²` cannot be got by saying `(p_{A,h} - p_{B,h})/p_0` is uniformly
small: Gaussian tails make that false for every `h > 0`, however small.  The correct
route is

    H² ≤ (1/2) ∫ d_h² / p_{B,h},

then a LOWER envelope for the mixture `p_{B,h}` (one component already dominates it),
an UPPER envelope for the numerator, and an integrable majorant for the ratio.  This
file proves each of those steps.

## THE ENVELOPES

For `|m| ≤ M`:

    exp(-y²/2σ² - M|y|/σ² - M²/2σ²)  ≤  exp(-(y-m)²/2σ²)  ≤  exp(-y²/2σ² + M|y|/σ²).

So the ratio of an upper to a lower envelope carries `exp(3M|y|/σ²)`, and
`3M|y| ≤ y²/4 + 9M²` turns that into a Gaussian with a smaller rate times a constant.
The remaining polynomial factor `(y²)^r` is handled by `x^n ≤ n^n e^x`, which gives
`(y²)^r ≤ (2r/b)^r e^{(b/2)y²}` -- enough to dominate by `e^{-(b/2)y²}`.

## WHAT IS PROVED

* `chi2_pointwise` — `(√p-√q)² ≤ (p-q)²/q`: Hellinger is below χ², pointwise.
* `mixture_ge_component` — a mixture dominates any one component.
* `gauss_lower_envelope`, `gauss_upper_envelope` — the two shifted-Gaussian envelopes.
* `majorise` — `3M|y| ≤ y²/4 + 9M²`.
* `pow_le_exp` — `x^n ≤ n^n e^x` for `x ≥ 0`, from `1 + t ≤ e^t`.
* `sq_pow_le_exp` — `(y²)^r ≤ (r/a)^r e^{a y²}`.
* `envelope_bound` — the pointwise domination of the whole envelope by a Gaussian.
* `envelope_integrable` — **the envelope is integrable**, which is what dominated
  convergence needs.

## WHAT THIS DOES NOT ESTABLISH

- The Taylor remainder itself (`|d_h(y)| ≤ C|h|^r(1+|y|^r)·envelope`) is not derived
  here; the components are analytic in `h`, and the Lagrange form of the remainder
  uses exactly the derivatives of `LeanQueryGaussianLevelV1`.
- The constant `c₊` is therefore not computed; what is closed is that the majorant
  which dominates the ratio is integrable, so the `h^{2r}` ORDER is not obstructed by
  the tails.
-/

namespace CIGAMF.P13.QueryHellingerEnvelope

open MeasureTheory Finset

/-- Hellinger is below χ², pointwise. -/
theorem chi2_pointwise (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ (p - q) ^ 2 / q := by
  have hsp : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hspnn : 0 ≤ Real.sqrt p := Real.sqrt_nonneg p
  have hid : (Real.sqrt p - Real.sqrt q) ^ 2 * (Real.sqrt p + Real.sqrt q) ^ 2
      = (p - q) ^ 2 := by nlinarith [hsp, hsq]
  have hge : q ≤ (Real.sqrt p + Real.sqrt q) ^ 2 := by nlinarith [hsq, hspnn, hsqpos]
  rw [le_div_iff₀ hq]
  nlinarith [hid, hge, sq_nonneg (Real.sqrt p - Real.sqrt q)]

/-- A mixture dominates any one of its components. -/
theorem mixture_ge_component {X : Type*} [Fintype X] [DecidableEq X]
    (pi f : X → ℝ) (hpi : ∀ x, 0 ≤ pi x) (hf : ∀ x, 0 ≤ f x) (x₀ : X) :
    pi x₀ * f x₀ ≤ ∑ x, pi x * f x :=
  Finset.single_le_sum (fun x _ => mul_nonneg (hpi x) (hf x)) (Finset.mem_univ x₀)

/-- The lower envelope of a shifted Gaussian. -/
theorem gauss_lower_envelope (σ M m y : ℝ) (hσ : 0 < σ) (hm : |m| ≤ M) :
    Real.exp (-(y ^ 2) / (2 * σ ^ 2) - M * |y| / σ ^ 2 - M ^ 2 / (2 * σ ^ 2))
      ≤ Real.exp (-((y - m) ^ 2) / (2 * σ ^ 2)) := by
  have hσ2 : (0:ℝ) < σ ^ 2 := by positivity
  refine Real.exp_le_exp.2 ?_
  have h1 : -(|m| * |y|) ≤ m * y := by
    have := neg_abs_le (m * y)
    rwa [abs_mul] at this
  have h2 : m ^ 2 ≤ M ^ 2 := by
    have h0 : 0 ≤ |m| := abs_nonneg m
    nlinarith [sq_abs m, hm, h0]
  have hy : 0 ≤ |y| := abs_nonneg y
  have hmM : |m| ≤ M := hm
  have hkey : (y - m) ^ 2 ≤ y ^ 2 + 2 * M * |y| + M ^ 2 := by
    nlinarith [h1, h2, hy, hmM, mul_le_mul_of_nonneg_right hm hy]
  have hgoal : -(y ^ 2) / (2 * σ ^ 2) - M * |y| / σ ^ 2 - M ^ 2 / (2 * σ ^ 2)
      = (-(y ^ 2) - 2 * M * |y| - M ^ 2) / (2 * σ ^ 2) := by
    field_simp
    try ring
  rw [hgoal, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hkey
    (le_of_lt (by positivity : (0:ℝ) < 2 * σ ^ 2))
  nlinarith [hmul]

/-- The upper envelope of a shifted Gaussian. -/
theorem gauss_upper_envelope (σ M m y : ℝ) (hσ : 0 < σ) (hm : |m| ≤ M) :
    Real.exp (-((y - m) ^ 2) / (2 * σ ^ 2))
      ≤ Real.exp (-(y ^ 2) / (2 * σ ^ 2) + M * |y| / σ ^ 2) := by
  have hσ2 : (0:ℝ) < σ ^ 2 := by positivity
  refine Real.exp_le_exp.2 ?_
  have h1 : m * y ≤ |m| * |y| := by
    have := le_abs_self (m * y)
    rwa [abs_mul] at this
  have hy : 0 ≤ |y| := abs_nonneg y
  have hkey : y ^ 2 - 2 * M * |y| ≤ (y - m) ^ 2 := by
    nlinarith [h1, hy, mul_le_mul_of_nonneg_right hm hy, sq_nonneg m]
  have hgoal : -(y ^ 2) / (2 * σ ^ 2) + M * |y| / σ ^ 2
      = (-(y ^ 2) + 2 * M * |y|) / (2 * σ ^ 2) := by
    field_simp
    try ring
  rw [hgoal, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right hkey
    (le_of_lt (by positivity : (0:ℝ) < 2 * σ ^ 2))
  nlinarith [hmul]

/-- `3M|y| ≤ y²/4 + 9M²`: the majorisation that turns the ratio of envelopes into a
Gaussian with a smaller rate times a constant. -/
theorem majorise (M y : ℝ) : 3 * M * |y| ≤ y ^ 2 / 4 + 9 * M ^ 2 := by
  nlinarith [sq_nonneg (|y| / 2 - 3 * M), sq_abs y, abs_nonneg y]

/-- `x^n ≤ n^n e^x` for `x ≥ 0`, from `1 + t ≤ e^t`. -/
theorem pow_le_exp (n : ℕ) (x : ℝ) (hx : 0 ≤ x) : x ^ n ≤ (n : ℝ) ^ n * Real.exp x := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp only [pow_zero, one_mul]
    exact Real.one_le_exp hx
  · have hn : (0:ℝ) < (n : ℝ) := by exact_mod_cast h
    have h1 : x / (n : ℝ) ≤ Real.exp (x / (n : ℝ)) := by
      have := Real.add_one_le_exp (x / (n : ℝ))
      linarith
    have hnn : (0:ℝ) ≤ x / (n : ℝ) := by positivity
    have h2 : (x / (n : ℝ)) ^ n ≤ (Real.exp (x / (n : ℝ))) ^ n := by
      exact pow_le_pow_left₀ hnn h1 n
    have h3 : (Real.exp (x / (n : ℝ))) ^ n = Real.exp x := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    rw [h3, div_pow, div_le_iff₀ (by positivity)] at h2
    linarith [h2]

/-- `(y²)^r ≤ (r/a)^r e^{a y²}` for `a > 0`. -/
theorem sq_pow_le_exp (r : ℕ) (a y : ℝ) (ha : 0 < a) :
    (y ^ 2) ^ r ≤ ((r : ℝ) / a) ^ r * Real.exp (a * y ^ 2) := by
  have hx : (0:ℝ) ≤ a * y ^ 2 := by positivity
  have hb := pow_le_exp r (a * y ^ 2) hx
  have hexp : (a * y ^ 2) ^ r = a ^ r * (y ^ 2) ^ r := by rw [mul_pow]
  rw [hexp] at hb
  have har : (0:ℝ) < a ^ r := by positivity
  have hdiv : ((r : ℝ) / a) ^ r = (r : ℝ) ^ r / a ^ r := by rw [div_pow]
  rw [hdiv, div_mul_eq_mul_div, le_div_iff₀ har]
  linarith [hb]

/-- The pointwise domination of the envelope by a Gaussian with half the rate. -/
theorem envelope_bound (C0 C1 b : ℝ) (r : ℕ) (y : ℝ) (hb : 0 < b)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    (C0 + C1 * (y ^ 2) ^ r) * Real.exp (-(b * y ^ 2))
      ≤ C0 * Real.exp (-(b / 2 * y ^ 2))
        + C1 * (((2 * (r : ℝ)) / b) ^ r * Real.exp (-(b / 2 * y ^ 2))) := by
  have hy : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
  have hb2 : (0:ℝ) < b / 2 := by linarith
  have hmono : Real.exp (-(b * y ^ 2)) ≤ Real.exp (-(b / 2 * y ^ 2)) :=
    Real.exp_le_exp.2 (by nlinarith [hy, hb])
  have hpos : (0:ℝ) < Real.exp (-(b * y ^ 2)) := Real.exp_pos _
  have hpoly := sq_pow_le_exp r (b / 2) y hb2
  have hrw : ((r : ℝ) / (b / 2)) = (2 * (r : ℝ)) / b := by
    field_simp
  rw [hrw] at hpoly
  have hterm : C1 * (y ^ 2) ^ r * Real.exp (-(b * y ^ 2))
      ≤ C1 * (((2 * (r : ℝ)) / b) ^ r * Real.exp (-(b / 2 * y ^ 2))) := by
    have hstep : (y ^ 2) ^ r * Real.exp (-(b * y ^ 2))
        ≤ ((2 * (r : ℝ)) / b) ^ r * Real.exp (b / 2 * y ^ 2) * Real.exp (-(b * y ^ 2)) :=
      mul_le_mul_of_nonneg_right hpoly hpos.le
    have hcomb : Real.exp (b / 2 * y ^ 2) * Real.exp (-(b * y ^ 2))
        = Real.exp (-(b / 2 * y ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc C1 * (y ^ 2) ^ r * Real.exp (-(b * y ^ 2))
        = C1 * ((y ^ 2) ^ r * Real.exp (-(b * y ^ 2))) := by ring
      _ ≤ C1 * (((2 * (r : ℝ)) / b) ^ r * Real.exp (b / 2 * y ^ 2)
            * Real.exp (-(b * y ^ 2))) := by
          exact mul_le_mul_of_nonneg_left hstep hC1
      _ = C1 * (((2 * (r : ℝ)) / b) ^ r * Real.exp (-(b / 2 * y ^ 2))) := by
          rw [mul_assoc, hcomb]
  have hfirst : C0 * Real.exp (-(b * y ^ 2)) ≤ C0 * Real.exp (-(b / 2 * y ^ 2)) :=
    mul_le_mul_of_nonneg_left hmono hC0
  calc (C0 + C1 * (y ^ 2) ^ r) * Real.exp (-(b * y ^ 2))
      = C0 * Real.exp (-(b * y ^ 2)) + C1 * (y ^ 2) ^ r * Real.exp (-(b * y ^ 2)) := by ring
    _ ≤ _ := by linarith [hfirst, hterm]

/-- **The envelope is integrable** -- what dominated convergence needs. -/
theorem envelope_integrable (C0 C1 b : ℝ) (r : ℕ) (hb : 0 < b)
    (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) :
    Integrable (fun y : ℝ => (C0 + C1 * (y ^ 2) ^ r) * Real.exp (-(b * y ^ 2))) := by
  have hb2 : (0:ℝ) < b / 2 := by linarith
  have hgauss : Integrable (fun y : ℝ => Real.exp (-(b / 2 * y ^ 2))) := by
    have := integrable_exp_neg_mul_sq hb2
    simpa [neg_mul] using this
  have hdom : Integrable (fun y : ℝ => C0 * Real.exp (-(b / 2 * y ^ 2))
      + C1 * (((2 * (r : ℝ)) / b) ^ r * Real.exp (-(b / 2 * y ^ 2)))) :=
    (hgauss.const_mul C0).add ((hgauss.const_mul (((2 * (r : ℝ)) / b) ^ r)).const_mul C1)
  have hcont : Continuous (fun y : ℝ => (C0 + C1 * (y ^ 2) ^ r) * Real.exp (-(b * y ^ 2))) := by
    fun_prop
  refine hdom.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hnn : 0 ≤ (C0 + C1 * (y ^ 2) ^ r) * Real.exp (-(b * y ^ 2)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  exact envelope_bound C0 C1 b r y hb hC0 hC1

#print axioms chi2_pointwise
#print axioms mixture_ge_component
#print axioms gauss_lower_envelope
#print axioms gauss_upper_envelope
#print axioms majorise
#print axioms pow_le_exp
#print axioms sq_pow_le_exp
#print axioms envelope_bound
#print axioms envelope_integrable

end CIGAMF.P13.QueryHellingerEnvelope
