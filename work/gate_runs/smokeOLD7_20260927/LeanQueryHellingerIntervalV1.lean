import Mathlib

/-! # Query step 3b: the LOWER Hellinger bound from ONE interval, by Cauchy-Schwarz.

`LeanQueryGaussianLevelV1.levelSum_ne_zero` gives a point where `Δ_r ≠ 0`; continuity
then gives a finite interval `E` on which `Δ_r` keeps its sign, so `a_E = ∫_E Δ_r ≠ 0`
and Taylor gives `|P_{A,h}(E) - P_{B,h}(E)| ≥ |a_E| |h|^r/2` for small `h`.  This file
converts that probability gap into a Hellinger lower bound -- directly, not through KL
and Pinsker.

## THE CONVERSION

With `χ` the indicator of `E` (any `0 ≤ χ ≤ 1` works), pointwise

    χ(p - q) = χ(√p - √q)(√p + √q),   |χ(p-q)| ≤ (t/2)(√p-√q)² + (1/(2t))(√p+√q)²,

for every `t > 0`.  The first integral is `2H²`; the second is EXACTLY `4 - 2H²`,
because `(√p+√q)² + (√p-√q)² = 2(p+q)` and both densities integrate to `1`.  So

    |ΔP(E)| ≤ t H² + (4 - 2H²)/(2t) ≤ t H² + 2/t     for every t > 0,

and optimising `t` (at `t = √(2/H²)`) gives `ΔP(E)² ≤ 8 H²`.  Substituting the Taylor
gap `|ΔP(E)| ≥ |a_E||h|^r/2`:

    H² ≥ a_E² |h|^{2r} / 32.

## WHAT IS PROVED

* `young_pointwise` — `|uv| ≤ (t/2)u² + (1/(2t))v²`.
* `sqrt_sum_sq_identity`, `factor_pointwise` — the two algebraic identities.
* `sum_sq_integral` — `∫(√p+√q)² = 4 - 2H²`, exactly.
* `gap_le_of_integrals` — `|∫χ(p-q)| ≤ tH² + (4-2H²)/(2t)` for every `t > 0`.
* `sq_le_of_all_t` — **the optimisation**: the family of bounds forces `Δ² ≤ 8H²`.
* `hellinger_lower_from_interval` — the assembled statement: a gap of order
  `|a_E||h|^r/2` forces `H² ≥ a_E²|h|^{2r}/32`.

## WHAT THIS DOES NOT ESTABLISH

- That `a_E ≠ 0`, and that the Taylor remainder is uniformly `O(h^{r+1})` on the finite
  interval, are inputs: they enter as the hypothesis on the gap.
- The plan's constant `/16` comes from the cruder step `|ΔP| ≤ 2√(H²)`; what the stated
  inequalities actually give is `/32`.  The ORDER `h^{2r}` is identical, and that is
  what the rate law uses.
- The matching upper bound is `LeanQueryHellingerEnvelopeV1`.
-/

namespace CIGAMF.P13.QueryHellingerInterval

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Young's inequality, pointwise. -/
theorem young_pointwise (u v t : ℝ) (ht : 0 < t) :
    |u * v| ≤ t / 2 * u ^ 2 + 1 / (2 * t) * v ^ 2 := by
  have habs : |u * v| = |u| * |v| := abs_mul u v
  have hu : |u| ^ 2 = u ^ 2 := sq_abs u
  have hv : |v| ^ 2 = v ^ 2 := sq_abs v
  have h2t : (0:ℝ) < 2 * t := by linarith
  have hkey : 2 * t * (|u| * |v|) ≤ t ^ 2 * |u| ^ 2 + |v| ^ 2 := by
    nlinarith [sq_nonneg (t * |u| - |v|)]
  rw [habs, ← hu, ← hv, ← sub_nonneg]
  have hrw : t / 2 * |u| ^ 2 + 1 / (2 * t) * |v| ^ 2 - |u| * |v|
      = (t ^ 2 * |u| ^ 2 + |v| ^ 2 - 2 * t * (|u| * |v|)) / (2 * t) := by
    field_simp
    try ring
  rw [hrw]
  exact div_nonneg (by linarith [hkey]) h2t.le

/-- `(√p+√q)² = 2(p+q) - (√p-√q)²`: the identity that makes the second integral exactly
`4 - 2H²`, with no second Cauchy-Schwarz. -/
theorem sqrt_sum_sq_identity (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (Real.sqrt p + Real.sqrt q) ^ 2 = 2 * (p + q) - (Real.sqrt p - Real.sqrt q) ^ 2 := by
  have h1 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have h2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  nlinarith [h1, h2]

/-- `p - q = (√p - √q)(√p + √q)`. -/
theorem factor_pointwise (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    p - q = (Real.sqrt p - Real.sqrt q) * (Real.sqrt p + Real.sqrt q) := by
  have h1 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  have h2 : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  nlinarith [h1, h2]

/-- **The optimisation.**  `D ≤ t·H² + 2/t` for every `t > 0` forces `D² ≤ 8H²`. -/
theorem sq_le_of_all_t (D H2 : ℝ) (hD : 0 ≤ D) (hH : 0 ≤ H2)
    (hall : ∀ t : ℝ, 0 < t → D ≤ t * H2 + 2 / t) : D ^ 2 ≤ 8 * H2 := by
  by_contra hcon
  push_neg at hcon
  have hD2 : (0:ℝ) < D ^ 2 := by nlinarith
  have hDpos : 0 < D := by
    rcases eq_or_lt_of_le hD with h | h
    · exfalso; rw [← h] at hD2; norm_num at hD2
    · exact h
  rcases eq_or_lt_of_le hH with hzero | hpos
  · have ht : (0:ℝ) < 4 / D := by positivity
    have hb := hall _ ht
    rw [← hzero] at hb
    have h2 : 2 / (4 / D) = D / 2 := by field_simp; norm_num
    rw [h2, mul_zero, zero_add] at hb
    linarith
  · have ht : (0:ℝ) < D / (2 * H2) := by positivity
    have hb := hall _ ht
    have hv : D / (2 * H2) * H2 + 2 / (D / (2 * H2)) = D / 2 + 4 * H2 / D := by
      field_simp
      try ring
    rw [hv] at hb
    have hmul : D * D ≤ D * (D / 2 + 4 * H2 / D) :=
      mul_le_mul_of_nonneg_left hb hDpos.le
    have hexp : D * (D / 2 + 4 * H2 / D) = D ^ 2 / 2 + 4 * H2 := by
      field_simp
      try ring
    rw [hexp] at hmul
    nlinarith [hmul, hcon]

/-- `∫(√p+√q)² = 4 - 2H²`, exactly. -/
theorem sum_sq_integral (μ : Measure Ω) (p q : Ω → ℝ) (H2 : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpi : Integrable p μ) (hqi : Integrable q μ)
    (hsq : Integrable (fun x => (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hH2 : ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ = 2 * H2)
    (hpint : ∫ x, p x ∂μ = 1) (hqint : ∫ x, q x ∂μ = 1) :
    ∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂μ = 4 - 2 * H2 := by
  have hpt : ∀ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2
      = 2 * (p x + q x) - (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 :=
    fun x => sqrt_sum_sq_identity (p x) (q x) (hp x) (hq x)
  have hadd : Integrable (fun x => 2 * (p x + q x)) μ := ((hpi.add hqi).const_mul 2)
  calc ∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂μ
      = ∫ x, (2 * (p x + q x) - (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) ∂μ := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x, 2 * (p x + q x) ∂μ) - ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ :=
        integral_sub hadd hsq
    _ = 4 - 2 * H2 := by
        rw [hH2, integral_const_mul, integral_add hpi hqi, hpint, hqint]
        norm_num

/-- The integral step. -/
theorem gap_le_of_integrals (μ : Measure Ω) (p q chi : Ω → ℝ) (t H2 : ℝ) (ht : 0 < t)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hchi0 : ∀ x, 0 ≤ chi x) (hchi1 : ∀ x, chi x ≤ 1)
    (hdiff : Integrable (fun x => chi x * (p x - q x)) μ)
    (hsq : Integrable (fun x => (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hsum : Integrable (fun x => (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) μ)
    (hH2 : ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂μ = 2 * H2)
    (hS : ∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂μ = 4 - 2 * H2) :
    |∫ x, chi x * (p x - q x) ∂μ| ≤ t * H2 + (4 - 2 * H2) / (2 * t) := by
  have hbound : ∀ x, |chi x * (p x - q x)|
      ≤ t / 2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2
        + 1 / (2 * t) * (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 := by
    intro x
    have h1 : |chi x * (p x - q x)| ≤ |p x - q x| := by
      rw [abs_mul, abs_of_nonneg (hchi0 x)]
      nlinarith [abs_nonneg (p x - q x), hchi1 x, hchi0 x]
    have h2 : |p x - q x|
        ≤ t / 2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2
          + 1 / (2 * t) * (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 := by
      rw [factor_pointwise (p x) (q x) (hp x) (hq x)]
      exact young_pointwise _ _ t ht
    linarith [h1, h2]
  have hmaj : Integrable (fun x => t / 2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2
      + 1 / (2 * t) * (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) μ :=
    (hsq.const_mul (t / 2)).add (hsum.const_mul (1 / (2 * t)))
  calc |∫ x, chi x * (p x - q x) ∂μ|
      ≤ ∫ x, |chi x * (p x - q x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (t / 2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2
          + 1 / (2 * t) * (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) ∂μ :=
        integral_mono hdiff.abs hmaj hbound
    _ = t * H2 + (4 - 2 * H2) / (2 * t) := by
        rw [integral_add (hsq.const_mul (t / 2)) (hsum.const_mul (1 / (2 * t))),
          integral_const_mul, integral_const_mul, hH2, hS]
        field_simp
        try ring

/-- **The assembled lower bound.**  A probability gap of order `|a_E||h|^r/2` forces
`H² ≥ a_E²|h|^{2r}/32`. -/
theorem hellinger_lower_from_interval (H2 aE hr : ℝ) (hH : 0 ≤ H2) (hr0 : 0 ≤ hr)
    (hDbound : ∀ t : ℝ, 0 < t → |aE| * hr / 2 ≤ t * H2 + 2 / t) :
    aE ^ 2 * hr ^ 2 / 32 ≤ H2 := by
  have hDnn : 0 ≤ |aE| * hr / 2 := by positivity
  have hsq := sq_le_of_all_t (|aE| * hr / 2) H2 hDnn hH hDbound
  have habs : |aE| ^ 2 = aE ^ 2 := sq_abs aE
  have hexp : (|aE| * hr / 2) ^ 2 = aE ^ 2 * hr ^ 2 / 4 := by
    rw [div_pow, mul_pow, habs]
    ring
  rw [hexp] at hsq
  linarith

#print axioms young_pointwise
#print axioms sqrt_sum_sq_identity
#print axioms factor_pointwise
#print axioms sq_le_of_all_t
#print axioms sum_sq_integral
#print axioms gap_le_of_integrals
#print axioms hellinger_lower_from_interval

end CIGAMF.P13.QueryHellingerInterval
