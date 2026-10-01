import Mathlib

/-!
# Paper B: the inequality that takes an envelope bound to a KL bound

The lower-bound chain needs `KL(P_theta^q || P_lambda^q) <= C h^{2s}`, uniformly over the
query class.  The corpus's envelope work bounds `integral (p-q)^2 / l` for a floor `l`.  A
Hellinger bound does **not** give a KL bound, and neither does the envelope by itself: an
extra inequality is needed, and skipping it is the error this file exists to prevent.

The inequality is elementary and is the whole content.  From `log x <= x - 1`,

    p * log(p/q)  <=  p*(p/q) - p  =  (p - q)^2 / q  +  (p - q),

with the right-hand side an *identity*, not a further bound.  Integrating against a common
dominating measure, the last term contributes `integral p - integral q = 0` for two
densities, so

    KL(p || q)  <=  chi^2(p || q)  =  integral (p - q)^2 / q  <=  integral (p - q)^2 / l

whenever `0 < l <= q` pointwise.  So an envelope bound with a floor transfers to KL, and
only through this step.

WHAT IS HERE AND WHAT IS NOT.  The pointwise inequality and the floor comparison are proved
unconditionally.  The integral form is stated with its integrability hypotheses **carried**,
because that is where the work is when the densities are Gaussian mixtures on the line: the
floor has to be integrable against the squared difference, and both densities have to be
integrable.  Instantiating those at the actual observation model, uniformly over the
admissible query class, is Paper B's obligation and is not discharged here.
-/

namespace CIGAMF.P13.PaperBKL

open MeasureTheory

/-- **The pointwise step.**  `p log(p/q)` is dominated by the chi-squared integrand plus a
term whose integral vanishes for two densities.  The right-hand side's second form is an
identity, so nothing is lost twice. -/
theorem kl_integrand_le (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    p * Real.log (p / q) ≤ (p - q) ^ 2 / q + (p - q) := by
  have hid : (p - q) ^ 2 / q + (p - q) = p * (p / q) - p := by
    field_simp
    ring
  rw [hid]
  rcases eq_or_lt_of_le hp with hp0 | hp0
  · rw [← hp0]
    simp
  · have hpq : 0 < p / q := div_pos hp0 hq
    have hlog := Real.log_le_sub_one_of_pos hpq
    nlinarith [hlog, hp0]

/-- **Lowering the denominator raises the chi-squared integrand**, which is how a floor
enters. -/
theorem chi_integrand_mono (p q l : ℝ) (hl : 0 < l) (hlq : l ≤ q) :
    (p - q) ^ 2 / q ≤ (p - q) ^ 2 / l :=
  div_le_div_of_nonneg_left (sq_nonneg _) hl hlq

/-- **The two steps composed, pointwise.** -/
theorem kl_integrand_le_floor (p q l : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hl : 0 < l)
    (hlq : l ≤ q) :
    p * Real.log (p / q) ≤ (p - q) ^ 2 / l + (p - q) := by
  have h1 := kl_integrand_le p q hp hq
  have h2 := chi_integrand_mono p q l hl hlq
  linarith

/-- **The integral form, with its hypotheses carried.**  For two densities against a common
measure, the linear term integrates to zero and the envelope bound transfers to KL. -/
theorem kl_le_envelope {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p q l : α → ℝ)
    (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 < q y) (hl : ∀ y, 0 < l y) (hlq : ∀ y, l y ≤ q y)
    (hkl : Integrable (fun y => p y * Real.log (p y / q y)) μ)
    (henv : Integrable (fun y => (p y - q y) ^ 2 / l y) μ)
    (hdiff : Integrable (fun y => p y - q y) μ)
    (hmass : ∫ y, (p y - q y) ∂μ = 0) :
    ∫ y, p y * Real.log (p y / q y) ∂μ ≤ ∫ y, (p y - q y) ^ 2 / l y ∂μ := by
  have hpt : ∀ y, p y * Real.log (p y / q y)
      ≤ (p y - q y) ^ 2 / l y + (p y - q y) :=
    fun y => kl_integrand_le_floor (p y) (q y) (l y) (hp y) (hq y) (hl y) (hlq y)
  have hmono : ∫ y, p y * Real.log (p y / q y) ∂μ
      ≤ ∫ y, ((p y - q y) ^ 2 / l y + (p y - q y)) ∂μ :=
    integral_mono hkl (henv.add hdiff) hpt
  rwa [integral_add henv hdiff, hmass, add_zero] at hmono

/-- **A Hellinger bound alone does not do this.**  Recorded as a statement about the
arithmetic rather than a remark: the chi-squared integrand exceeds the Hellinger one
pointwise by the factor `(sqrt p + sqrt q)^2 / q`, which is unbounded as `p/q` grows, so no
inequality runs from the Hellinger integral to the KL integral without a further hypothesis.
-/
theorem hellinger_integrand_le_chi (p q : ℝ) (hp : 0 ≤ p) (hq : 0 < q) :
    (p - q) ^ 2 / (Real.sqrt p + Real.sqrt q) ^ 2 ≤ (p - q) ^ 2 / q := by
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt (le_of_lt hq)
  have hle : q ≤ (Real.sqrt p + Real.sqrt q) ^ 2 := by
    nlinarith [Real.sqrt_nonneg p, Real.sqrt_nonneg q, hsq]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hq hle

/-! ## Audit -/

#print axioms kl_integrand_le
#print axioms chi_integrand_mono
#print axioms kl_integrand_le_floor
#print axioms kl_le_envelope
#print axioms hellinger_integrand_le_chi

end CIGAMF.P13.PaperBKL
