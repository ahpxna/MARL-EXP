import «LeanPaperA7ConfidenceV1»

/-!
# Paper A7: the closed-form process the implementation uses is an EXACT martingale

The stopping rule computes

    M_t = prod_e sqrt( a / (a + N_e(t)) ) * exp( S_e(t)^2 / (2 (a + N_e(t))) ),

and the corpus so far justified it through a FINITE mixture and a supermartingale property.
That is the wrong object twice over: the threshold carries the continuous-prior penalty
`(1/2) sum_e log(1 + N_e/a)`, and the closed form is not merely a supermartingale.

The identity below settles it in one Gaussian integral.  Write `f_n(s)` for a single
coordinate's factor.  Then for a standard normal innovation `Z`,

    E[ f_{n+1}(s + Z) ] = f_n(s)      exactly,

because completing the square gives

    E exp( (s+Z)^2 / (2(v+1)) ) = sqrt( (v+1)/v ) * exp( s^2 / (2v) ),      v = a + n > 0,

and the two square-root prefactors cancel.  No series, no continuous-prior integral, and no
conditional Fubini over a parametrised family: the transfer that the mixture route needed is
simply not performed.

WHAT THIS DOES AND DOES NOT ESTABLISH.  This is the one-step identity at a FIXED past, which
is the analytic core.  Turning it into "`M_t` is a martingale" still requires, and none of
it is in this file:

  1. measurability of `N_e(t)`, `S_e(t)` and the query `q_t` with respect to the filtration;
  2. that the next innovation has conditional law `N(0,1)` given the past;
  3. applying the identity at a RANDOM past --- `N_e(t)` and `S_e(t)` are not constants, and
     it must NOT be replaced by "`S_e` given `N_e` is Gaussian", which is false under
     adaptive sampling;
  4. `E M_t = 1` and integrability, by induction on `t`;
  5. joining `log M_t` to the implementation's own statistic and threshold, and then Ville.

The regularisation constant `a` is held FIXED throughout, and the process is taken at a
fixed true parameter.  Substituting a time-varying estimate for the parameter does not
preserve the martingale property, and nothing here licenses that.
-/

namespace CIGAMF.P13.PaperAMartingale

open MeasureTheory
open CIGAMF.P13.PaperA7Confidence

/-- One coordinate's factor in the closed-form process. -/
noncomputable def mgfFactor (a n s : ℝ) : ℝ :=
  Real.sqrt (a / (a + n)) * Real.exp (s ^ 2 / (2 * (a + n)))

/-- **The Gaussian integral behind the identity.**  Completing the square turns the shifted
quadratic into a Gaussian in `z` plus a constant, and the constant is the factor at the
smaller count. -/
theorem shift_integral (c s : ℝ) (hc : 1 < c) :
    ∫ z : ℝ, Real.exp ((s + z) ^ 2 / (2 * c)) * gaussianPDF 0 1 z
      = Real.sqrt (c / (c - 1)) * Real.exp (s ^ 2 / (2 * (c - 1))) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hk : (0 : ℝ) < c - 1 := by linarith
  have hb : (0 : ℝ) < (c - 1) / (2 * c) := by positivity
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  -- pointwise: a Gaussian in `z` times a constant
  have hpoint : ∀ z : ℝ,
      Real.exp ((s + z) ^ 2 / (2 * c)) * gaussianPDF 0 1 z
        = (Real.exp (s ^ 2 / (2 * (c - 1))) / Real.sqrt (2 * Real.pi))
            * Real.exp (-((c - 1) / (2 * c)) * (z - s / (c - 1)) ^ 2) := by
    intro z
    unfold gaussianPDF
    have hexp : (s + z) ^ 2 / (2 * c) + -((z - 0) ^ 2 / (2 * 1 ^ 2))
        = s ^ 2 / (2 * (c - 1)) + -((c - 1) / (2 * c)) * (z - s / (c - 1)) ^ 2 := by
      field_simp
      ring
    rw [show Real.exp ((s + z) ^ 2 / (2 * c))
          * (Real.exp (-((z - 0) ^ 2 / (2 * 1 ^ 2))) / (1 * Real.sqrt (2 * Real.pi)))
        = (Real.exp ((s + z) ^ 2 / (2 * c)) * Real.exp (-((z - 0) ^ 2 / (2 * 1 ^ 2))))
            / Real.sqrt (2 * Real.pi) by ring]
    rw [← Real.exp_add, hexp, Real.exp_add]
    ring
  rw [show (fun z : ℝ => Real.exp ((s + z) ^ 2 / (2 * c)) * gaussianPDF 0 1 z)
      = (fun z : ℝ => (Real.exp (s ^ 2 / (2 * (c - 1))) / Real.sqrt (2 * Real.pi))
          * Real.exp (-((c - 1) / (2 * c)) * (z - s / (c - 1)) ^ 2)) from funext hpoint]
  rw [MeasureTheory.integral_const_mul]
  have hshift : ∫ z : ℝ, Real.exp (-((c - 1) / (2 * c)) * (z - s / (c - 1)) ^ 2)
      = ∫ z : ℝ, Real.exp (-((c - 1) / (2 * c)) * z ^ 2) :=
    MeasureTheory.integral_sub_right_eq_self
      (fun z => Real.exp (-((c - 1) / (2 * c)) * z ^ 2)) (s / (c - 1))
  rw [hshift, integral_gaussian]
  have hval : Real.sqrt (Real.pi / ((c - 1) / (2 * c)))
      = Real.sqrt (c / (c - 1)) * Real.sqrt (2 * Real.pi) := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ c / (c - 1))]
    congr 1
    field_simp
  rw [hval]
  field_simp

/-- **The one-step identity, at a fixed past.**  The factor at count `n+1`, averaged over a
standard normal innovation, is exactly the factor at count `n`. -/
theorem one_step_mean (a n s : ℝ) (ha : 0 < a) (hn : 0 ≤ n) :
    ∫ z : ℝ, mgfFactor a (n + 1) (s + z) * gaussianPDF 0 1 z = mgfFactor a n s := by
  have hv : (0 : ℝ) < a + n := by linarith
  have hc : (1 : ℝ) < a + n + 1 := by linarith
  unfold mgfFactor
  have hrw : ∀ z : ℝ,
      Real.sqrt (a / (a + (n + 1))) * Real.exp ((s + z) ^ 2 / (2 * (a + (n + 1))))
          * gaussianPDF 0 1 z
        = Real.sqrt (a / (a + (n + 1)))
            * (Real.exp ((s + z) ^ 2 / (2 * (a + n + 1))) * gaussianPDF 0 1 z) := by
    intro z
    have : a + (n + 1) = a + n + 1 := by ring
    rw [this]
    ring
  rw [show (fun z : ℝ => Real.sqrt (a / (a + (n + 1)))
        * Real.exp ((s + z) ^ 2 / (2 * (a + (n + 1)))) * gaussianPDF 0 1 z)
      = (fun z : ℝ => Real.sqrt (a / (a + (n + 1)))
          * (Real.exp ((s + z) ^ 2 / (2 * (a + n + 1))) * gaussianPDF 0 1 z))
      from funext hrw]
  rw [MeasureTheory.integral_const_mul, shift_integral (a + n + 1) s hc]
  have hcm : a + n + 1 - 1 = a + n := by ring
  rw [hcm]
  have hsq : Real.sqrt (a / (a + (n + 1))) * Real.sqrt ((a + n + 1) / (a + n))
      = Real.sqrt (a / (a + n)) := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ a / (a + (n + 1)))]
    congr 1
    have h1 : a + (n + 1) = a + n + 1 := by ring
    rw [h1]
    field_simp
  rw [← mul_assoc, hsq]

/-- **A martingale, not a supermartingale.**  The mean of the next factor is the current
one, with equality --- stated separately because the distinction is what lets the threshold
carry the continuous-prior penalty rather than a bound on it. -/
theorem one_step_is_equality (a n s : ℝ) (ha : 0 < a) (hn : 0 ≤ n) :
    ∫ z : ℝ, mgfFactor a (n + 1) (s + z) * gaussianPDF 0 1 z = mgfFactor a n s
      ∧ ¬ (∫ z : ℝ, mgfFactor a (n + 1) (s + z) * gaussianPDF 0 1 z < mgfFactor a n s) := by
  have h := one_step_mean a n s ha hn
  exact ⟨h, by rw [h]; exact lt_irrefl _⟩

/-! ## Audit -/

#print axioms shift_integral
#print axioms one_step_mean
#print axioms one_step_is_equality

end CIGAMF.P13.PaperAMartingale
