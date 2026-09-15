import «LeanD6RepeatedDiscoveryV1»

/-! # Step 3: `512 <= r0` is the wrong hypothesis, and the data says so

`expected_bad_epoch_work` concludes `<= 2 * eta d r0` with
`eta d r0 = ofReal (2*d*exp(-r0/128))`, so the bound is `4*d*exp(-r0/128)`.
The hypothesis `512 <= r0` does not mention `d`.  It is used for exactly one
thing -- `linear_exp_bound` needs `exp(-r0/128) <= 1/4` to get the geometric
ratio -- and it does nothing about the prefactor `4*d`.

`research/high_risk_20260910/d6_revalidation_epochs.json` measures the
consequence, and the column `theoretical_infinite_expected_bad_epoch_work_upper`
is exactly `4*d*exp(-r0/128)`:

    q     d=2q+1   badwork @512   bound @512    badwork @1024   bound @1024
    4     9        0.0000         0.66          0.0000          -
    64    129      0.053-0.073    9.45          0.0000          -
    256   513      0.487-0.500    37.58         -               -
    1024  2049     0.970-0.997    150.12        0.003-0.007     2.75

At `q = 1024, r0 = 512` nearly every epoch is bad and the bound is `150` -- it
is not loose, it is VACUOUS, since the quantity it bounds is at most one per
epoch.  Raising `r0` to `1024` collapses the failure to `~0.005`.

`bad_epoch_threshold` replaces the constant by what the prefactor requires:
`r0 >= 128*log(4*d/tol)` gives `2*eta d r0 <= tol` for any target, uniformly in
`d`.  `vacuous_at_512` records the other direction: with the constant
hypothesis alone the bound exceeds one -- says nothing at all -- as soon as
`d >= 14`, i.e. for every `q >= 7`.

This does not weaken `512 <= r0`; that hypothesis is still needed for the
geometric ratio and both are required together.  What changes is that the
guarantee is now uniform in `q` instead of silently dying at `q = 7`.
-/
namespace CIGAMF.P13.D6UniformDiscoveryThreshold
open scoped BigOperators ENNReal
open Finset MeasureTheory
open CIGAMF.P13.D6DiscoveryStopping CIGAMF.P13.D6DiscoveryVectorCertificate
open CIGAMF.P13.D6NuisanceFreeDiscoveryLaw CIGAMF.P13.D6RepeatedDiscovery
noncomputable section
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The logarithmic threshold, put in multiplicative form. -/
lemma exp_threshold_of_log (d r0 : ℕ) (tol : ℝ) (htol : 0 < tol) (hd : 0 < d)
    (hlog : 128*Real.log (4*(d:ℝ)/tol) ≤ (r0:ℝ)) :
    4*(d:ℝ) ≤ tol*Real.exp ((r0:ℝ)/128) := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hpos : (0:ℝ) < 4*(d:ℝ)/tol := by positivity
  have h1 : 4*(d:ℝ)/tol ≤ Real.exp ((r0:ℝ)/128) := by
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 := mul_le_mul_of_nonneg_left h1 htol.le
  have h3 : tol*(4*(d:ℝ)/tol) = 4*(d:ℝ) := by field_simp
  linarith [h2,h3.symm.le,h3.le]

/-- Any target tolerance is reachable, uniformly in the dimension. -/
theorem eta_le_of_exp_threshold (d r0 : ℕ) (tol : ℝ) (htol : 0 < tol)
    (hr0 : 4*(d:ℝ) ≤ tol*Real.exp ((r0:ℝ)/128)) :
    2*eta d r0 ≤ ENNReal.ofReal tol := by
  have hen : (0:ℝ) < Real.exp (-(r0:ℝ)/128) := Real.exp_pos _
  have he : Real.exp (-(r0:ℝ)/128)*Real.exp ((r0:ℝ)/128) = 1 := by
    rw [← Real.exp_add, show -(r0:ℝ)/128+(r0:ℝ)/128=0 by ring, Real.exp_zero]
  have hkey : 2*(2*(d:ℝ)*Real.exp (-(r0:ℝ)/128)) ≤ tol := by
    nlinarith [mul_le_mul_of_nonneg_right hr0 hen.le,he]
  have h2e : (2:ℝ≥0∞)=ENNReal.ofReal 2 := by simp
  unfold eta
  rw [h2e,← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hkey

/-- The threshold form, stated the way it should be used. -/
theorem bad_epoch_threshold (d r0 : ℕ) (tol : ℝ) (htol : 0 < tol) (hd : 0 < d)
    (hlog : 128*Real.log (4*(d:ℝ)/tol) ≤ (r0:ℝ)) :
    2*eta d r0 ≤ ENNReal.ofReal tol :=
  eta_le_of_exp_threshold d r0 tol htol (exp_threshold_of_log d r0 tol htol hd hlog)

/-- The uniform-in-`q` discovery guarantee: the constant hypothesis for the
geometric ratio, the logarithmic one for non-vacuity. -/
theorem uniform_bad_epoch_work (m : J → Fin 4 → ℝ) (B : Finset J) (a : J)
    (hm : ∀ i,(∑ t,signs t*m i t)=target B a i) (r0 : ℕ) (hr0 : 512 ≤ r0)
    (tol : ℝ) (htol : 0 < tol)
    (hlog : 128*Real.log (4*(Fintype.card J:ℝ)/tol) ≤ (r0:ℝ)) :
    (∫⁻ x,badEpochWork B a r0 x ∂vectorPath m) ≤ ENNReal.ofReal tol := by
  letI : Nonempty J := ⟨a⟩
  exact (expected_bad_epoch_work m B a hm r0 hr0).trans
    (bad_epoch_threshold _ r0 tol htol Fintype.card_pos hlog)

/-- The other direction, recorded so the constant is not mistaken for adequate:
at `r0 = 512` the bound exceeds one, hence says nothing, once `d >= 14`. -/
theorem vacuous_at_512 (d : ℕ) (hd : 14 ≤ d) : 1 < 2*eta d 512 := by
  have hdR : (14:ℝ) ≤ d := by exact_mod_cast hd
  have he1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hep : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
  have hsq : (Real.exp 1)^2 < 7.3891 := by nlinarith [he1,hep]
  have hsqn : (0:ℝ) ≤ (Real.exp 1)^2 := sq_nonneg _
  have h4 : (Real.exp 1)^4 < 56 := by nlinarith [hsq,hsqn]
  have hexp4 : Real.exp 4 = (Real.exp 1)^4 := by
    rw [show (4:ℝ)=(4:ℕ)*(1:ℝ) by norm_num,Real.exp_nat_mul]
  have hlt : Real.exp 4 < 4*(d:ℝ) := by rw [hexp4];linarith
  have hinv : 1 < 4*(d:ℝ)*Real.exp (-(4:ℝ)) := by
    have hpos : (0:ℝ) < Real.exp 4 := Real.exp_pos _
    have hid : Real.exp (-(4:ℝ))*Real.exp 4 = 1 := by rw [← Real.exp_add];norm_num
    nlinarith [mul_lt_mul_of_pos_right hlt (Real.exp_pos (-(4:ℝ))),hid]
  have hneg : (-(512:ℕ):ℝ)/128 = -(4:ℝ) := by norm_num
  have h1e : (1:ℝ≥0∞)=ENNReal.ofReal 1 := by simp
  have h2e : (2:ℝ≥0∞)=ENNReal.ofReal 2 := by simp
  unfold eta
  rw [h1e,h2e,← ENNReal.ofReal_mul (by norm_num),hneg]
  apply (ENNReal.ofReal_lt_ofReal_iff (by nlinarith [Real.exp_pos (-(4:ℝ))])).mpr
  nlinarith [hinv]

#print axioms exp_threshold_of_log
#print axioms eta_le_of_exp_threshold
#print axioms bad_epoch_threshold
#print axioms uniform_bad_epoch_work
#print axioms vacuous_at_512
end
end CIGAMF.P13.D6UniformDiscoveryThreshold
