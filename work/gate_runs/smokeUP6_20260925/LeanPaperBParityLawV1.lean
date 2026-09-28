import «LeanPaperBParityNormV1»

/-!
# Paper B: the parity query's observation LAW, and its characteristic function

`LeanPaperBParityNormV1` normalised the cube sum, but a normalised sum over the cube is still
not the characteristic function of anything: the observation carries additive Gaussian
noise, and the object whose characteristic function the decoder and the density bounds use is
the observation LAW.  This module defines that law and computes its characteristic function.

The model, for query `j`, mask value `v` (`-1` exactly when the query names the world),
step `h` and noise variance `sigma2`:

    Y = v * prod_{l<j} Z_l + (h/j) * sum_{l<j} Z_l + xi,
    Z uniform on {-1,+1}^j,  xi ~ N(0, sigma2) independent of Z.

Conditionally on `Z = z` the observation is `N(v chi(z) + (h/j) S(z), sigma2)`, and `Z` is
uniform, so the law of `Y` is the Gaussian mixture `obsLaw` below, with weight `2^-j` on each
cube point.  That definition IS the observation law; it is not a stand-in for the right-hand
side of the identity.

`charFun_obsLaw` computes its characteristic function from Mathlib's `charFun_gaussianReal`
(each component contributes its own `exp(-sigma2 t^2/2)`, which factors out of the mixture),
and `parity_obs_cf_difference` subtracts the two mask values:

    phi_{+}(t) - phi_{-}(t) = 2 i^(j+1) sin t (sin(t h / j))^j exp(-sigma2 t^2 / 2).

This is the normalised gap the decoder uses; the leading constant is `2`, the `h`-dependence
is the `j`-th power, and the Gaussian factor is the noise's, derived rather than posited.
-/

namespace CIGAMF.P13.PaperBParityLaw

open MeasureTheory ProbabilityTheory BoundedContinuousFunction
open scoped NNReal ENNReal
open CIGAMF.P13.PaperBCube CIGAMF.P13.PaperBParity CIGAMF.P13.PaperBParityNorm

/-! ## 1. The cube in real coordinates -/

/-- The `+-1` value of a coordinate, as a real number. -/
noncomputable def sgnR (b : Bool) : ℝ := if b then 1 else -1

/-- The product character of a cube point, real. -/
noncomputable def chrR {j : ℕ} (z : Fin j → Bool) : ℝ := ∏ i, sgnR (z i)

/-- The coordinate sum of a cube point, real. -/
noncomputable def csumR {j : ℕ} (z : Fin j → Bool) : ℝ := ∑ i, sgnR (z i)

theorem sgnR_cast (b : Bool) : ((sgnR b : ℝ) : ℂ) = sgn b := by
  cases b <;> simp [sgnR, sgn]

theorem chrR_cast {j : ℕ} (z : Fin j → Bool) : ((chrR z : ℝ) : ℂ) = chr z := by
  unfold chrR chr
  push_cast
  exact Finset.prod_congr rfl fun i _ => sgnR_cast (z i)

theorem csumR_cast {j : ℕ} (z : Fin j → Bool) : ((csumR z : ℝ) : ℂ) = csum z := by
  unfold csumR csum
  push_cast
  exact Finset.sum_congr rfl fun i _ => sgnR_cast (z i)

/-! ## 2. The observation law -/

/-- The conditional mean of the observation at cube point `z`. -/
noncomputable def obsMean (j : ℕ) (v h : ℝ) (z : Fin j → Bool) : ℝ :=
  v * chrR z + h / (j : ℝ) * csumR z

/-- **The observation law of query `j`**: the uniform mixture over the latent cube of the
conditional Gaussians `N(obsMean z, sigma2)`. -/
noncomputable def obsLaw (j : ℕ) (v h : ℝ) (σ2 : ℝ≥0) : Measure ℝ :=
  ∑ z : Fin j → Bool, ((2 : ℝ≥0∞) ^ j)⁻¹ • gaussianReal (obsMean j v h z) σ2

/-- The law of query `j` in world `w`: the mask value is `-1` exactly when `j = w`. -/
noncomputable def maskR (j w : ℕ) : ℝ := if j = w then -1 else 1

noncomputable def obsLawWorld (j w : ℕ) (h : ℝ) (σ2 : ℝ≥0) : Measure ℝ :=
  obsLaw j (maskR j w) h σ2

/-- It is a probability measure: `2^j` components of mass `2^-j`. -/
theorem obsLaw_univ (j : ℕ) (v h : ℝ) (σ2 : ℝ≥0) : obsLaw j v h σ2 Set.univ = 1 := by
  unfold obsLaw
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  exact ENNReal.mul_inv_cancel (by simp) (by simp)

instance (j : ℕ) (v h : ℝ) (σ2 : ℝ≥0) : IsProbabilityMeasure (obsLaw j v h σ2) :=
  ⟨obsLaw_univ j v h σ2⟩

/-! ## 3. Its characteristic function -/

/-- The characteristic function of a finite mixture is the mixture of the characteristic
functions. -/
theorem charFun_mixture {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤)
    (G : ι → Measure ℝ) [∀ i, IsFiniteMeasure (G i)] (t : ℝ) :
    charFun (∑ i, c i • G i) t = ∑ i, ((c i).toReal : ℂ) * charFun (G i) t := by
  rw [charFun_eq_integral_innerProbChar, integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, ← charFun_eq_integral_innerProbChar, Complex.real_smul]
  · intro i _
    exact ((innerProbChar t).integrable (G i)).smul_measure (hc i)

theorem weight_toReal (j : ℕ) : (((2 : ℝ≥0∞) ^ j)⁻¹.toReal : ℂ) = ((2 : ℂ) ^ j)⁻¹ := by
  rw [ENNReal.toReal_inv, ENNReal.toReal_pow]
  push_cast
  simp

/-- **The characteristic function of the observation law**: the cube sum, normalised by
`2^-j`, times the noise's Gaussian factor. -/
theorem charFun_obsLaw (j : ℕ) (v h : ℝ) (σ2 : ℝ≥0) (t : ℝ) :
    charFun (obsLaw j v h σ2) t
      = ((2 : ℂ) ^ j)⁻¹ *
          (∑ z : Fin j → Bool,
            Complex.exp ((Complex.I * t * v) * chr z + (Complex.I * t * h / j) * csum z))
          * Complex.exp (-((σ2 : ℝ) * t ^ 2 / 2)) := by
  unfold obsLaw
  rw [charFun_mixture _ (fun _ => by simp) _ t, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [charFun_gaussianReal, weight_toReal, sub_eq_add_neg, Complex.exp_add]
  have hmean : ((t : ℂ) * ((obsMean j v h z : ℝ) : ℂ) * Complex.I)
      = (Complex.I * t * v) * chr z + (Complex.I * t * h / j) * csum z := by
    unfold obsMean
    push_cast
    rw [chrR_cast, csumR_cast]
    ring
  rw [hmean]
  push_cast
  ring

/-- **The characteristic-function gap between the two mask values, exactly.** -/
theorem parity_obs_cf_difference (j : ℕ) (h : ℝ) (σ2 : ℝ≥0) (t : ℝ) :
    charFun (obsLaw j 1 h σ2) t - charFun (obsLaw j (-1) h σ2) t
      = 2 * Complex.I ^ (j + 1) * (Real.sin t : ℂ) * (Real.sin (t * h / j) : ℂ) ^ j
          * Complex.exp (-((σ2 : ℝ) * t ^ 2 / 2)) := by
  rw [charFun_obsLaw, charFun_obsLaw]
  have hplus : ∀ z : Fin j → Bool,
      Complex.exp ((Complex.I * t * ((1 : ℝ) : ℂ)) * chr z + (Complex.I * t * h / j) * csum z)
        = Complex.exp ((Complex.I * t) * chr z + (Complex.I * t * h / j) * csum z) := by
    intro z; congr 1; push_cast; ring
  have hminus : ∀ z : Fin j → Bool,
      Complex.exp ((Complex.I * t * ((-1 : ℝ) : ℂ)) * chr z
          + (Complex.I * t * h / j) * csum z)
        = Complex.exp ((-(Complex.I * t)) * chr z + (Complex.I * t * h / j) * csum z) := by
    intro z; congr 1; push_cast; ring
  simp only [hplus, hminus]
  have hnorm := parity_cf_difference_normalised j t h
  have hs1 : Complex.sinh (Complex.I * t) = (Real.sin t : ℂ) * Complex.I := by
    rw [mul_comm, Complex.sinh_mul_I, Complex.ofReal_sin]
  have hs2 : Complex.sinh (Complex.I * t * h / j)
      = (Real.sin (t * h / j) : ℂ) * Complex.I := by
    have : Complex.I * t * h / j = ((t * h / j : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.sinh_mul_I, Complex.ofReal_sin]
  rw [hs1, hs2] at hnorm
  calc ((2 : ℂ) ^ j)⁻¹ *
          (∑ z : Fin j → Bool,
            Complex.exp ((Complex.I * t) * chr z + (Complex.I * t * h / j) * csum z))
          * Complex.exp (-((σ2 : ℝ) * t ^ 2 / 2))
        - ((2 : ℂ) ^ j)⁻¹ *
          (∑ z : Fin j → Bool,
            Complex.exp ((-(Complex.I * t)) * chr z + (Complex.I * t * h / j) * csum z))
          * Complex.exp (-((σ2 : ℝ) * t ^ 2 / 2))
      = (((2 : ℂ) ^ j)⁻¹ *
          ((∑ z : Fin j → Bool,
              Complex.exp ((Complex.I * t) * chr z + (Complex.I * t * h / j) * csum z))
            - ∑ z : Fin j → Bool,
              Complex.exp ((-(Complex.I * t)) * chr z + (Complex.I * t * h / j) * csum z)))
          * Complex.exp (-((σ2 : ℝ) * t ^ 2 / 2)) := by ring
    _ = _ := by rw [hnorm]; ring

/-- **In the parity channel's own terms**: query `j` separates world `j` from every other
world `w`, and the gap is the display above. -/
theorem parity_world_cf_gap (j w : ℕ) (hw : j ≠ w) (h : ℝ) (σ2 : ℝ≥0) (t : ℝ) :
    charFun (obsLawWorld j w h σ2) t - charFun (obsLawWorld j j h σ2) t
      = 2 * Complex.I ^ (j + 1) * (Real.sin t : ℂ) * (Real.sin (t * h / j) : ℂ) ^ j
          * Complex.exp (-((σ2 : ℝ) * t ^ 2 / 2)) := by
  unfold obsLawWorld maskR
  rw [if_neg hw, if_pos rfl]
  exact parity_obs_cf_difference j h σ2 t

/-- Two worlds that query `j` does not name have the SAME observation law at that query. -/
theorem obsLawWorld_eq_of_not_named (j w w' : ℕ) (hw : j ≠ w) (hw' : j ≠ w') (h : ℝ)
    (σ2 : ℝ≥0) : obsLawWorld j w h σ2 = obsLawWorld j w' h σ2 := by
  unfold obsLawWorld maskR
  rw [if_neg hw, if_neg hw']

/-! ## Audit -/

#print axioms chrR_cast
#print axioms csumR_cast
#print axioms obsLaw_univ
#print axioms charFun_mixture
#print axioms charFun_obsLaw
#print axioms parity_obs_cf_difference
#print axioms parity_world_cf_gap
#print axioms obsLawWorld_eq_of_not_named

end CIGAMF.P13.PaperBParityLaw
