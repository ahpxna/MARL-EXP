import «LeanPaperBParityLawV1»

/-!
# Paper B: the decoder's bounded feature and its gap, from the observation law

The decoder of Paper B reads, for query `j`, the bounded feature

    phi_j(y) = cos y   (j odd),        phi_j(y) = sin y   (j even),

and thresholds its average.  What it needs is the GAP between the feature's means under the
two mask values.  Both means are read off the characteristic function at `t = 1`:
`E cos Y = Re phi(1)` and `E sin Y = Im phi(1)` (`mean_cos_eq`, `mean_sin_eq`).  With
`parity_obs_cf_difference` the difference `phi_+(1) - phi_-(1) = 2 i^(j+1) sin 1 sin(h/j)^j
e^(-sigma^2/2)` is real for odd `j` and imaginary for even `j`, so the chosen feature sees its
full modulus (`feature_gap_abs`):

    |E_+ phi_j - E_- phi_j| = 2 sin 1 |sin(h/j)|^j exp(-sigma^2/2),

and `feature_gap_lower` gives `>= 2 sin 1 (3/(4j))^j h^j exp(-sigma^2/2)` for `0 < h <= j`,
the order `h^j` with an explicit constant.
-/

namespace CIGAMF.P13.PaperBParityGap

open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBParity CIGAMF.P13.PaperBParityLaw

/-- The decoder's feature for query `j`. -/
noncomputable def feat (j : ℕ) (y : ℝ) : ℝ := if Even j then Real.sin y else Real.cos y

theorem feat_abs_le (j : ℕ) (y : ℝ) : |feat j y| ≤ 1 := by
  unfold feat; split_ifs
  · exact abs_sin_le_one y
  · exact abs_cos_le_one y

theorem continuous_feat (j : ℕ) : Continuous (feat j) := by
  unfold feat; split_ifs
  · exact Real.continuous_sin
  · exact Real.continuous_cos

theorem integrable_exp_I (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (fun x : ℝ => Complex.exp ((1 : ℝ) * x * Complex.I)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.ofReal_one, one_mul]
  rw [Complex.norm_exp_ofReal_mul_I]

/-- `E cos Y` is the real part of the characteristic function at one. -/
theorem mean_cos_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ y, Real.cos y ∂μ = (charFun μ 1).re := by
  rw [charFun_apply_real]
  have h := Complex.reCLM.integral_comp_comm (integrable_exp_I μ)
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  congr 1
  funext y
  simp only [Complex.ofReal_one, one_mul]
  rw [Complex.exp_ofReal_mul_I_re]

/-- `E sin Y` is the imaginary part of the characteristic function at one. -/
theorem mean_sin_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∫ y, Real.sin y ∂μ = (charFun μ 1).im := by
  rw [charFun_apply_real]
  have h := Complex.imCLM.integral_comp_comm (integrable_exp_I μ)
  simp only [Complex.imCLM_apply] at h
  rw [← h]
  congr 1
  funext y
  simp only [Complex.ofReal_one, one_mul]
  rw [Complex.exp_ofReal_mul_I_im]

/-- `i^(j+1)` is real (`±1`) for odd `j` and imaginary (`±i`) for even `j`. -/
theorem I_pow_odd (j : ℕ) (hj : ¬ Even j) : |(Complex.I ^ (j + 1)).re| = 1 ∧
    (Complex.I ^ (j + 1)).im = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by
    have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hj); omega⟩
  have : Complex.I ^ (2 * k + 1 + 1) = (-1) ^ (k + 1) := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) from by ring, pow_mul, Complex.I_sq]
  rw [this]
  rcases Nat.even_or_odd (k + 1) with he | ho
  · rw [he.neg_one_pow]; simp
  · rw [ho.neg_one_pow]; simp

theorem I_pow_even (j : ℕ) (hj : Even j) : (Complex.I ^ (j + 1)).re = 0 ∧
    |(Complex.I ^ (j + 1)).im| = 1 := by
  obtain ⟨k, rfl⟩ := hj
  have : Complex.I ^ (k + k + 1) = (-1) ^ k * Complex.I := by
    rw [pow_succ, show k + k = 2 * k from by ring, pow_mul, Complex.I_sq]
  rw [this]
  rcases Nat.even_or_odd k with he | ho
  · rw [he.neg_one_pow]; simp
  · rw [ho.neg_one_pow]; simp

/-- The feature's mean under a law on `ℝ`. -/
noncomputable def featMean (j : ℕ) (μ : Measure ℝ) : ℝ := ∫ y, feat j y ∂μ

theorem featMean_eq (j : ℕ) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    featMean j μ = if Even j then (charFun μ 1).im else (charFun μ 1).re := by
  unfold featMean feat
  split_ifs
  · exact mean_sin_eq μ
  · exact mean_cos_eq μ

/-- **The gap the decoder sees, exactly.** -/
theorem feature_gap_abs (j : ℕ) (h : ℝ) (σ2 : ℝ≥0) :
    |featMean j (obsLaw j 1 h σ2) - featMean j (obsLaw j (-1) h σ2)|
      = 2 * Real.sin 1 * |Real.sin (1 * h / j)| ^ j * Real.exp (-((σ2 : ℝ) * 1 ^ 2 / 2)) := by
  have hd := parity_obs_cf_difference j h σ2 1
  rw [featMean_eq, featMean_eq]
  have hsin1 : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [pi_gt_three])
  -- the real factor multiplying i^(j+1)
  set A : ℝ := 2 * Real.sin 1 * Real.sin (1 * h / j) ^ j * Real.exp (-((σ2 : ℝ) * 1 ^ 2 / 2))
    with hA
  have hform : charFun (obsLaw j 1 h σ2) 1 - charFun (obsLaw j (-1) h σ2) 1
      = (A : ℂ) * Complex.I ^ (j + 1) := by
    rw [hd, hA]
    push_cast
    ring
  have habsA : |A| = 2 * Real.sin 1 * |Real.sin (1 * h / j)| ^ j
      * Real.exp (-((σ2 : ℝ) * 1 ^ 2 / 2)) := by
    rw [hA, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _),
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hsin1]
  split_ifs with hj
  · obtain ⟨hre, him⟩ := I_pow_even j hj
    have := congrArg Complex.im hform
    rw [Complex.sub_im, Complex.im_ofReal_mul] at this
    rw [this, abs_mul, him, mul_one, habsA]
  · obtain ⟨hre, him⟩ := I_pow_odd j hj
    have := congrArg Complex.re hform
    rw [Complex.sub_re, Complex.re_ofReal_mul] at this
    rw [this, abs_mul, hre, mul_one, habsA]

/-- **The gap is of order `h^j`**, with an explicit constant, for `0 < h <= j`. -/
theorem feature_gap_lower (j : ℕ) (hj : 0 < j) (h : ℝ) (hh : 0 < h) (hhj : h ≤ j) (σ2 : ℝ≥0) :
    2 * Real.sin 1 * (3 / (4 * (j : ℝ))) ^ j * h ^ j * Real.exp (-((σ2 : ℝ) / 2))
      ≤ |featMean j (obsLaw j 1 h σ2) - featMean j (obsLaw j (-1) h σ2)| := by
  rw [feature_gap_abs]
  have hsin1 : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [pi_gt_three])
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hsmall : 1 * h / (j : ℝ) ≤ 1 := by rw [one_mul, div_le_one hjR]; exact hhj
  have hord := parity_gap_order j hj 1 h one_pos hh hsmall
  have hsinnn : 0 ≤ Real.sin (1 * h / j) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
    linarith [pi_gt_three]
  rw [abs_of_nonneg hsinnn]
  have hexp : Real.exp (-((σ2 : ℝ) * 1 ^ 2 / 2)) = Real.exp (-((σ2 : ℝ) / 2)) := by
    congr 1; ring
  rw [hexp]
  have hlhs : (3 * 1 / (4 * (j : ℝ))) ^ j * h ^ j = (3 / (4 * (j : ℝ))) ^ j * h ^ j := by
    congr 2; ring
  rw [hlhs] at hord
  have hpos : 0 ≤ 2 * Real.sin 1 := by positivity
  calc 2 * Real.sin 1 * (3 / (4 * (j : ℝ))) ^ j * h ^ j * Real.exp (-((σ2 : ℝ) / 2))
      = 2 * Real.sin 1 * ((3 / (4 * (j : ℝ))) ^ j * h ^ j) * Real.exp (-((σ2 : ℝ) / 2)) := by
        ring
    _ ≤ 2 * Real.sin 1 * Real.sin (1 * h / j) ^ j * Real.exp (-((σ2 : ℝ) / 2)) := by
        gcongr

#print axioms mean_cos_eq
#print axioms mean_sin_eq
#print axioms feature_gap_abs
#print axioms feature_gap_lower

end CIGAMF.P13.PaperBParityGap
