import «LeanPaperBParityLawV1»
import «LeanPaperBPairRateV1»
import «LeanPaperBChiSqV1»

/-!
# Paper B: the per-query chi-square of the parity channel, from its actual density

`LeanPaperBChiSqV1` reduces the round's conditional divergence to per-query chi-squares.
This module computes those for the parity-membership query of `LeanPaperBParityLawV1`, on
the observation law's OWN density, with no hypothesis about the density difference:

1. `pdens` is the density of `obsLaw` (`obsLaw_eq_withDensity`), so the lower bound below
   and the decoder's characteristic function concern the SAME law;
2. `pdens = Zc⁻¹ * chanDens gkern b` with `b_i = h/j` (`pdens_eq_chanDens`): the corpus's
   channel density at the normalised Gaussian;
3. `channel_pair_diff` makes the two mask values' difference an iterated symmetric difference
   of `pairBase gkern`, and `pair_envelope` bounds it by `2 (h/j)^j envUp`;
4. every component's centre lies within `1 + h` of the origin, so both densities sit above
   `Zc⁻¹ envLo` (`pdens_floor`);
5. hence, for either ordering of the two mask values,

       ∫⁻ (p_v - p_v')^2 / p_v'  <=  parC j sigma h0 * h^(2j),   0 <= h <= h0,

   with `parC` explicit and independent of `h` (`parity_chiSq_le`).

The order `h^(2j)` is the query's resolving order; the constant depends on the fixed `j`,
`sigma` and `h0`, not on `h`.
-/

namespace CIGAMF.P13.PaperBParityChiSq

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBWorlds CIGAMF.P13.PaperBChannelPair
open CIGAMF.P13.PaperBPairRate CIGAMF.P13.PaperBParityLaw

/-! ## 1. The density, in the corpus's channel coordinates -/

/-- The noise variance as the `ℝ≥0` Mathlib's Gaussian takes. -/
def var2 (σ : ℝ) : ℝ≥0 := ⟨σ ^ 2, sq_nonneg σ⟩

/-- The Gaussian's normalising constant. -/
noncomputable def Zc (σ : ℝ) : ℝ := Real.sqrt (2 * π * σ ^ 2)

theorem Zc_pos (σ : ℝ) (hσ : 0 < σ) : 0 < Zc σ := Real.sqrt_pos.mpr (by positivity)

theorem var2_ne_zero (σ : ℝ) (hσ : 0 < σ) : var2 σ ≠ 0 := by
  intro h
  have : (σ ^ 2 : ℝ) = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  have : 0 < σ ^ 2 := by positivity
  linarith

theorem var2_coe (σ : ℝ) : ((var2 σ : ℝ≥0) : ℝ) = σ ^ 2 := rfl

theorem gaussianPDFReal_eq (μ σ y : ℝ) :
    gaussianPDFReal μ (var2 σ) y = (Zc σ)⁻¹ * gkern σ (y - μ) := by
  rw [gaussianPDFReal, var2_coe]
  rfl

/-- **The density of the parity query's observation law.** -/
noncomputable def pdens (j : ℕ) (v h σ y : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ ^ j * ∑ z : Fin j → Bool, gaussianPDFReal (obsMean j v h z) (var2 σ) y

/-- The coordinate step of the channel: every coordinate moves by `h / j`. -/
noncomputable def bvec (j : ℕ) (h : ℝ) : Fin j → ℝ := fun _ => h / j

theorem sgnR_eq_sgnB (b : Bool) : sgnR b = sgnB b := by cases b <;> rfl

theorem obsMean_eq (j : ℕ) (v h : ℝ) (z : Fin j → Bool) :
    obsMean j v h z = v * parity z + shiftOf (bvec j h) z := by
  unfold obsMean chrR csumR parity shiftOf bvec
  simp only [sgnR_eq_sgnB]
  rw [Finset.mul_sum]

theorem pdens_eq_chanDens (j : ℕ) (v h σ y : ℝ) :
    pdens j v h σ y = (Zc σ)⁻¹ * chanDens (gkern σ) (bvec j h) v y := by
  have hterm : ∀ z : Fin j → Bool, gaussianPDFReal (obsMean j v h z) (var2 σ) y
      = (Zc σ)⁻¹ * gkern σ (y - v * parity z - shiftOf (bvec j h) z) := by
    intro z
    rw [gaussianPDFReal_eq, obsMean_eq, sub_add_eq_sub_sub]
  unfold pdens chanDens
  rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.mul_sum]
  ring

theorem gkern_eq_mix (σ : ℝ) : gkern σ = mixDens σ 1 (fun _ => 1) (fun _ => 0) := by
  funext y
  simp [mixDens]

/-- **The two mask values' density difference, as the corpus's iterated difference.** -/
theorem pdens_diff (j : ℕ) (h σ y : ℝ) :
    pdens j 1 h σ y - pdens j (-1) h σ y
      = (Zc σ)⁻¹ * iterDiff (pairBase (mixDens σ 1 (fun _ => 1) (fun _ => 0)))
          (List.ofFn (bvec j h)) y := by
  rw [pdens_eq_chanDens, pdens_eq_chanDens, ← mul_sub, channel_pair_diff, gkern_eq_mix]

theorem sum_abs_bvec (j : ℕ) (hj : 0 < j) (h : ℝ) (hh : 0 ≤ h) :
    ∑ i, |bvec j h i| = h := by
  unfold bvec
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    abs_of_nonneg (div_nonneg hh (Nat.cast_nonneg j))]
  have : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  field_simp

theorem prod_abs_bvec (j : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    ∏ i, |bvec j h i| = (h / j) ^ j := by
  unfold bvec
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    abs_of_nonneg (div_nonneg hh (Nat.cast_nonneg j))]

/-! ## 2. The envelope and the floor -/

theorem diff_envelope (j : ℕ) (hj : 0 < j) (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h)
    (hhh : h ≤ h₀) (y : ℝ) :
    |iterDiff (pairBase (mixDens σ 1 (fun _ => 1) (fun _ => 0))) (List.ofFn (bvec j h)) y|
      ≤ 2 * ((h / j) ^ j * envUp σ (0 + 1 + h₀) j y) := by
  have h₀nn : 0 ≤ h₀ := hh.trans hhh
  have := pair_envelope σ 0 h₀ hσ le_rfl h₀nn j 1 (fun _ => 1) (fun _ => zero_le_one)
    (by simp) (fun _ => 0) (fun _ => by simp) (bvec j h)
    (by rw [sum_abs_bvec j hj h hh]; exact hhh) y
  rwa [prod_abs_bvec j h hh] at this

/-- **Both densities sit above the envelope floor**, for either mask value. -/
theorem pdens_floor (j : ℕ) (hj : 0 < j) (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h)
    (hhh : h ≤ h₀) (v : ℝ) (hv : v = 1 ∨ v = -1) (y : ℝ) :
    (Zc σ)⁻¹ * envLo σ (0 + 1 + h₀) y ≤ pdens j v h σ y := by
  rw [pdens_eq_chanDens]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Zc_pos σ hσ).le)
  unfold chanDens
  have hterm : ∀ z : Fin j → Bool,
      envLo σ (0 + 1 + h₀) y ≤ gkern σ (y - v * parity z - shiftOf (bvec j h) z) := by
    intro z
    have hc : |v * parity z + shiftOf (bvec j h) z| ≤ 0 + 1 + h₀ := by
      have hp : |v * parity z| = 1 := by
        rw [abs_mul, parity_abs z]
        rcases hv with rfl | rfl <;> norm_num
      have hs : |shiftOf (bvec j h) z| ≤ h := by
        have := abs_shiftOf_le (bvec j h) z
        rwa [sum_abs_bvec j hj h hh] at this
      calc |v * parity z + shiftOf (bvec j h) z|
          ≤ |v * parity z| + |shiftOf (bvec j h) z| := abs_add_le _ _
        _ ≤ 0 + 1 + h₀ := by linarith
    have := gaussian_lower_envelope σ (0 + 1 + h₀) y (v * parity z + shiftOf (bvec j h) z)
      hσ hc
    rw [show y - (v * parity z + shiftOf (bvec j h) z)
        = y - v * parity z - shiftOf (bvec j h) z from by ring] at this
    exact this
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hterm z)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have h2 : (2 : ℝ)⁻¹ ^ j * ((2 ^ j : ℕ) : ℝ) = 1 := by
    push_cast
    rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
  calc envLo σ (0 + 1 + h₀) y = (2 : ℝ)⁻¹ ^ j * ((2 ^ j : ℕ) : ℝ) * envLo σ (0 + 1 + h₀) y := by
        rw [h2, one_mul]
    _ ≤ (2 : ℝ)⁻¹ ^ j * ∑ z : Fin j → Bool,
          gkern σ (y - v * parity z - shiftOf (bvec j h) z) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem pdens_pos (j : ℕ) (hj : 0 < j) (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h) (hhh : h ≤ h₀)
    (v : ℝ) (hv : v = 1 ∨ v = -1) (y : ℝ) : 0 < pdens j v h σ y :=
  lt_of_lt_of_le (mul_pos (inv_pos.mpr (Zc_pos σ hσ)) (envLo_pos _ _ _))
    (pdens_floor j hj σ h h₀ hσ hh hhh v hv y)

/-! ## 3. The chi-square bound -/

/-- The query-independent constant: fixed `j`, `sigma` and `h0`, no `h`. -/
noncomputable def parC (j : ℕ) (σ h₀ : ℝ) : ℝ :=
  4 * ((1 / (j : ℝ)) ^ j) ^ 2 / Zc σ *
    ∫ y, envUp σ (0 + 1 + h₀) j y ^ 2 / envLo σ (0 + 1 + h₀) y

theorem parC_nonneg (j : ℕ) (σ h₀ : ℝ) (hσ : 0 < σ) : 0 ≤ parC j σ h₀ := by
  unfold parC
  exact mul_nonneg (div_nonneg (by positivity) (Zc_pos σ hσ).le)
    (envRatio_integral_nonneg σ _ j)

/-- **The per-query chi-square, for either ordering of the two mask values.** -/
theorem parity_chiSq_le (j : ℕ) (hj : 0 < j) (σ h h₀ : ℝ) (hσ : 0 < σ) (hh : 0 ≤ h)
    (hhh : h ≤ h₀) (v v' : ℝ) (hv : v = 1 ∨ v = -1) (hv' : v' = 1 ∨ v' = -1) :
    ∫⁻ y, ENNReal.ofReal ((pdens j v h σ y - pdens j v' h σ y) ^ 2 / pdens j v' h σ y)
      ≤ ENNReal.ofReal (parC j σ h₀ * h ^ (2 * j)) := by
  have h₀nn : 0 ≤ h₀ := hh.trans hhh
  have hZ := Zc_pos σ hσ
  set K : ℝ := 4 * ((h / j) ^ j) ^ 2 / Zc σ with hK
  have hKnn : 0 ≤ K := by rw [hK]; positivity
  -- the squared difference is the same for either ordering
  have hsq : ∀ y, (pdens j v h σ y - pdens j v' h σ y) ^ 2
      ≤ ((Zc σ)⁻¹ * (2 * ((h / j) ^ j * envUp σ (0 + 1 + h₀) j y))) ^ 2 := by
    intro y
    have hd := diff_envelope j hj σ h h₀ hσ hh hhh y
    have hE : 0 ≤ 2 * ((h / j) ^ j * envUp σ (0 + 1 + h₀) j y) :=
      mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg (div_nonneg hh (Nat.cast_nonneg j)) j)
        (envUp_nonneg σ _ j y (by linarith)))
    have habs : |pdens j v h σ y - pdens j v' h σ y|
        ≤ (Zc σ)⁻¹ * (2 * ((h / j) ^ j * envUp σ (0 + 1 + h₀) j y)) := by
      rcases hv with rfl | rfl <;> rcases hv' with rfl | rfl
      · simp only [sub_self, abs_zero]; positivity
      · rw [pdens_diff, abs_mul, abs_of_pos (inv_pos.mpr hZ)]
        exact mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hZ.le)
      · rw [abs_sub_comm, pdens_diff, abs_mul, abs_of_pos (inv_pos.mpr hZ)]
        exact mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hZ.le)
      · simp only [sub_self, abs_zero]; positivity
    calc (pdens j v h σ y - pdens j v' h σ y) ^ 2 = |pdens j v h σ y - pdens j v' h σ y| ^ 2 :=
          (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) habs 2
  -- pointwise domination by an integrable envelope ratio
  have hpt : ∀ y, (pdens j v h σ y - pdens j v' h σ y) ^ 2 / pdens j v' h σ y
      ≤ K * (envUp σ (0 + 1 + h₀) j y ^ 2 / envLo σ (0 + 1 + h₀) y) := by
    intro y
    have hlo := envLo_pos σ (0 + 1 + h₀) y
    have hfl := pdens_floor j hj σ h h₀ hσ hh hhh v' hv' y
    have hflpos : 0 < (Zc σ)⁻¹ * envLo σ (0 + 1 + h₀) y := mul_pos (inv_pos.mpr hZ) hlo
    calc (pdens j v h σ y - pdens j v' h σ y) ^ 2 / pdens j v' h σ y
        ≤ ((Zc σ)⁻¹ * (2 * ((h / j) ^ j * envUp σ (0 + 1 + h₀) j y))) ^ 2
            / ((Zc σ)⁻¹ * envLo σ (0 + 1 + h₀) y) :=
          div_le_div₀ (sq_nonneg _) (hsq y) hflpos hfl
      _ = K * (envUp σ (0 + 1 + h₀) j y ^ 2 / envLo σ (0 + 1 + h₀) y) := by
          rw [hK]
          field_simp
          ring
  have hint : Integrable (fun y => K * (envUp σ (0 + 1 + h₀) j y ^ 2
      / envLo σ (0 + 1 + h₀) y)) :=
    (envRatio_integrable σ (0 + 1 + h₀) hσ (by linarith) j).const_mul K
  have hnn : 0 ≤ᵐ[volume] fun y => K * (envUp σ (0 + 1 + h₀) j y ^ 2
      / envLo σ (0 + 1 + h₀) y) :=
    Filter.Eventually.of_forall fun y =>
      mul_nonneg hKnn (div_nonneg (sq_nonneg _) (envLo_pos _ _ _).le)
  calc ∫⁻ y, ENNReal.ofReal ((pdens j v h σ y - pdens j v' h σ y) ^ 2 / pdens j v' h σ y)
      ≤ ∫⁻ y, ENNReal.ofReal (K * (envUp σ (0 + 1 + h₀) j y ^ 2
          / envLo σ (0 + 1 + h₀) y)) :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hpt y)
    _ = ENNReal.ofReal (∫ y, K * (envUp σ (0 + 1 + h₀) j y ^ 2
          / envLo σ (0 + 1 + h₀) y)) :=
        (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    _ = ENNReal.ofReal (parC j σ h₀ * h ^ (2 * j)) := by
        have hpow : ((h / j) ^ j) ^ 2 = ((1 / (j : ℝ)) ^ j) ^ 2 * h ^ (2 * j) := by
          rw [div_eq_mul_one_div h]
          ring
        rw [integral_const_mul]
        congr 1
        unfold parC
        rw [hK, hpow]
        ring

/-! ## 4. The density is the observation law's, and it is a probability density -/

theorem pdens_nonneg (j : ℕ) (v h σ y : ℝ) : 0 ≤ pdens j v h σ y := by
  unfold pdens
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun z _ => gaussianPDFReal_nonneg _ _ _)

theorem continuous_pdens (j : ℕ) (v h σ : ℝ) : Continuous (pdens j v h σ) := by
  unfold pdens gaussianPDFReal
  fun_prop

/-- **The parity query's law has density `pdens`.**  So the lower bound (through the
density) and the decoder (through `charFun_obsLaw`) are about the same law. -/
theorem obsLaw_eq_withDensity (j : ℕ) (v h σ : ℝ) (hσ : 0 < σ) :
    obsLaw j v h (var2 σ) = volume.withDensity (fun y => ENNReal.ofReal (pdens j v h σ y)) := by
  have hv := var2_ne_zero σ hσ
  have hc : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j) = ((2 : ℝ≥0∞) ^ j)⁻¹ := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  have hpt : ∀ y, ENNReal.ofReal (pdens j v h σ y)
      = ∑ z : Fin j → Bool, ((2 : ℝ≥0∞) ^ j)⁻¹ * gaussianPDF (obsMean j v h z) (var2 σ) y := by
    intro y
    unfold pdens gaussianPDF
    rw [ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun z _ => gaussianPDFReal_nonneg _ _ _), hc,
      Finset.mul_sum]
  ext s hs
  rw [withDensity_apply _ hs]
  simp_rw [hpt]
  unfold obsLaw
  rw [Measure.coe_finset_sum, Finset.sum_apply,
    lintegral_finset_sum _ (fun z _ => (measurable_gaussianPDF _ _).const_mul _)]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, lintegral_const_mul _ (measurable_gaussianPDF _ _),
    gaussianReal_apply _ hv]

theorem lintegral_pdens (j : ℕ) (v h σ : ℝ) (hσ : 0 < σ) :
    ∫⁻ y, ENNReal.ofReal (pdens j v h σ y) = 1 := by
  have hu := obsLaw_univ j v h (var2 σ)
  rw [obsLaw_eq_withDensity j v h σ hσ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at hu
  exact hu

#print axioms pdens_eq_chanDens
#print axioms pdens_diff
#print axioms pdens_floor
#print axioms parity_chiSq_le
#print axioms obsLaw_eq_withDensity
#print axioms lintegral_pdens

end CIGAMF.P13.PaperBParityChiSq
