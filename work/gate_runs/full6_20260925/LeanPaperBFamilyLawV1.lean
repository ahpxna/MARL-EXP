import «LeanPaperBFamilyChannelV1»
import «LeanPaperBParityGapV1»

/-!
# Paper B: the latent family's observation law, its characteristic function, and the gaps

The decoders of the latent family read bounded features of the observation, `cos Y` or `sin Y`,
whose means are read off the characteristic function at `t = 1`.  This module computes them.

* `famLaw`: the observation law of a probe, the uniform mixture of `N(mean(p), sigma^2)` over the
  `8 * 2^r` latent patterns; `famLaw_eq_withDensity` identifies it with the channel's density,
  so `obsLawC (famChan ..) w q = famLaw ..` (`obsLawC_famChan`).
* `charFun_famLaw`: the characteristic function factorises as (head factor) x (tail sum) x
  (Gaussian factor), because the head and tail patterns are independent.
* `head_factor`: the head factor is `cos(t a_0) cos(t a_1) cos(t a_2)`, where
  `a = (3u + h aH_0, -2 + h aH_1, -2 + h aH_2)` are the head coefficients.
* The decision probe `z_1`: `E cos Y = cos(3u + h) cos^2 2 cos 1 exp(-sigma^2/2)`.  It depends on
  `u` and not on `v` (`decMean_eq`), and its gap is at least `G_dec h` for `0 < h <= 1`
  (`dec_gap_lower`).
* The tail probe `(1/r) sum z_tail`: `E feat_r Y = cos 3 cos^2 2 * featMean_r(obsLaw r v h)`.  It
  depends on `v` and not on `u` (`tailMean_eq`), and its gap is at least `G_tail h^r` for
  `0 < h <= min 1 r` (`tail_gap_lower`), from the parity channel's `feature_gap_lower`.
-/

namespace CIGAMF.P13.PaperBFamilyLaw

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBWorlds CIGAMF.P13.PaperBChannelPair
open CIGAMF.P13.PaperBParityChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration
open CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityGap CIGAMF.P13.PaperBFamilyChannel

/-! ## 1. The law -/

/-- The weight of one latent pattern. -/
noncomputable def famW (r : ℕ) : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 3)⁻¹ * ((2 : ℝ≥0∞) ^ r)⁻¹

/-- The conditional mean at a latent pattern. -/
noncomputable def famMean {r : ℕ} (h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ)
    (p : (Fin 3 → Bool) × (Fin r → Bool)) : ℝ :=
  headC u h aH p.1 + v * parity p.2 + shiftOf (tailB h aT) p.2

/-- **The observation law of a probe.** -/
noncomputable def famLaw {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) : Measure ℝ :=
  ∑ p : (Fin 3 → Bool) × (Fin r → Bool), famW r • gaussianReal (famMean h u v aH aT p) (var2 σ)

theorem famW_toReal (r : ℕ) : (famW r).toReal = (2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r := by
  unfold famW
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_pow,
    ENNReal.toReal_pow]
  simp

theorem famW_ne_top (r : ℕ) : famW r ≠ ⊤ := by
  unfold famW
  exact ENNReal.mul_ne_top (by simp) (by simp)

theorem ofReal_famW (r : ℕ) : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r) = famW r := by
  rw [← famW_toReal, ENNReal.ofReal_toReal (famW_ne_top r)]

theorem famLaw_eq_withDensity {r : ℕ} (σ h u v : ℝ) (hσ : 0 < σ) (aH : Fin 3 → ℝ)
    (aT : Fin r → ℝ) :
    famLaw σ h u v aH aT
      = volume.withDensity (fun y => ENNReal.ofReal (famDens σ h u v aH aT y)) := by
  have hv := var2_ne_zero σ hσ
  have hpt : ∀ y, ENNReal.ofReal (famDens σ h u v aH aT y)
      = ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
          famW r * gaussianPDF (famMean h u v aH aT p) (var2 σ) y := by
    intro y
    have hexp : famDens σ h u v aH aT y = ∑ p : (Fin 3 → Bool) × (Fin r → Bool),
        ((2 : ℝ)⁻¹ ^ 3 * (2 : ℝ)⁻¹ ^ r) * gaussianPDFReal (famMean h u v aH aT p) (var2 σ) y := by
      unfold famDens famMean
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun zh _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    rw [hexp, ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (by positivity)
      (gaussianPDFReal_nonneg _ _ _))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ENNReal.ofReal_mul (by positivity), ofReal_famW]
    rfl
  ext s hs
  rw [withDensity_apply _ hs]
  simp_rw [hpt]
  unfold famLaw
  rw [Measure.coe_finset_sum, Finset.sum_apply,
    lintegral_finset_sum _ (fun p _ => (measurable_gaussianPDF _ _).const_mul _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, lintegral_const_mul _ (measurable_gaussianPDF _ _),
    gaussianReal_apply _ hv]

theorem famLaw_univ {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) :
    famLaw σ h u v aH aT Set.univ = 1 := by
  unfold famLaw
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  unfold famW
  rw [mul_mul_mul_comm, ENNReal.mul_inv_cancel (by simp) (by simp),
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

instance {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) :
    IsProbabilityMeasure (famLaw σ h u v aH aT) := ⟨famLaw_univ σ h u v aH aT⟩

/-- **The channel's observation law of a real probe is the family's law.** -/
theorem obsLawC_famChan {r k : ℕ} (σ h : ℝ) (hσ : 0 < σ) (aH : Fin (k + 1) → Fin 3 → ℝ)
    (aT : Fin (k + 1) → Fin r → ℝ) (w : Bool × Bool) (q : Fin (k + 1)) (hq : (q : ℕ) ≠ 0) :
    obsLawC (famChan σ h hσ aH aT) w q = famLaw σ h (uOf w) (vOf w) (aH q) (aT q) := by
  rw [famLaw_eq_withDensity σ h _ _ hσ]
  unfold obsLawC
  congr 1
  funext y
  show ENNReal.ofReal (famChanDens σ h aH aT w q y) = _
  unfold famChanDens
  rw [if_neg hq]

/-! ## 2. The characteristic function factorises -/

theorem charFun_famLaw {r : ℕ} (σ h u v : ℝ) (aH : Fin 3 → ℝ) (aT : Fin r → ℝ) (t : ℝ) :
    charFun (famLaw σ h u v aH aT) t
      = (∑ zh : Fin 3 → Bool, ((2 : ℂ) ^ 3)⁻¹
            * Complex.exp ((t : ℂ) * ((headC u h aH zh : ℝ) : ℂ) * Complex.I))
        * (∑ z : Fin r → Bool, ((2 : ℂ) ^ r)⁻¹
            * Complex.exp ((t : ℂ) * ((v * parity z + shiftOf (tailB h aT) z : ℝ) : ℂ)
                * Complex.I))
        * Complex.exp (((-(σ ^ 2 * t ^ 2 / 2) : ℝ) : ℂ)) := by
  unfold famLaw
  rw [charFun_mixture _ (fun _ => famW_ne_top r) _ t, Fintype.sum_prod_type, Finset.sum_mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun zh _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [charFun_gaussianReal, famW_toReal]
  unfold famMean
  rw [var2_coe]
  have hsplit : ((t : ℂ) * ((headC u h aH zh + v * parity z + shiftOf (tailB h aT) z : ℝ) : ℂ)
      * Complex.I - ((σ ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)
      = (t : ℂ) * ((headC u h aH zh : ℝ) : ℂ) * Complex.I
        + (t : ℂ) * ((v * parity z + shiftOf (tailB h aT) z : ℝ) : ℂ) * Complex.I
        + (((-(σ ^ 2 * t ^ 2 / 2) : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_add]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_ofNat,
    ← inv_pow]
  ring

/-- The head factor is a product of cosines. -/
theorem head_factor (t : ℝ) (α : Fin 3 → ℝ) :
    ∑ zh : Fin 3 → Bool, ((2 : ℂ) ^ 3)⁻¹
        * Complex.exp (t * (∑ i, α i * sgnB (zh i)) * Complex.I)
      = ((Real.cos (t * α 0) * Real.cos (t * α 1) * Real.cos (t * α 2) : ℝ) : ℂ) := by
  have hprod : ∀ zh : Fin 3 → Bool, ((2 : ℂ) ^ 3)⁻¹
      * Complex.exp (t * (∑ i, α i * sgnB (zh i)) * Complex.I)
      = ∏ i, ((2 : ℂ)⁻¹ * Complex.exp (t * α i * sgnB (zh i) * Complex.I)) := by
    intro zh
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Complex.exp_sum, inv_pow]
    congr 2
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun i b => (2 : ℂ)⁻¹ * Complex.exp (t * α i * sgnB b * Complex.I))]
  rw [Fin.prod_univ_three]
  have hc : ∀ a : ℝ, ∑ b : Bool, (2 : ℂ)⁻¹ * Complex.exp (t * a * sgnB b * Complex.I)
      = (Real.cos (t * a) : ℂ) := by
    intro a
    rw [Fintype.sum_bool]
    simp only [sgnB, if_true, Bool.false_eq_true, if_false]
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [hc, hc, hc]
  push_cast
  ring

theorem headC_as_sum (u h : ℝ) (aH : Fin 3 → ℝ) (zh : Fin 3 → Bool) :
    headC u h aH zh = ∑ i, ![3 * u + h * aH 0, -2 + h * aH 1, -2 + h * aH 2] i * sgnB (zh i) := by
  unfold headC
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-! ## 3. The two probes the decoders use -/

/-- The decision probe `z_1`. -/
def decH : Fin 3 → ℝ := ![1, 0, 0]
def decT (r : ℕ) : Fin r → ℝ := fun _ => 0

/-- The tail probe `(1/r) sum z_tail`. -/
def tailH : Fin 3 → ℝ := ![0, 0, 0]
noncomputable def tailT (r : ℕ) : Fin r → ℝ := fun _ => 1 / (r : ℝ)

theorem decNorm (r : ℕ) : ∑ i, |decH i| + ∑ i, |decT r i| ≤ 1 := by
  simp [decH, decT, Fin.sum_univ_three]

theorem tailNorm (r : ℕ) (hr : 0 < r) : ∑ i, |tailH i| + ∑ i, |tailT r i| ≤ 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  simp only [tailH, tailT, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, abs_zero, add_zero, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    abs_of_pos (one_div_pos.mpr hrR)]
  rw [mul_one_div_cancel hrR.ne']


theorem re_real_mul (K G : ℝ) (T : ℂ) : ((K : ℂ) * T * (G : ℂ)).re = K * T.re * G := by
  simp [Complex.mul_re]

theorem im_real_mul (K G : ℝ) (T : ℂ) : ((K : ℂ) * T * (G : ℂ)).im = K * T.im * G := by
  simp [Complex.mul_im]

theorem cos_pm (u c : ℝ) (hu : u = 1 ∨ u = -1) : Real.cos (c * u) = Real.cos c := by
  rcases hu with rfl | rfl <;> simp [Real.cos_neg]

theorem parity_pm {r : ℕ} (z : Fin r → Bool) : parity z = 1 ∨ parity z = -1 := by
  have := parity_abs z
  rcases abs_eq zero_le_one |>.mp this with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- The decision probe's tail sum has real part `cos 1`, whatever `v`. -/
theorem dec_tail_re {r : ℕ} (h v : ℝ) (hv : v = 1 ∨ v = -1) :
    (∑ z : Fin r → Bool, ((2 : ℂ) ^ r)⁻¹ * Complex.exp (((1 : ℝ) : ℂ)
        * ((v * parity z + shiftOf (tailB h (decT r)) z : ℝ) : ℂ) * Complex.I)).re
      = Real.cos 1 := by
  have hshift : ∀ z : Fin r → Bool, shiftOf (tailB h (decT r)) z = 0 := by
    intro z; unfold shiftOf tailB decT; simp
  have hterm : ∀ z : Fin r → Bool, (((2 : ℂ) ^ r)⁻¹ * Complex.exp (((1 : ℝ) : ℂ)
      * ((v * parity z + shiftOf (tailB h (decT r)) z : ℝ) : ℂ) * Complex.I)).re
      = ((2 : ℝ) ^ r)⁻¹ * Real.cos 1 := by
    intro z
    rw [hshift, add_zero, show ((2 : ℂ) ^ r)⁻¹ = (((2 : ℝ) ^ r)⁻¹ : ℝ) by push_cast; rfl,
      Complex.re_ofReal_mul, show ((1 : ℝ) : ℂ) * ((v * parity z : ℝ) : ℂ) * Complex.I
        = ((v * parity z : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I_re]
    congr 1
    rcases parity_pm z with hp | hp <;> rw [hp] <;> rcases hv with rfl | rfl <;>
      simp [Real.cos_neg]
  rw [Complex.re_sum]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **The decision probe's cosine mean**, for `u, v = +-1`: it depends on `u` only. -/
theorem decMean_eq {r : ℕ} (σ h u v : ℝ) (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    ∫ y, Real.cos y ∂famLaw σ h u v decH (decT r)
      = Real.cos (3 * u + h) * Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2)) := by
  rw [mean_cos_eq, charFun_famLaw]
  have hhead : ∑ zh : Fin 3 → Bool, ((2 : ℂ) ^ 3)⁻¹
      * Complex.exp (((1 : ℝ) : ℂ) * ((headC u h decH zh : ℝ) : ℂ) * Complex.I)
      = ((Real.cos (3 * u + h) * Real.cos 2 ^ 2 : ℝ) : ℂ) := by
    simp_rw [headC_as_sum]
    rw [head_factor]
    congr 1
    simp only [decH, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, mul_one, mul_zero, add_zero, one_mul]
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.cos_neg]
    ring
  rw [hhead, ← Complex.ofReal_exp, re_real_mul, dec_tail_re h v hv]
  congr 2
  ring

/-- **The decision gap**: at least `(3/2) sin 3 cos^2 2 cos 1 exp(-sigma^2/2) h` for
`0 < h <= 1`. -/
theorem dec_gap_lower {r : ℕ} (σ h v : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hv : v = 1 ∨ v = -1) :
    3 / 2 * Real.sin 3 * Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2)) * h
      ≤ |∫ y, Real.cos y ∂famLaw σ h 1 v decH (decT r)
          - ∫ y, Real.cos y ∂famLaw σ h (-1) v decH (decT r)| := by
  rw [decMean_eq σ h 1 v (Or.inl rfl) hv, decMean_eq σ h (-1) v (Or.inr rfl) hv]
  have hcs := Real.cos_sub_cos (3 * 1 + h) (3 * (-1) + h)
  rw [show (3 * 1 + h + (3 * (-1) + h)) / 2 = h by ring,
    show (3 * 1 + h - (3 * (-1) + h)) / 2 = 3 by ring] at hcs
  have hdiff : Real.cos (3 * 1 + h) * Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2))
      - Real.cos (3 * (-1) + h) * Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2))
      = -(2 * Real.sin h * Real.sin 3) * (Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2))) := by
    calc _ = (Real.cos (3 * 1 + h) - Real.cos (3 * (-1) + h))
          * (Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2))) := by ring
      _ = _ := by rw [hcs]; ring
  rw [hdiff]
  have hs3 : 0 < Real.sin 3 := Real.sin_pos_of_pos_of_lt_pi (by norm_num) pi_gt_three
  have hc1 : 0 < Real.cos 1 := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_gt_three],
    by linarith [pi_gt_three]⟩
  have hsh : 3 * h / 4 ≤ Real.sin h := CIGAMF.P13.PaperBAttain.sin_lower_small h hh hh1
  have hE : 0 < Real.exp (-(σ ^ 2 / 2)) := Real.exp_pos _
  have hC : 0 ≤ Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2)) := by positivity
  rw [abs_mul, abs_neg, abs_of_nonneg hC, abs_of_nonneg (by nlinarith [hs3, hsh, hh])]
  nlinarith [mul_le_mul_of_nonneg_right hsh (mul_nonneg hs3.le hC), hs3, hC]

/-- The parity observation law's characteristic function, split as a tail sum and a Gaussian
factor. -/
theorem charFun_obsLaw_split (r : ℕ) (v h : ℝ) (σ : ℝ) (t : ℝ) :
    charFun (obsLaw r v h (var2 σ)) t
      = (∑ z : Fin r → Bool, ((2 : ℂ) ^ r)⁻¹
          * Complex.exp ((t : ℂ) * ((obsMean r v h z : ℝ) : ℂ) * Complex.I))
        * Complex.exp (((-(σ ^ 2 * t ^ 2 / 2) : ℝ) : ℂ)) := by
  unfold obsLaw
  rw [charFun_mixture _ (fun _ => by simp) _ t, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [charFun_gaussianReal, weight_toReal, var2_coe, sub_eq_add_neg, Complex.exp_add]
  push_cast
  ring

theorem tail_obsMean (r : ℕ) (h v : ℝ) (z : Fin r → Bool) :
    v * parity z + shiftOf (tailB h (tailT r)) z = obsMean r v h z := by
  rw [obsMean_eq]
  congr 1
  unfold shiftOf tailB tailT bvec
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The tail probe's feature mean**: `cos 3 cos^2 2` times the parity channel's, so it
depends on `v` only. -/
theorem tailMean_eq {r : ℕ} (σ h u v : ℝ) (hu : u = 1 ∨ u = -1) :
    featMean r (famLaw σ h u v tailH (tailT r))
      = Real.cos 3 * Real.cos 2 ^ 2 * featMean r (obsLaw r v h (var2 σ)) := by
  have hcf : charFun (famLaw σ h u v tailH (tailT r)) 1
      = ((Real.cos 3 * Real.cos 2 ^ 2 : ℝ) : ℂ) * charFun (obsLaw r v h (var2 σ)) 1 := by
    rw [charFun_famLaw, charFun_obsLaw_split]
    have hhead : ∑ zh : Fin 3 → Bool, ((2 : ℂ) ^ 3)⁻¹
        * Complex.exp (((1 : ℝ) : ℂ) * ((headC u h tailH zh : ℝ) : ℂ) * Complex.I)
        = ((Real.cos 3 * Real.cos 2 ^ 2 : ℝ) : ℂ) := by
      simp_rw [headC_as_sum]
      rw [head_factor]
      congr 1
      simp only [tailH, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, mul_zero, add_zero, one_mul]
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.cos_neg, cos_pm u 3 hu]
      ring
    rw [hhead]
    simp_rw [tail_obsMean]
    ring
  rw [featMean_eq, featMean_eq, hcf]
  split_ifs
  · rw [Complex.im_ofReal_mul]
  · rw [Complex.re_ofReal_mul]

/-- **The tail gap**: at least `|cos 3| cos^2 2 * 2 sin 1 (3/(4r))^r h^r exp(-sigma^2/2)` for
`0 < h <= r`. -/
theorem tail_gap_lower {r : ℕ} (hr : 0 < r) (σ h u : ℝ) (hu : u = 1 ∨ u = -1) (hh : 0 < h)
    (hhr : h ≤ r) :
    |Real.cos 3| * Real.cos 2 ^ 2
        * (2 * Real.sin 1 * (3 / (4 * (r : ℝ))) ^ r * h ^ r * Real.exp (-(σ ^ 2 / 2)))
      ≤ |featMean r (famLaw σ h u 1 tailH (tailT r))
          - featMean r (famLaw σ h u (-1) tailH (tailT r))| := by
  rw [tailMean_eq σ h u 1 hu, tailMean_eq σ h u (-1) hu, ← mul_sub, abs_mul, abs_mul,
    abs_of_nonneg (sq_nonneg (Real.cos 2))]
  have hg := feature_gap_lower r hr h hh hhr (var2 σ)
  rw [var2_coe] at hg
  exact mul_le_mul_of_nonneg_left hg (by positivity)

#print axioms famLaw_eq_withDensity
#print axioms obsLawC_famChan
#print axioms charFun_famLaw
#print axioms head_factor
#print axioms decMean_eq
#print axioms dec_gap_lower
#print axioms tailMean_eq
#print axioms tail_gap_lower

end CIGAMF.P13.PaperBFamilyLaw
