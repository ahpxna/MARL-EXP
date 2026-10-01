import «LeanPaperBHellingerTestV1»
import «LeanPaperBFamilyDecoderV1»

/-!
# Paper B: the general law, both sides, on the latent family

`hellinger_tournament` (`LeanPaperBHellingerTestV1`) attains `|W|^2 log(|W|/delta)/t_H` on every
channel, where `t_H` resolves the obstructions in Hellinger information.  This module bounds the
Hellinger information BELOW by the gap of a bounded feature, and uses the latent family's own
feature gaps, so that the general tournament attains both of the family's rates.  With the
general lower law (`family_safe_lower`, `family_id_lower`), the obstruction law is then tight on
the latent family on both sides.

* `tvs`: the `l1` distance `∫ |p_w - p_v|` of a query.
* `tvs_sq_le`: `(∫ |p_w - p_v|)^2 <= 8 H^2`, from the pointwise AM-GM bound
  `|p - q| <= (t/2)(√p - √q)^2 + (1/(2t))(√p + √q)^2`, with `∫(√p - √q)^2 = 2 H^2` and
  `∫(√p + √q)^2 <= 4`.  Everything is a `lintegral` of a nonnegative function.
* `feature_gap_le`: for a measurable feature with `|f| <= 1`, the two means differ by at most
  `∫ |p_w - p_v|`.  So `gap^2 <= 8 H^2`.
* `fam_hel_u`, `fam_hel_v`: on the latent family's decoder channel, worlds that differ in `u` have
  Hellinger information at least `(G_dec h)^2/8` at the decision probe, and worlds that differ in
  `v` at least `(G_tail h^r)^2/8` at the tail probe.
* `fam_resolves_safe`, `fam_resolves_id`: every obstruction is resolved at those thresholds.
* **`family_safe_general_upper`**, **`family_id_general_upper`**: the GENERAL tournament is safe
  (resp. identifies) with probability `>= 1 - delta` within `16 ceil(8 log(4/delta)/(G h)^2)` and
  `16 ceil(8 log(4/delta)/(G_I h^r)^2)` queries.
-/

namespace CIGAMF.P13.PaperBHellingerFamily

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBHellingerTest
open CIGAMF.P13.PaperBSchedTest CIGAMF.P13.PaperBParityGap CIGAMF.P13.PaperBRates
open CIGAMF.P13.PaperBFamilyChannel CIGAMF.P13.PaperBFamilyLaw CIGAMF.P13.PaperBFamilyDecoder

/-! ## 1. The `l1` distance is at most `sqrt(8) H` -/

section General

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- The `l1` distance of query `q` between two worlds. -/
noncomputable def tvs (C : Channel W Q) (w v : W) (q : Q) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal |C.dens w q y - C.dens v q y|

theorem sqrt_identities (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 + 2 * Real.sqrt (a * b) = a + b
      ∧ (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * Real.sqrt (a * b) := by
  rw [Real.sqrt_mul ha]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  constructor <;> nlinarith

/-- **The pointwise AM-GM bound.** -/
theorem abs_sub_le_amgm (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    |a - b| ≤ t / 2 * (Real.sqrt a - Real.sqrt b) ^ 2
      + 1 / (2 * t) * (Real.sqrt a + Real.sqrt b) ^ 2 := by
  set x := |Real.sqrt a - Real.sqrt b|
  set y := Real.sqrt a + Real.sqrt b
  have hy : 0 ≤ y := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hab : |a - b| = x * y := by
    have e : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
      have h1 := Real.sq_sqrt ha
      have h2 := Real.sq_sqrt hb
      nlinarith
    rw [e, abs_mul, abs_of_nonneg hy]
  have hx2 : (Real.sqrt a - Real.sqrt b) ^ 2 = x ^ 2 := (sq_abs _).symm
  rw [hab, hx2]
  have key : t / 2 * x ^ 2 + 1 / (2 * t) * y ^ 2 - x * y = (t * x - y) ^ 2 / (2 * t) := by
    field_simp
    ring
  have : 0 ≤ (t * x - y) ^ 2 / (2 * t) := by positivity
  linarith

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem lint_sqdiff (C : Channel W Q) (w v : W) (q : Q) :
    (∫⁻ y, ENNReal.ofReal ((Real.sqrt (C.dens w q y) - Real.sqrt (C.dens v q y)) ^ 2))
      + 2 * bc C w v q = 2 := by
  have hpt : ∀ y, ENNReal.ofReal ((Real.sqrt (C.dens w q y) - Real.sqrt (C.dens v q y)) ^ 2)
      + 2 * ENNReal.ofReal (Real.sqrt (C.dens w q y * C.dens v q y))
      = ENNReal.ofReal (C.dens w q y) + ENNReal.ofReal (C.dens v q y) := by
    intro y
    have ha := (C.pos w q y).le
    have hb := (C.pos v q y).le
    rw [← ENNReal.ofReal_add ha hb, ← (sqrt_identities _ _ ha hb).1,
      ENNReal.ofReal_add (sq_nonneg _) (by positivity),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hm1 : Measurable fun y =>
      ENNReal.ofReal ((Real.sqrt (C.dens w q y) - Real.sqrt (C.dens v q y)) ^ 2) :=
    (((Real.continuous_sqrt.measurable.comp (C.meas w q)).sub
      (Real.continuous_sqrt.measurable.comp (C.meas v q))).pow_const 2).ennreal_ofReal
  have hm2 : Measurable fun y => ENNReal.ofReal (Real.sqrt (C.dens w q y * C.dens v q y)) :=
    (Real.continuous_sqrt.measurable.comp ((C.meas w q).mul (C.meas v q))).ennreal_ofReal
  unfold bc
  rw [← lintegral_const_mul _ hm2, ← lintegral_add_left hm1]
  simp_rw [hpt]
  rw [lintegral_add_left (C.meas w q).ennreal_ofReal, C.mass w q, C.mass v q]
  norm_num

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem lint_sqsum (C : Channel W Q) (w v : W) (q : Q) :
    ∫⁻ y, ENNReal.ofReal ((Real.sqrt (C.dens w q y) + Real.sqrt (C.dens v q y)) ^ 2)
      = 2 + 2 * bc C w v q := by
  have hpt : ∀ y, ENNReal.ofReal ((Real.sqrt (C.dens w q y) + Real.sqrt (C.dens v q y)) ^ 2)
      = ENNReal.ofReal (C.dens w q y) + ENNReal.ofReal (C.dens v q y)
        + 2 * ENNReal.ofReal (Real.sqrt (C.dens w q y * C.dens v q y)) := by
    intro y
    have ha := (C.pos w q y).le
    have hb := (C.pos v q y).le
    rw [(sqrt_identities _ _ ha hb).2, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add ha hb, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hm2 : Measurable fun y => ENNReal.ofReal (Real.sqrt (C.dens w q y * C.dens v q y)) :=
    (Real.continuous_sqrt.measurable.comp ((C.meas w q).mul (C.meas v q))).ennreal_ofReal
  simp_rw [hpt]
  unfold bc
  have hmpq : Measurable fun y => ENNReal.ofReal (C.dens w q y) + ENNReal.ofReal (C.dens v q y) :=
    (C.meas w q).ennreal_ofReal.add (C.meas v q).ennreal_ofReal
  rw [lintegral_add_left hmpq, lintegral_add_left (C.meas w q).ennreal_ofReal, C.mass w q,
    C.mass v q, lintegral_const_mul _ hm2]
  norm_num

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
theorem tvs_le_two (C : Channel W Q) (w v : W) (q : Q) : tvs C w v q ≤ 2 := by
  unfold tvs
  have hpt : ∀ y, ENNReal.ofReal |C.dens w q y - C.dens v q y|
      ≤ ENNReal.ofReal (C.dens w q y) + ENNReal.ofReal (C.dens v q y) := by
    intro y
    have ha := (C.pos w q y).le
    have hb := (C.pos v q y).le
    rw [← ENNReal.ofReal_add ha hb]
    exact ENNReal.ofReal_le_ofReal (by rw [abs_le]; constructor <;> linarith)
  calc ∫⁻ y, ENNReal.ofReal |C.dens w q y - C.dens v q y|
      ≤ ∫⁻ y, (ENNReal.ofReal (C.dens w q y) + ENNReal.ofReal (C.dens v q y)) := lintegral_mono hpt
    _ = 2 := by
        rw [lintegral_add_left (C.meas w q).ennreal_ofReal, C.mass w q, C.mass v q]
        norm_num

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- **`∫|p - q| <= t H^2 + 2/t` for every `t > 0`.** -/
theorem tvs_bound (C : Channel W Q) (w v : W) (q : Q) (t : ℝ) (ht : 0 < t) :
    (tvs C w v q).toReal ≤ t * hel C w v q + 2 / t := by
  set A := ∫⁻ y, ENNReal.ofReal ((Real.sqrt (C.dens w q y) - Real.sqrt (C.dens v q y)) ^ 2)
  set B := ∫⁻ y, ENNReal.ofReal ((Real.sqrt (C.dens w q y) + Real.sqrt (C.dens v q y)) ^ 2)
  have hA : A + 2 * bc C w v q = 2 := lint_sqdiff C w v q
  have hB : B = 2 + 2 * bc C w v q := lint_sqsum C w v q
  have hbc := bc_ne_top C w v q
  have hbc1 : (bc C w v q).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using bc_le_one C w v q)
  have hAtop : A ≠ ⊤ := by
    intro h; rw [h, top_add] at hA; exact ENNReal.top_ne_ofNat hA
  have hBtop : B ≠ ⊤ := by rw [hB]; exact ENNReal.add_ne_top.mpr ⟨by simp, ENNReal.mul_ne_top (by simp) hbc⟩
  have hAr : A.toReal = 2 - 2 * (bc C w v q).toReal := by
    have := congrArg ENNReal.toReal hA
    rw [ENNReal.toReal_add hAtop (ENNReal.mul_ne_top (by simp) hbc), ENNReal.toReal_mul] at this
    simp at this
    linarith
  have hBr : B.toReal = 2 + 2 * (bc C w v q).toReal := by
    rw [hB, ENNReal.toReal_add (by simp) (ENNReal.mul_ne_top (by simp) hbc), ENNReal.toReal_mul]
    simp
  have hmA : Measurable fun y =>
      ENNReal.ofReal ((Real.sqrt (C.dens w q y) - Real.sqrt (C.dens v q y)) ^ 2) :=
    (((Real.continuous_sqrt.measurable.comp (C.meas w q)).sub
      (Real.continuous_sqrt.measurable.comp (C.meas v q))).pow_const 2).ennreal_ofReal
  have hmB : Measurable fun y =>
      ENNReal.ofReal ((Real.sqrt (C.dens w q y) + Real.sqrt (C.dens v q y)) ^ 2) :=
    (((Real.continuous_sqrt.measurable.comp (C.meas w q)).add
      (Real.continuous_sqrt.measurable.comp (C.meas v q))).pow_const 2).ennreal_ofReal
  have hle : tvs C w v q ≤ ENNReal.ofReal (t / 2) * A + ENNReal.ofReal (1 / (2 * t)) * B := by
    unfold tvs
    rw [← lintegral_const_mul _ hmA, ← lintegral_const_mul _ hmB,
      ← lintegral_add_left (hmA.const_mul _)]
    refine lintegral_mono fun y => ?_
    have ha := (C.pos w q y).le
    have hb := (C.pos v q y).le
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le_amgm _ _ t ha hb ht)
  have hfin : ENNReal.ofReal (t / 2) * A + ENNReal.ofReal (1 / (2 * t)) * B ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by simp) hAtop, ENNReal.mul_ne_top (by simp) hBtop⟩
  have h1 := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) hAtop) (ENNReal.mul_ne_top (by simp) hBtop),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), hAr, hBr] at h1
  unfold hel
  have e : t / 2 * (2 - 2 * (bc C w v q).toReal) + 1 / (2 * t) * (2 + 2 * (bc C w v q).toReal)
      = t * (1 - (bc C w v q).toReal) + (1 + (bc C w v q).toReal) / t := by
    field_simp <;> ring
  rw [e] at h1
  have h2 : (1 + (bc C w v q).toReal) / t ≤ 2 / t :=
    div_le_div_of_nonneg_right (by linarith) ht.le
  linarith

omit [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q] [DecidableEq Q] in
/-- **`(∫ |p_w - p_v|)^2 <= 8 H^2`.** -/
theorem tvs_sq_le (C : Channel W Q) (w v : W) (q : Q) :
    (tvs C w v q).toReal ^ 2 ≤ 8 * hel C w v q := by
  set X := (tvs C w v q).toReal with hX
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hH0 := hel_nonneg C w v q
  rcases hX0.eq_or_lt with h | h
  · rw [← h]; nlinarith
  · have hb := tvs_bound C w v q (4 / X) (by positivity)
    have e1 : 2 / (4 / X) = X / 2 := by rw [div_div_eq_mul_div]; ring
    have e2 : 4 / X * hel C w v q * X = 4 * hel C w v q := by field_simp
    rw [e1] at hb
    nlinarith

/-- **A bounded feature's mean gap is at most the `l1` distance.** -/
theorem feature_gap_le (C : Channel W Q) (w v : W) (q : Q) (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∀ y, |f y| ≤ 1) :
    |∫ y, f y ∂obsLawC C w q - ∫ y, f y ∂obsLawC C v q| ≤ (tvs C w v q).toReal := by
  have hlaw : ∀ x : W, ∫ y, f y ∂obsLawC C x q = ∫ y, C.dens x q y * f y := by
    intro x
    unfold obsLawC
    rw [integral_withDensity_eq_integral_toReal_smul₀ (C.meas x q).ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (C.pos x q y).le]
  have hint : ∀ x : W, Integrable (fun y => C.dens x q y) := by
    intro x
    have h := integrable_toReal_of_lintegral_ne_top
      ((C.meas x q).ennreal_ofReal.aemeasurable (μ := volume)) (by rw [C.mass x q]; simp)
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [ENNReal.toReal_ofReal (C.pos x q y).le]
  have hintf : ∀ x : W, Integrable (fun y => C.dens x q y * f y) := by
    intro x
    refine (hint x).mono' ((C.meas x q).mul hf).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (C.pos x q y)]
    exact mul_le_of_le_one_right (C.pos x q y).le (hb y)
  have hd : Integrable (fun y => |C.dens w q y - C.dens v q y|) :=
    ((hint w).sub (hint v)).abs
  rw [hlaw w, hlaw v, ← integral_sub (hintf w) (hintf v)]
  have hn : |∫ y, (C.dens w q y * f y - C.dens v q y * f y)|
      ≤ ∫ y, |C.dens w q y - C.dens v q y| := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hd (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hb y)
  refine hn.trans (le_of_eq ?_)
  unfold tvs
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => abs_nonneg _)
    hd.aestronglyMeasurable]

/-- **A feature gap forces Hellinger information**: `gap^2 <= 8 H^2`. -/
theorem gap_sq_le_hel (C : Channel W Q) (w v : W) (q : Q) (f : ℝ → ℝ) (hf : Measurable f)
    (hb : ∀ y, |f y| ≤ 1) :
    (∫ y, f y ∂obsLawC C w q - ∫ y, f y ∂obsLawC C v q) ^ 2 ≤ 8 * hel C w v q := by
  have h1 := feature_gap_le C w v q f hf hb
  have h2 := tvs_sq_le C w v q
  have h3 : (∫ y, f y ∂obsLawC C w q - ∫ y, f y ∂obsLawC C v q) ^ 2
      ≤ (tvs C w v q).toReal ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  linarith

end General

/-! ## 2. The latent family's Hellinger information -/

theorem fmean_eq_int (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) (w : Bool × Bool) :
    fmean (dChan r σ h hσ) w (onQuery 1 Real.cos hcos hbcos) 1
      = ∫ y, Real.cos y ∂obsLawC (dChan r σ h hσ) w 1 := by
  unfold fmean onQuery
  simp only [if_true]

theorem fmean_eq_int_tail (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) (w : Bool × Bool) :
    fmean (dChan r σ h hσ) w (onQuery 2 (feat r) (continuous_feat r).measurable (feat_abs_le r)) 2
      = ∫ y, feat r y ∂obsLawC (dChan r σ h hσ) w 2 := by
  unfold fmean onQuery
  simp only [if_true]

theorem sgnB_ne {a b : Bool} (h : a ≠ b) (F : ℝ → ℝ) :
    |F (sgnB a) - F (sgnB b)| = |F 1 - F (-1)| := by
  cases a <;> cases b <;> simp_all [sgnB, abs_sub_comm]

/-- **Worlds that differ in `u` carry `(G_dec h)^2/8` of Hellinger information at the decision
probe.** -/
theorem fam_hel_u (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1)
    (w w' : Bool × Bool) (hu : w.1 ≠ w'.1) :
    (Gdec σ * h) ^ 2 / 8 ≤ hel (dChan r σ h hσ) w w' 1 := by
  have hg := gap_sq_le_hel (dChan r σ h hσ) w w' 1 Real.cos hcos hbcos
  rw [← fmean_eq_int, ← fmean_eq_int, fmean_dec, fmean_dec] at hg
  have hgap : Gdec σ * h ≤ |cDec σ h (uOf w) - cDec σ h (uOf w')| := by
    unfold uOf
    rw [sgnB_ne hu (cDec σ h)]
    exact dec_gap r σ h hh hh1
  have h0 : 0 ≤ Gdec σ * h := (mul_pos (Gdec_pos σ) hh).le
  have hsq : (Gdec σ * h) ^ 2 ≤ (cDec σ h (uOf w) - cDec σ h (uOf w')) ^ 2 := by
    rw [← sq_abs (cDec σ h (uOf w) - cDec σ h (uOf w'))]
    exact pow_le_pow_left₀ h0 hgap 2
  linarith

/-- **Worlds that differ in `v` carry `(G_tail h^r)^2/8` at the tail probe.** -/
theorem fam_hel_v (r : ℕ) (hr : 0 < r) (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1)
    (w w' : Bool × Bool) (hv : w.2 ≠ w'.2) :
    (Gtail r σ * h ^ r) ^ 2 / 8 ≤ hel (dChan r σ h hσ) w w' 2 := by
  have hg := gap_sq_le_hel (dChan r σ h hσ) w w' 2 (feat r) (continuous_feat r).measurable
    (feat_abs_le r)
  rw [← fmean_eq_int_tail, ← fmean_eq_int_tail, fmean_tail, fmean_tail] at hg
  have hhr : h ≤ (r : ℝ) := hh1.trans (by exact_mod_cast hr)
  have hgap : Gtail r σ * h ^ r ≤ |dTail r σ h (vOf w) - dTail r σ h (vOf w')| := by
    unfold vOf
    rw [sgnB_ne hv (dTail r σ h)]
    exact tail_gap r hr σ h hh hhr
  have h0 : 0 ≤ Gtail r σ * h ^ r := (mul_pos (Gtail_pos r hr σ) (pow_pos hh r)).le
  have hsq : (Gtail r σ * h ^ r) ^ 2 ≤ (dTail r σ h (vOf w) - dTail r σ h (vOf w')) ^ 2 := by
    rw [← sq_abs (dTail r σ h (vOf w) - dTail r σ h (vOf w'))]
    exact pow_le_pow_left₀ h0 hgap 2
  linarith

theorem kH_ge (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) (w w' : Bool × Bool) (q : Fin 3) (x : ℝ)
    (hx : x ≤ hel (dChan r σ h hσ) w w' q) : x ≤ (kH (dChan r σ h hσ) w w' : ℝ) := by
  have : helNN (dChan r σ h hσ) w w' q ≤ kH (dChan r σ h hσ) w w' :=
    Finset.le_sup (Finset.mem_univ _)
  exact hx.trans (by exact_mod_cast this)

/-- The safe threshold `(G_dec h)^2/8`. -/
noncomputable def tS (σ h : ℝ) : ℝ≥0 := ⟨(Gdec σ * h) ^ 2 / 8, by positivity⟩

/-- The identification threshold `(G_I h^r)^2/8`. -/
noncomputable def tI (r : ℕ) (σ h : ℝ) : ℝ≥0 := ⟨(GI r σ * h ^ r) ^ 2 / 8, by positivity⟩

/-- **Every obstruction of the safe decision is resolved at `(G_dec h)^2/8`.** -/
theorem fam_resolves_safe (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) :
    Resolves (kH (dChan r σ h hσ)) (famSafe r) (tS σ h) := by
  intro H hH
  obtain ⟨w1, hw1, h1⟩ := hH 0
  obtain ⟨w2, hw2, h2⟩ := hH 1
  have e1 : w1.1 = true := by
    by_contra hc
    simp only [Bool.not_eq_true] at hc
    exact h1 (by simp [famSafe, hc])
  have e2 : w2.1 = false := by
    by_contra hc
    simp only [Bool.not_eq_false] at hc
    exact h2 (by simp [famSafe, hc])
  have hu : w1.1 ≠ w2.1 := by rw [e1, e2]; decide
  refine ⟨w1, hw1, w2, hw2, fun h => hu (by rw [h]), ?_⟩
  show ((Gdec σ * h) ^ 2 / 8 : ℝ) ≤ (kH (dChan r σ h hσ) w1 w2 : ℝ)
  exact kH_ge r σ h hσ w1 w2 1 _ (fam_hel_u r σ h hσ hh hh1 w1 w2 hu)

/-- **Every obstruction of identification is resolved at `(G_I h^r)^2/8`.** -/
theorem fam_resolves_id (r : ℕ) (hr : 0 < r) (σ h : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1) :
    Resolves (kH (dChan r σ h hσ)) (fun w : Bool × Bool => ({w} : Finset (Bool × Bool)))
      (tI r σ h) := by
  intro H hH
  obtain ⟨w0, hw0, -⟩ := hH (true, true)
  obtain ⟨w1, hw1, h1⟩ := hH w0
  have hne : w0 ≠ w1 := by simpa using h1
  refine ⟨w0, hw0, w1, hw1, hne, ?_⟩
  show ((GI r σ * h ^ r) ^ 2 / 8 : ℝ) ≤ (kH (dChan r σ h hσ) w0 w1 : ℝ)
  have hGI0 : 0 ≤ GI r σ := (GI_pos r hr σ).le
  have hhr : h ^ r ≤ h := by
    calc h ^ r ≤ h ^ 1 := pow_le_pow_of_le_one hh.le hh1 hr
      _ = h := pow_one h
  have hhr0 : 0 ≤ h ^ r := (pow_pos hh r).le
  by_cases hu : w0.1 = w1.1
  · have hv : w0.2 ≠ w1.2 := fun hv => hne (Prod.ext hu hv)
    refine kH_ge r σ h hσ w0 w1 2 _ (le_trans ?_ (fam_hel_v r hr σ h hσ hh hh1 w0 w1 hv))
    have : GI r σ * h ^ r ≤ Gtail r σ * h ^ r :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hhr0
    have h0 : 0 ≤ GI r σ * h ^ r := mul_nonneg hGI0 hhr0
    have := pow_le_pow_left₀ h0 this 2
    linarith
  · refine kH_ge r σ h hσ w0 w1 1 _ (le_trans ?_ (fam_hel_u r σ h hσ hh hh1 w0 w1 hu))
    have h1' : GI r σ * h ^ r ≤ Gdec σ * h :=
      mul_le_mul (min_le_left _ _) hhr hhr0 (Gdec_pos σ).le
    have h0 : 0 ≤ GI r σ * h ^ r := mul_nonneg hGI0 hhr0
    have := pow_le_pow_left₀ h0 h1' 2
    linarith

/-! ## 3. Both family rates from the general tournament -/

theorem card_W : Fintype.card (Bool × Bool) = 4 := by decide

/-- **The general law attains the safe decision's rate on the latent family.**  The Hellinger
tournament with `n = ceil(8 log(4/delta)/(G_dec h)^2)` rounds per pair is safe with probability
`>= 1 - delta` at every world, within `16 n` queries. -/
theorem family_safe_general_upper (r : ℕ) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hδ : 0 < δ) :
    (∀ w, hist (dChan r σ h hσ)
        (schedPolicy (tSched (dChan r σ h hσ) (tS σ h)
          ⌈8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2⌉₊)) w
        (Fintype.card ((Bool × Bool) × (Bool × Bool))
          * ⌈8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2⌉₊)
        {ω | decode (famSafe r) (pairSet (kH (dChan r σ h hσ)) (tS σ h))
            (beatH (dChan r σ h hσ) (tS σ h) ⌈8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2⌉₊) 0 ω
          ∉ famSafe r w} ≤ ENNReal.ofReal δ)
      ∧ ∀ w, costN (dChan r σ h hσ)
          (schedPolicy (tSched (dChan r σ h hσ) (tS σ h)
            ⌈8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2⌉₊)) w
          (Fintype.card ((Bool × Bool) × (Bool × Bool))
            * ⌈8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2⌉₊)
          ≤ ((16 * ⌈8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2⌉₊ : ℕ) : ℝ≥0∞) := by
  have hG := mul_pos (Gdec_pos σ) hh
  have htpos : 0 < tS σ h := by
    show (0 : ℝ) < (Gdec σ * h) ^ 2 / 8
    positivity
  have hn : Real.log ((Fintype.card (Bool × Bool) : ℝ) / δ) / (tS σ h)
      ≤ (⌈8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2⌉₊ : ℝ) := by
    rw [card_W]
    have e : Real.log (((4 : ℕ) : ℝ) / δ) / ((tS σ h : ℝ≥0) : ℝ)
        = 8 * Real.log (4 / δ) / (Gdec σ * h) ^ 2 := by
      show Real.log (((4 : ℕ) : ℝ) / δ) / ((Gdec σ * h) ^ 2 / 8) = _
      push_cast
      field_simp
    rw [e]
    exact Nat.le_ceil _
  obtain ⟨h1, h2⟩ := hellinger_tournament (dChan r σ h hσ) (famSafe r) (tS σ h) htpos
    (fam_resolves_safe r σ h hσ hh hh1) 0 δ hδ _ hn
  refine ⟨h1, fun w => (h2 w).trans (le_of_eq ?_)⟩
  rw [card_W]
  norm_num

/-- **The general law attains identification's rate on the latent family.** -/
theorem family_id_general_upper (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) :
    (∀ w, hist (dChan r σ h hσ)
        (schedPolicy (tSched (dChan r σ h hσ) (tI r σ h)
          ⌈8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊)) w
        (Fintype.card ((Bool × Bool) × (Bool × Bool))
          * ⌈8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊)
        {ω | decode (fun w : Bool × Bool => ({w} : Finset (Bool × Bool)))
            (pairSet (kH (dChan r σ h hσ)) (tI r σ h))
            (beatH (dChan r σ h hσ) (tI r σ h) ⌈8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊)
            (true, true) ω ∉ ({w} : Finset (Bool × Bool))} ≤ ENNReal.ofReal δ)
      ∧ ∀ w, costN (dChan r σ h hσ)
          (schedPolicy (tSched (dChan r σ h hσ) (tI r σ h)
            ⌈8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊)) w
          (Fintype.card ((Bool × Bool) × (Bool × Bool))
            * ⌈8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊)
          ≤ ((16 * ⌈8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊ : ℕ) : ℝ≥0∞) := by
  have hG := mul_pos (GI_pos r hr σ) (pow_pos hh r)
  have htpos : 0 < tI r σ h := by
    show (0 : ℝ) < (GI r σ * h ^ r) ^ 2 / 8
    positivity
  have hn : Real.log ((Fintype.card (Bool × Bool) : ℝ) / δ) / (tI r σ h)
      ≤ (⌈8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊ : ℝ) := by
    rw [card_W]
    have e : Real.log (((4 : ℕ) : ℝ) / δ) / ((tI r σ h : ℝ≥0) : ℝ)
        = 8 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2 := by
      show Real.log (((4 : ℕ) : ℝ) / δ) / ((GI r σ * h ^ r) ^ 2 / 8) = _
      push_cast
      field_simp
    rw [e]
    exact Nat.le_ceil _
  obtain ⟨h1, h2⟩ := hellinger_tournament (dChan r σ h hσ)
    (fun w : Bool × Bool => ({w} : Finset (Bool × Bool))) (tI r σ h) htpos
    (fam_resolves_id r hr σ h hσ hh hh1) (true, true) δ hδ _ hn
  refine ⟨h1, fun w => (h2 w).trans (le_of_eq ?_)⟩
  rw [card_W]
  norm_num

#print axioms tvs_sq_le
#print axioms feature_gap_le
#print axioms gap_sq_le_hel
#print axioms fam_hel_u
#print axioms fam_hel_v
#print axioms fam_resolves_safe
#print axioms fam_resolves_id
#print axioms family_safe_general_upper
#print axioms family_id_general_upper

end CIGAMF.P13.PaperBHellingerFamily
