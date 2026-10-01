import «LeanPaperBShareTournamentV1»

/-!
# The certificate channel: with KL information the factor `1/(|W|-1)` cannot be removed

`obstruction_lower` states, for every channel, `E_w N · t_KL ≥ ((1-δ)/(|H|-1)) log(1/δ) - log 2`.
This module exhibits channels on which that bound is attained to first order, factor included.

**The channel.**
* Worlds `w ∈ Fin k`, `k ≥ 2`. Answers `a ∈ Fin k` read "not `a`", so `a` is safe exactly at
  the worlds `w ≠ a`. No answer is safe everywhere, so `Fin k` is an obstruction.
* One informative query returns a real `y` whose region `reg y ∈ Fin k` is a symbol `s` with
  law `P_w(s = w) = ρ` and `P_w(s = v) = (1-ρ)/(k-1)` for `v ≠ w`. Inside a region, `y` is
  standard Gaussian restricted to it, the same in every world, so the density ratio of two
  worlds is constant on each region.

**What is proved.**
* `cert_error`: the one-query policy "answer `reg y`" is wrong with probability exactly `ρ` at
  every world (`cert_policy_correct`), and it pays one query (`cert_cost`).
* `klq_cert_le`: for `ρ ≤ 1/k`, every query carries at most `log(1/((k-1)ρ))/(k-1)` nats
  between any two worlds.
* `cert_tight`: with `ρ = δ`, `E N · t_KL ≤ log(1/((k-1)δ))/(k-1)`, against the law's
  `((1-δ)/(k-1)) log(1/δ) - log 2`. Up to the additive terms the lower law is an equality, and
  its factor `1/(|W|-1)` is necessary for any bound stated through KL information alone.
-/

namespace CIGAMF.P13.PaperBCertificateChannel

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperALowerKL
open CIGAMF.P13.PaperBObstructionLaw CIGAMF.P13.PaperBSafe CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBHellingerTest

variable (k : ℕ) [NeZero k]

/-! ## 1. Regions of the real line -/

/-- The region of `y`: `⌊y⌋` clamped to `{0, …, k-1}`. -/
noncomputable def reg (y : ℝ) : Fin k :=
  ⟨min (Int.toNat ⌊y⌋) (k - 1), by have := NeZero.pos k; omega⟩

theorem measurable_reg : Measurable (reg k) := by
  have : reg k = (fun z : ℤ => (⟨min z.toNat (k - 1), by have := NeZero.pos k; omega⟩ : Fin k))
      ∘ Int.floor := rfl
  rw [this]
  exact (Measurable.of_discrete).comp Int.measurable_floor

theorem measurableSet_region (s : Fin k) : MeasurableSet (reg k ⁻¹' {s}) :=
  measurable_reg k (measurableSet_singleton s)

theorem Ico_sub_region (s : Fin k) : Set.Ico (s : ℝ) ((s : ℝ) + 1) ⊆ reg k ⁻¹' {s} := by
  intro y hy
  have hfl : ⌊y⌋ = (s : ℤ) := by
    rw [Int.floor_eq_iff]
    exact ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff, reg, hfl, Int.toNat_natCast]
  ext
  simp only
  have := s.isLt
  omega

/-- The Gaussian mass of a region. -/
noncomputable def massR (s : Fin k) : ℝ≥0∞ :=
  ∫⁻ y in reg k ⁻¹' {s}, ENNReal.ofReal (gaussianPDFReal 0 1 y)

theorem massR_le_one (s : Fin k) : massR k s ≤ 1 := by
  unfold massR
  calc ∫⁻ y in reg k ⁻¹' {s}, ENNReal.ofReal (gaussianPDFReal 0 1 y)
      ≤ ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 1 y) := setLIntegral_le_lintegral _ _
    _ = 1 := lintegral_gaussianPDFReal_eq_one _ one_ne_zero

theorem massR_pos (s : Fin k) : 0 < massR k s := by
  unfold massR
  rw [setLIntegral_pos_iff (measurable_gaussianPDFReal 0 1).ennreal_ofReal]
  have hsupp : Function.support (fun y => ENNReal.ofReal (gaussianPDFReal 0 1 y)) = Set.univ := by
    ext y
    simp [gaussianPDFReal_pos 0 1 y one_ne_zero]
  rw [hsupp, Set.univ_inter]
  calc (0 : ℝ≥0∞) < volume (Set.Ico (s : ℝ) ((s : ℝ) + 1)) := by simp
    _ ≤ volume (reg k ⁻¹' {s}) := measure_mono (Ico_sub_region k s)

theorem massR_ne_top (s : Fin k) : massR k s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (massR_le_one k s)

/-- The region mass as a positive real. -/
noncomputable def B (s : Fin k) : ℝ := (massR k s).toReal

theorem B_pos (s : Fin k) : 0 < B k s :=
  ENNReal.toReal_pos (massR_pos k s).ne' (massR_ne_top k s)

theorem ofReal_B (s : Fin k) : ENNReal.ofReal (B k s) = massR k s :=
  ENNReal.ofReal_toReal (massR_ne_top k s)

/-- **Integrating a region-constant multiple of the Gaussian.** -/
theorem lintegral_region (G : Fin k → ℝ≥0∞) :
    ∫⁻ y, G (reg k y) * ENNReal.ofReal (gaussianPDFReal 0 1 y)
      = ∑ s, G s * massR k s := by
  have hpt : ∀ y, G (reg k y) * ENNReal.ofReal (gaussianPDFReal 0 1 y)
      = ∑ s, (reg k ⁻¹' {s}).indicator
          (fun y => G s * ENNReal.ofReal (gaussianPDFReal 0 1 y)) y := by
    intro y
    rw [Finset.sum_eq_single (reg k y)]
    · rw [Set.indicator_of_mem (by simp)]
    · intro b _ hb
      rw [Set.indicator_of_notMem (by simpa using Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hpt]
  rw [lintegral_finsetSum _ fun s _ =>
    (((measurable_gaussianPDFReal 0 1).ennreal_ofReal.const_mul _).indicator
      (measurableSet_region k s))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lintegral_indicator (measurableSet_region k s),
    lintegral_const_mul _ (measurable_gaussianPDFReal 0 1).ennreal_ofReal]
  rfl

/-! ## 2. The symbol law and the channel -/

variable {k}

/-- The symbol law of world `w`. -/
noncomputable def sym (ρ : ℝ) (w s : Fin k) : ℝ := if s = w then ρ else (1 - ρ) / ((k : ℝ) - 1)

theorem sym_pos (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w s : Fin k) :
    0 < sym ρ w s := by
  unfold sym
  have : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  split_ifs
  · exact hρ0
  · apply div_pos <;> linarith

theorem sum_sym (hk : 2 ≤ k) (ρ : ℝ) (w : Fin k) : ∑ s, sym ρ w s = 1 := by
  unfold sym
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w)]
  rw [if_pos rfl]
  have hk1 : ((k : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    linarith
  rw [Finset.sum_congr rfl fun s hs => if_neg (Finset.ne_of_mem_erase hs),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
  field_simp
  ring

variable (k)

/-- The informative query's density in world `w`. -/
noncomputable def cdens (ρ : ℝ) (w : Fin k) (y : ℝ) : ℝ :=
  sym ρ w (reg k y) / B k (reg k y) * gaussianPDFReal 0 1 y

theorem measurable_cdens (ρ : ℝ) (w : Fin k) : Measurable (cdens k ρ w) := by
  unfold cdens
  have h1 : Measurable fun y => sym ρ w (reg k y) / B k (reg k y) :=
    (Measurable.of_discrete (f := fun s : Fin k => sym ρ w s / B k s)).comp (measurable_reg k)
  exact h1.mul (measurable_gaussianPDFReal 0 1)

theorem ofReal_cdens (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w : Fin k) (y : ℝ) :
    ENNReal.ofReal (cdens k ρ w y)
      = ENNReal.ofReal (sym ρ w (reg k y) / B k (reg k y))
        * ENNReal.ofReal (gaussianPDFReal 0 1 y) := by
  unfold cdens
  rw [ENNReal.ofReal_mul (div_pos (sym_pos hk ρ hρ0 hρ1 w _) (B_pos k _)).le]

theorem lintegral_cdens (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w : Fin k) :
    ∫⁻ y, ENNReal.ofReal (cdens k ρ w y) = 1 := by
  simp_rw [ofReal_cdens k hk ρ hρ0 hρ1 w]
  rw [lintegral_region k (fun s => ENNReal.ofReal (sym ρ w s / B k s))]
  have : ∀ s, ENNReal.ofReal (sym ρ w s / B k s) * massR k s = ENNReal.ofReal (sym ρ w s) := by
    intro s
    rw [← ofReal_B k s, ← ENNReal.ofReal_mul (div_pos (sym_pos hk ρ hρ0 hρ1 w s) (B_pos k s)).le,
      div_mul_cancel₀ _ (B_pos k s).ne']
  simp_rw [this]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => (sym_pos hk ρ hρ0 hρ1 w s).le), sum_sym hk,
    ENNReal.ofReal_one]

/-- **The certificate channel.** -/
noncomputable def certChan (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Channel (Fin k) (Fin 2) where
  dens w q y := if q = 0 then gaussianPDFReal 0 1 y else cdens k ρ w y
  dummy := 0
  meas w q := by
    by_cases hq : q = 0
    · simp only [hq, if_true]; exact measurable_gaussianPDFReal 0 1
    · simp only [hq, if_false]; exact measurable_cdens k ρ w
  pos w q y := by
    by_cases hq : q = 0
    · simp only [hq, if_true]; exact gaussianPDFReal_pos 0 1 y one_ne_zero
    · simp only [hq, if_false]
      unfold cdens
      exact mul_pos (div_pos (sym_pos hk ρ hρ0 hρ1 w _) (B_pos k _))
        (gaussianPDFReal_pos 0 1 y one_ne_zero)
  mass w q := by
    by_cases hq : q = 0
    · simp only [hq, if_true]; exact lintegral_gaussianPDFReal_eq_one _ one_ne_zero
    · simp only [hq, if_false]; exact lintegral_cdens k hk ρ hρ0 hρ1 w
  dummy_same w w' y := by simp

/-! ## 3. The divergence -/

theorem klq_cert_one (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w u : Fin k) :
    klq (certChan k hk ρ hρ0 hρ1) w u 1
      = ENNReal.ofReal (∑ s, sym ρ u s * klFun (sym ρ w s / sym ρ u s)) := by
  set C := certChan k hk ρ hρ0 hρ1
  have hd : ∀ v y, C.dens v 1 y = cdens k ρ v y := fun v y => by simp [C, certChan]
  unfold klq obsLawC
  simp_rw [hd]
  haveI : IsFiniteMeasure (volume.withDensity fun y => ENNReal.ofReal (cdens k ρ w y)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_cdens k hk ρ hρ0 hρ1 w]; exact ENNReal.one_lt_top⟩
  haveI : IsFiniteMeasure (volume.withDensity fun y => ENNReal.ofReal (cdens k ρ u y)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      lintegral_cdens k hk ρ hρ0 hρ1 u]; exact ENNReal.one_lt_top⟩
  have hpos : ∀ v y, 0 < cdens k ρ v y := fun v y =>
    mul_pos (div_pos (sym_pos hk ρ hρ0 hρ1 v _) (B_pos k _)) (gaussianPDFReal_pos 0 1 y one_ne_zero)
  rw [klDiv_withDensity_eq volume (measurable_cdens k ρ w).ennreal_ofReal
    (measurable_cdens k ρ u).ennreal_ofReal
    (fun y => (ENNReal.ofReal_pos.mpr (hpos u y)).ne') (fun y => ENNReal.ofReal_ne_top)]
  have hpt : ∀ y, ENNReal.ofReal ((ENNReal.ofReal (cdens k ρ u y)).toReal
      * klFun ((ENNReal.ofReal (cdens k ρ w y)).toReal / (ENNReal.ofReal (cdens k ρ u y)).toReal))
      = ENNReal.ofReal (sym ρ u (reg k y) * klFun (sym ρ w (reg k y) / sym ρ u (reg k y))
          / B k (reg k y)) * ENNReal.ofReal (gaussianPDFReal 0 1 y) := by
    intro y
    rw [ENNReal.toReal_ofReal (hpos w y).le, ENNReal.toReal_ofReal (hpos u y).le]
    have hratio : cdens k ρ w y / cdens k ρ u y = sym ρ w (reg k y) / sym ρ u (reg k y) := by
      unfold cdens
      have h1 := B_pos k (reg k y)
      have h2 := gaussianPDFReal_pos 0 1 y one_ne_zero
      have h3 := sym_pos hk ρ hρ0 hρ1 u (reg k y)
      field_simp
    rw [hratio, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (sym_pos hk ρ hρ0 hρ1 u _).le
      (klFun_nonneg (div_nonneg (sym_pos hk ρ hρ0 hρ1 w _).le (sym_pos hk ρ hρ0 hρ1 u _).le)))
      (B_pos k _).le)]
    congr 1
    unfold cdens
    ring
  simp_rw [hpt]
  rw [lintegral_region k (fun s => ENNReal.ofReal (sym ρ u s * klFun (sym ρ w s / sym ρ u s)
    / B k s))]
  have hs : ∀ s, ENNReal.ofReal (sym ρ u s * klFun (sym ρ w s / sym ρ u s) / B k s) * massR k s
      = ENNReal.ofReal (sym ρ u s * klFun (sym ρ w s / sym ρ u s)) := by
    intro s
    rw [← ofReal_B k s, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (sym_pos hk ρ hρ0 hρ1 u _).le
      (klFun_nonneg (div_nonneg (sym_pos hk ρ hρ0 hρ1 w _).le (sym_pos hk ρ hρ0 hρ1 u _).le)))
      (B_pos k _).le), div_mul_cancel₀ _ (B_pos k s).ne']
  simp_rw [hs]
  rw [ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (sym_pos hk ρ hρ0 hρ1 u _).le
    (klFun_nonneg (div_nonneg (sym_pos hk ρ hρ0 hρ1 w _).le (sym_pos hk ρ hρ0 hρ1 u _).le))]

/-- The divergence sum, in closed form: `(a - ρ) log(a/ρ)` with `a = (1-ρ)/(k-1)`. -/
theorem kl_sum_eq (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w u : Fin k) (hwu : w ≠ u) :
    ∑ s, sym ρ u s * klFun (sym ρ w s / sym ρ u s)
      = ((1 - ρ) / ((k : ℝ) - 1) - ρ) * Real.log (((1 - ρ) / ((k : ℝ) - 1)) / ρ) := by
  set a := (1 - ρ) / ((k : ℝ) - 1) with ha
  have ha0 : 0 < a := by
    have : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
    rw [ha]; apply div_pos <;> linarith
  have hzero : ∀ s ∈ (Finset.univ : Finset (Fin k)), s ∉ ({w, u} : Finset (Fin k)) →
      sym ρ u s * klFun (sym ρ w s / sym ρ u s) = 0 := by
    intro s _ hs
    have hsw : s ≠ w := fun h => hs (by simp [h])
    have hsu : s ≠ u := fun h => hs (by simp [h])
    unfold sym
    rw [if_neg hsw, if_neg hsu, div_self (ne_of_gt ha0), klFun_one, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_pair hwu]
  unfold sym
  rw [if_neg hwu, if_pos rfl, if_pos rfl, if_neg (Ne.symm hwu)]
  unfold klFun
  rw [show ρ / a = (a / ρ)⁻¹ by field_simp, Real.log_inv]
  have h1 : a * (a / ρ)⁻¹ = ρ := by field_simp
  have h2 : ρ * (a / ρ) = a := by field_simp
  calc a * ((a / ρ)⁻¹ * -Real.log (a / ρ) + 1 - (a / ρ)⁻¹)
        + ρ * (a / ρ * Real.log (a / ρ) + 1 - a / ρ)
      = (a * (a / ρ)⁻¹) * -Real.log (a / ρ) + a - a * (a / ρ)⁻¹
        + ((ρ * (a / ρ)) * Real.log (a / ρ) + ρ - ρ * (a / ρ)) := by ring
    _ = (a - ρ) * Real.log (a / ρ) := by rw [h1, h2]; ring

/-- **Every query carries at most `log(1/((k-1)ρ))/(k-1)` nats**, for `ρ ≤ 1/k`. -/
theorem klq_cert_le (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρk : ρ ≤ 1 / k) (w u : Fin k) (q : Fin 2) :
    klq (certChan k hk ρ hρ0 (by
      have : (1 : ℝ) / k < 1 := by
        rw [div_lt_one (by positivity)]; exact_mod_cast (show 1 < k by omega)
      linarith)) w u q
      ≤ ENNReal.ofReal (Real.log (1 / (((k : ℝ) - 1) * ρ)) / ((k : ℝ) - 1)) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hρ1 : ρ < 1 := by
    have : (1 : ℝ) / k < 1 := by rw [div_lt_one (by positivity)]; exact hk1
    linarith
  set a := (1 - ρ) / ((k : ℝ) - 1) with ha
  have hkρ : ((k : ℝ) - 1) * ρ ≤ 1 - ρ := by
    have : (k : ℝ) * ρ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hρk (by positivity : (0 : ℝ) ≤ k)
      rwa [mul_one_div_cancel (by positivity)] at this
    linarith
  have hρa : ρ ≤ a := by rw [ha, le_div_iff₀ (by linarith)]; linarith
  have hbound : (a - ρ) * Real.log (a / ρ) ≤ Real.log (1 / (((k : ℝ) - 1) * ρ)) / ((k : ℝ) - 1) := by
    have hlog0 : 0 ≤ Real.log (a / ρ) := Real.log_nonneg (by rw [le_div_iff₀ hρ0]; linarith)
    have ha1 : a ≤ 1 / ((k : ℝ) - 1) := by
      rw [ha]; apply div_le_div_of_nonneg_right (by linarith) (by linarith)
    have hlog : Real.log (a / ρ) ≤ Real.log (1 / (((k : ℝ) - 1) * ρ)) := by
      apply Real.log_le_log (div_pos (lt_of_lt_of_le hρ0 hρa) hρ0)
      calc a / ρ ≤ (1 / ((k : ℝ) - 1)) / ρ := div_le_div_of_nonneg_right ha1 hρ0.le
        _ = 1 / (((k : ℝ) - 1) * ρ) := by rw [div_div]
    calc (a - ρ) * Real.log (a / ρ) ≤ a * Real.log (a / ρ) :=
          mul_le_mul_of_nonneg_right (by linarith) hlog0
      _ ≤ 1 / ((k : ℝ) - 1) * Real.log (1 / (((k : ℝ) - 1) * ρ)) :=
          mul_le_mul ha1 hlog hlog0 (by positivity)
      _ = _ := by ring
  by_cases hq : q = 0
  · subst hq
    exact (klq_dummy' _ w u).le.trans zero_le
  · have hq1 : q = 1 := by omega
    subst hq1
    rw [klq_cert_one k hk ρ hρ0 hρ1 w u]
    apply ENNReal.ofReal_le_ofReal
    by_cases hwu : w = u
    · subst hwu
      have : ∀ s, sym ρ w s * klFun (sym ρ w s / sym ρ w s) = 0 := fun s => by
        rw [div_self (sym_pos hk ρ hρ0 hρ1 w s).ne', klFun_one, mul_zero]
      simp_rw [this]
      simp only [Finset.sum_const_zero]
      exact div_nonneg (Real.log_nonneg (by
        rw [le_div_iff₀ (by nlinarith)]; linarith)) (by linarith)
    · rw [kl_sum_eq k hk ρ hρ0 hρ1 w u hwu]
      exact hbound

/-! ## 4. The one-query policy -/

/-- The schedule: the informative query, always. -/
def certSched : ℕ → Fin 2 := fun _ => 1

/-- The answer "not `reg y`" after one query. -/
noncomputable def certOut (ω : Hist (Fin 2) 1) : Fin k := reg k (ω 0).2

/-- Answer `a` is safe exactly at the worlds `w ≠ a`. -/
def certSafe (w : Fin k) : Finset (Fin k) := Finset.univ.erase w

theorem certSafe_unsafe (hk : 2 ≤ k) : Unsafe (certSafe k) Finset.univ := by
  intro a
  exact ⟨a, Finset.mem_univ _, by simp [certSafe]⟩

/-- **The policy errs with probability exactly `ρ` at every world.** -/
theorem cert_error (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w : Fin k) :
    hist (certChan k hk ρ hρ0 hρ1) (schedPolicy certSched) w 1
        {ω | certOut k ω ∉ certSafe k w} = ENNReal.ofReal ρ := by
  set C := certChan k hk ρ hρ0 hρ1
  have hset : {ω : Hist (Fin 2) 1 | certOut k ω ∉ certSafe k w}
      = (fun ω : Hist (Fin 2) 1 => (ω 0).2) ⁻¹' (reg k ⁻¹' {w}) := by
    ext ω; simp [certOut, certSafe]
  have hm : MeasurableSet ((fun ω : Hist (Fin 2) 1 => (ω 0).2) ⁻¹' (reg k ⁻¹' {w})) :=
    (measurable_snd.comp (measurable_pi_apply 0)) (measurableSet_region k w)
  rw [hset, ← lintegral_indicator_one hm]
  have hprod := lintegral_prod_sched C certSched w
    (fun _ : ℕ => (reg k ⁻¹' {w}).indicator (1 : ℝ → ℝ≥0∞))
    (fun _ => measurable_one.indicator (measurableSet_region k w)) 1
  have hlhs : ∀ ω : Hist (Fin 2) 1,
      ∏ i : Fin 1, (reg k ⁻¹' {w}).indicator (1 : ℝ → ℝ≥0∞) (ω i).2
      = ((fun ω : Hist (Fin 2) 1 => (ω 0).2) ⁻¹' (reg k ⁻¹' {w})).indicator
          (1 : Hist (Fin 2) 1 → ℝ≥0∞) ω := by
    intro ω
    rw [Fin.prod_univ_one]
    by_cases h : (ω 0).2 ∈ reg k ⁻¹' {w}
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show ω ∈ (fun ω : Hist (Fin 2) 1 => (ω 0).2) ⁻¹' (reg k ⁻¹' {w})
          from h)]
      rfl
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show ω ∉ (fun ω : Hist (Fin 2) 1 => (ω 0).2) ⁻¹' (reg k ⁻¹' {w})
          from h)]
  simp_rw [hlhs] at hprod
  rw [hprod, Fin.prod_univ_one, lintegral_indicator_one (measurableSet_region k w)]
  show obsLawC C w 1 (reg k ⁻¹' {w}) = _
  unfold obsLawC
  rw [withDensity_apply _ (measurableSet_region k w)]
  have hd : ∀ y, C.dens w 1 y = cdens k ρ w y := fun y => by simp [C, certChan]
  simp_rw [hd, ofReal_cdens k hk ρ hρ0 hρ1 w]
  rw [← lintegral_indicator (measurableSet_region k w)]
  have hind : ∀ y, (reg k ⁻¹' {w}).indicator (fun y => ENNReal.ofReal (sym ρ w (reg k y)
      / B k (reg k y)) * ENNReal.ofReal (gaussianPDFReal 0 1 y)) y
      = (fun s => if s = w then ENNReal.ofReal (sym ρ w s / B k s) else 0) (reg k y)
        * ENNReal.ofReal (gaussianPDFReal 0 1 y) := by
    intro y
    by_cases h : reg k y = w
    · rw [Set.indicator_of_mem (by simpa using h)]; simp [h]
    · rw [Set.indicator_of_notMem (by simpa using h)]; simp [h]
  simp_rw [hind]
  rw [lintegral_region k (fun s => if s = w then ENNReal.ofReal (sym ρ w s / B k s) else 0),
    Finset.sum_eq_single w]
  · simp only [if_true]
    rw [← ofReal_B k w, ← ENNReal.ofReal_mul (div_pos (sym_pos hk ρ hρ0 hρ1 w w) (B_pos k w)).le,
      div_mul_cancel₀ _ (B_pos k w).ne']
    unfold sym; rw [if_pos rfl]
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cert_cost (hk : 2 ≤ k) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (w : Fin k) :
    costN (certChan k hk ρ hρ0 hρ1) (schedPolicy certSched) w 1 = 1 := by
  rw [costN_sched]
  unfold schedCost certSched
  simp [certChan]

theorem measurableSet_certOut (a : Fin k) (S : Finset (Fin k)) :
    MeasurableSet {ω : Hist (Fin 2) 1 | certOut k ω ∈ S} :=
  ((measurable_reg k).comp (measurable_snd.comp (measurable_pi_apply 0)))
    (Set.Finite.measurableSet (Set.toFinite _))

/-- **The KL lower law is attained, factor included.**  With `ρ = δ ≤ 1/k`: the one-query
policy is `δ`-safe at every world, pays one query, and every per-query KL is at most
`log(1/((k-1)δ))/(k-1)`. The law gives, at every world of the obstruction `Fin k`,
`((1-δ)/(k-1)) log(1/δ) - log 2 ≤ 1 · t_KL`: both sides are `log(1/δ)/(k-1)` to first order. -/
theorem cert_tight (hk : 2 ≤ k) (δ : ℝ) (hδ0 : 0 < δ) (hδk : δ ≤ 1 / k) :
    ∃ (C : Channel (Fin k) (Fin 2)),
      (∀ w, hist C (schedPolicy certSched) w 1 {ω | certOut k ω ∉ certSafe k w}
          = ENNReal.ofReal δ)
      ∧ (∀ w, costN C (schedPolicy certSched) w 1 = 1)
      ∧ (∀ w u q, klq C w u q
          ≤ ENNReal.ofReal (Real.log (1 / (((k : ℝ) - 1) * δ)) / ((k : ℝ) - 1)))
      ∧ ENNReal.ofReal ((1 - δ) / ((k : ℝ) - 1) * Real.log (1 / δ) - Real.log 2)
          ≤ ENNReal.ofReal (Real.log (1 / (((k : ℝ) - 1) * δ)) / ((k : ℝ) - 1)) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hδ1 : δ < 1 := by
    have : (1 : ℝ) / k < 1 := by rw [div_lt_one (by positivity)]; exact hk1
    linarith
  set C := certChan k hk δ hδ0 hδ1 with hC
  have herr := cert_error k hk δ hδ0 hδ1
  have hcost := cert_cost k hk δ hδ0 hδ1
  have hkl : ∀ w u q, klq C w u q
      ≤ ENNReal.ofReal (Real.log (1 / (((k : ℝ) - 1) * δ)) / ((k : ℝ) - 1)) :=
    fun w u q => klq_cert_le k hk δ hδ0 hδk w u q
  refine ⟨C, herr, hcost, hkl, ?_⟩
  -- the general lower law, applied at world 0 of the obstruction `Fin k`
  have hcorr : ∀ w, 1 - δ ≤ (hist C (schedPolicy certSched) w 1).real
      {ω | certOut k ω ∈ certSafe k w} := by
    intro w
    haveI := hist_prob C (schedPolicy certSched) w 1
    have hc : {ω : Hist (Fin 2) 1 | certOut k ω ∈ certSafe k w}
        = {ω | certOut k ω ∉ certSafe k w}ᶜ := by ext; simp
    rw [hc, measureReal_compl (by
      have := measurableSet_certOut k w (certSafe k w)
      exact this.compl), probReal_univ, measureReal_def, herr w, ENNReal.toReal_ofReal hδ0.le]
  set x : ℝ := Real.log (1 / (((k : ℝ) - 1) * δ)) / ((k : ℝ) - 1) with hx
  have hx0 : 0 ≤ x := by
    apply div_nonneg _ (by linarith)
    apply Real.log_nonneg
    rw [le_div_iff₀ (by nlinarith)]
    have : (k : ℝ) * δ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left hδk (by positivity : (0 : ℝ) ≤ k)
      rwa [mul_one_div_cancel (by positivity)] at this
    nlinarith
  set t : ℝ≥0 := (⟨x, hx0⟩ : ℝ≥0) with htdef
  have ht : (t : ℝ≥0∞) = ENNReal.ofReal x := by rw [ENNReal.coe_nnreal_eq]; rfl
  have hlaw := obstruction_lower C (schedPolicy certSched) 1 (certOut k) (certSafe k)
    (fun w => measurableSet_certOut k w (certSafe k w)) δ hδ0 hδ1.le hcorr Finset.univ
    (certSafe_unsafe k hk) (by rw [Finset.card_univ, Fintype.card_fin]; exact hk)
    ⟨0, by omega⟩ (Finset.mem_univ _) t
    (fun v _ _ q _ => by rw [ht]; exact hkl _ v q)
  rw [hcost, one_mul, ht, Finset.card_univ, Fintype.card_fin] at hlaw
  exact hlaw

#print axioms lintegral_region
#print axioms lintegral_cdens
#print axioms klq_cert_one
#print axioms kl_sum_eq
#print axioms klq_cert_le
#print axioms cert_error
#print axioms cert_cost
#print axioms cert_tight

end CIGAMF.P13.PaperBCertificateChannel
