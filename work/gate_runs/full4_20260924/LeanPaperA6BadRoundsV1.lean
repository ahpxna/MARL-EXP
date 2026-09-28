import «LeanPaperA6OracleLearnerV1»

/-!
# Paper A6: an oracle-tracking learner's estimate is wrong in only finitely many rounds

For the tracking learner `oLearner O` of ANY oracle (`LeanPaperA6OracleLearnerV1`), in any world
`theta` with noise `sigma > 0`:

* `radius_eventually` -- a deterministic `s0` after which a count `N >= sqrt s / K - (K - 1)`
  makes the confidence radius `sigma sqrt(2 (a + N) b_s) / N` smaller than `rho0`, where `b_s`
  bounds the threshold at level `s^{-4}` (`log s <= 4 s^{1/4}` beats nothing faster than
  `sqrt s`);
* `close_of_good` -- after `s0`, on the event that the learner's own statistic stays below that
  threshold, EVERY cell's estimate is within `rho0` of the truth.  Forcing supplies the counts;
  Ville (`good_window_real`) supplies the event;
* `badAll` -- the number of post-warm rounds before `t` at which some estimate is off by
  `rho0` or more;
* `badAll_expect` -- **`E[badAll t] <= s0 + 2` for EVERY horizon `t`**: `s0` rounds, plus
  `sum_s s^{-4} <= 2` for the failures of the confidence event.

Nothing here depends on the oracle; the oracle enters only through the counts, and forcing
alone gives those.
-/

namespace CIGAMF.P13.PaperA6BadRounds

open Finset MeasureTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7IdealLearner
open CIGAMF.P13.PaperA7Confidence (bthr)
open CIGAMF.P13.PaperA6OracleLearner

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]

/-! ## 1. Real analysis: the radius eventually falls below any `rho0` -/

theorem log_le_four_rt (s : ℝ) (hs : 1 ≤ s) :
    Real.log s ≤ 4 * Real.sqrt (Real.sqrt s) := by
  set y := Real.sqrt (Real.sqrt s) with hy
  have hy0 : 0 < y := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hy4 : y ^ 4 = s := by
    have h1 : Real.sqrt s ^ 2 = s := Real.sq_sqrt (by linarith)
    have h2 : y ^ 2 = Real.sqrt s := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = s := by rw [h2, h1]
  have hl : Real.log s = 4 * Real.log y := by
    rw [← hy4, Real.log_pow]; norm_num
  have := Real.log_le_sub_one_of_pos hy0
  rw [hl]
  linarith

theorem log_one_add_le (s a : ℝ) (hs : 1 ≤ s) (ha : 0 < a) :
    Real.log (1 + s / a) ≤ Real.log s + Real.log (1 + 1 / a) := by
  have hs0 : 0 < s := by linarith
  have h1 : 1 + s / a ≤ s * (1 + 1 / a) := by
    have : 1 ≤ s := hs
    have : s * (1 + 1 / a) = s + s / a := by field_simp
    rw [this]; linarith
  rw [← Real.log_mul hs0.ne' (by positivity)]
  exact Real.log_le_log (by positivity) h1

/-- The threshold's size at level `s^{-4}`, when every count is at most `s`. -/
noncomputable def bS (K : ℕ) (a s : ℝ) : ℝ := 4 * Real.log s + (K / 2) * Real.log (1 + s / a)

/-- **After `s0`, the radius is below `rho0`.** -/
theorem radius_eventually (K : ℕ) (hK : 1 ≤ K) (a σ2 ρ₀ : ℝ) (ha : 0 < a) (hσ2 : 0 < σ2)
    (hρ : 0 < ρ₀) :
    ∃ s₀ : ℕ, K ≤ s₀ ∧ 1 ≤ s₀ ∧ ∀ s : ℕ, s₀ ≤ s → ∀ N : ℝ,
      Real.sqrt (s : ℝ) / K - ((K : ℝ) - 1) ≤ N →
        1 ≤ N ∧ σ2 * (2 * (a + N) * bS K a s) < ρ₀ ^ 2 * N ^ 2 := by
  have hK0 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set c₀ : ℝ := 4 + K / 2 with hc₀
  set c₁ : ℝ := (K / 2) * Real.log (1 + 1 / a) with hc₁
  have hc₁0 : 0 ≤ c₁ := by
    have : 0 ≤ Real.log (1 + 1 / a) := Real.log_nonneg (by
      have h : 0 < 1 / a := (by positivity)
      linarith)
    positivity
  set Y₁ : ℝ := 8 * K * σ2 / ρ₀ ^ 2 * (4 * c₀ + c₁) with hY₁
  set Y : ℝ := 1 + 2 * K * (K - 1) + 2 * K * a + 2 * K + Y₁ with hY
  have hY₁0 : 0 ≤ Y₁ := by positivity
  have hKm : 0 ≤ (K : ℝ) - 1 := by linarith
  have hY1 : 1 ≤ Y := by
    have : 0 ≤ 2 * (K : ℝ) * (K - 1) := by positivity
    have : 0 ≤ 2 * (K : ℝ) * a := by positivity
    linarith
  refine ⟨⌈Y ^ 4⌉₊ + K, by omega, by omega, fun s hs N hN => ?_⟩
  have hsY : Y ^ 4 ≤ (s : ℝ) := by
    have h1 : Y ^ 4 ≤ (⌈Y ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Y ^ 4⌉₊ : ℕ) : ℝ) ≤ s := by exact_mod_cast (le_trans (Nat.le_add_right _ _) hs)
    linarith
  have hs1 : (1 : ℝ) ≤ s := le_trans (one_le_pow₀ hY1) hsY
  set y := Real.sqrt (Real.sqrt (s : ℝ)) with hy
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y ^ 2 = Real.sqrt (s : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hy4 : y ^ 4 = (s : ℝ) := by
    have h1 : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) := Real.sq_sqrt (by linarith)
    calc y ^ 4 = (y ^ 2) ^ 2 := by ring
      _ = (s : ℝ) := by rw [hy2, h1]
  have hyY : Y ≤ y := by
    by_contra hc
    push_neg at hc
    have : y ^ 4 < Y ^ 4 := pow_lt_pow_left₀ hc hy0 (by norm_num)
    linarith
  have hy1 : 1 ≤ y := le_trans hY1 hyY
  have hyy : y ≤ y ^ 2 := by nlinarith
  -- the count floor
  have hN0 : y ^ 2 / (2 * K) ≤ N := by
    have hsq : Real.sqrt (s : ℝ) = y ^ 2 := hy2.symm
    rw [hsq] at hN
    have h2 : 2 * (K : ℝ) * (K - 1) ≤ y ^ 2 := by
      have : 2 * (K : ℝ) * (K - 1) ≤ Y := by
        have : 0 ≤ 2 * (K : ℝ) * a := by positivity
        linarith
      linarith
    have : y ^ 2 / (2 * K) ≤ y ^ 2 / K - (K - 1) := by
      rw [div_le_iff₀ (by positivity)]
      have : (y ^ 2 / K - (K - 1)) * (2 * K) = 2 * y ^ 2 - 2 * K * (K - 1) := by
        field_simp; try ring
      rw [this]; linarith
    linarith
  have hNa : a ≤ N := by
    have : 2 * (K : ℝ) * a ≤ y ^ 2 := by
      have : 2 * (K : ℝ) * a ≤ Y := by
        have : 0 ≤ 2 * (K : ℝ) * (K - 1) := by positivity
        linarith
      linarith
    have : a ≤ y ^ 2 / (2 * K) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hN1 : 1 ≤ N := by
    have : 2 * (K : ℝ) ≤ y ^ 2 := by
      have : 2 * (K : ℝ) ≤ Y := by
        have : 0 ≤ 2 * (K : ℝ) * (K - 1) := by positivity
        have : 0 ≤ 2 * (K : ℝ) * a := by positivity
        linarith
      linarith
    have : 1 ≤ y ^ 2 / (2 * K) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  refine ⟨hN1, ?_⟩
  -- the threshold's size
  have hB : bS K a s ≤ 4 * c₀ * y + c₁ := by
    unfold bS
    have hl := log_le_four_rt (s : ℝ) hs1
    have hl2 := log_one_add_le (s : ℝ) a hs1 ha
    rw [← hy] at hl
    have hls : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs1
    have : 4 * Real.log (s : ℝ) + (K / 2) * Real.log (1 + s / a)
        ≤ c₀ * Real.log (s : ℝ) + c₁ := by
      rw [hc₀, hc₁]
      have := mul_le_mul_of_nonneg_left hl2 (by positivity : (0 : ℝ) ≤ K / 2)
      linarith
    have : c₀ * Real.log (s : ℝ) ≤ c₀ * (4 * y) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    linarith
  have hBnn : 0 ≤ bS K a s := by
    unfold bS
    have : 0 ≤ Real.log (s : ℝ) := Real.log_nonneg hs1
    have : 0 ≤ Real.log (1 + s / a) := Real.log_nonneg (by
      have h : 0 ≤ (s : ℝ) / a := (by positivity)
      linarith)
    positivity
  -- `2 sigma2 (a + N) b <= 4 sigma2 N b < rho0^2 N^2`
  have hstep1 : σ2 * (2 * (a + N) * bS K a s) ≤ 4 * σ2 * N * bS K a s := by
    have h : a + N ≤ 2 * N := by linarith
    have h2 : 0 ≤ 2 * σ2 * bS K a s := by positivity
    calc σ2 * (2 * (a + N) * bS K a s) = (2 * σ2 * bS K a s) * (a + N) := by ring
      _ ≤ (2 * σ2 * bS K a s) * (2 * N) := mul_le_mul_of_nonneg_left h h2
      _ = 4 * σ2 * N * bS K a s := by ring
  have hkey : 4 * σ2 * bS K a s < ρ₀ ^ 2 * N := by
    have h1 : 4 * σ2 * bS K a s ≤ 4 * σ2 * (4 * c₀ * y + c₁) :=
      mul_le_mul_of_nonneg_left hB (by positivity)
    have h2 : 4 * σ2 * (4 * c₀ * y + c₁) ≤ 4 * σ2 * (4 * c₀ + c₁) * y := by
      have hc : c₁ ≤ c₁ * y := le_mul_of_one_le_right hc₁0 hy1
      have h4 : 0 ≤ 4 * σ2 := by positivity
      have hm := mul_le_mul_of_nonneg_left hc h4
      have e : 4 * σ2 * (4 * c₀ + c₁) * y = 4 * σ2 * (4 * c₀ * y) + 4 * σ2 * (c₁ * y) := by ring
      have e' : 4 * σ2 * (4 * c₀ * y + c₁) = 4 * σ2 * (4 * c₀ * y) + 4 * σ2 * c₁ := by ring
      rw [e, e']
      linarith
    have h3 : 4 * σ2 * (4 * c₀ + c₁) * y < ρ₀ ^ 2 * (y ^ 2 / (2 * K)) := by
      have hYy : Y₁ < y := by
        have g1 : 0 ≤ 2 * (K : ℝ) * (K - 1) := mul_nonneg (by positivity) hKm
        have g2 : 0 ≤ 2 * (K : ℝ) * a := by positivity
        have g3 : 0 ≤ 2 * (K : ℝ) := by positivity
        linarith
      have hρ2 : 0 < ρ₀ ^ 2 := by positivity
      have e1 : ρ₀ ^ 2 * (y ^ 2 / (2 * K)) = ρ₀ ^ 2 / (2 * K) * y * y := by ring
      have e2 : 4 * σ2 * (4 * c₀ + c₁) = ρ₀ ^ 2 / (2 * K) * Y₁ := by
        rw [hY₁]; field_simp; ring
      rw [e1, e2]
      have hpos : 0 < ρ₀ ^ 2 / (2 * K) * y := by
        have : 0 < y := by linarith
        positivity
      have hm := mul_lt_mul_of_pos_left hYy hpos
      calc ρ₀ ^ 2 / (2 * K) * Y₁ * y = (ρ₀ ^ 2 / (2 * K) * y) * Y₁ := by ring
        _ < (ρ₀ ^ 2 / (2 * K) * y) * y := hm
    have h4 : ρ₀ ^ 2 * (y ^ 2 / (2 * K)) ≤ ρ₀ ^ 2 * N :=
      mul_le_mul_of_nonneg_left hN0 (by positivity)
    linarith
  have hNpos : 0 < N := by linarith
  calc σ2 * (2 * (a + N) * bS K a s) ≤ 4 * σ2 * N * bS K a s := hstep1
    _ = (4 * σ2 * bS K a s) * N := by ring
    _ < (ρ₀ ^ 2 * N) * N := mul_lt_mul_of_pos_right hkey hNpos
    _ = ρ₀ ^ 2 * N ^ 2 := by ring

/-! ## 2. After `s0`, on the good event, every estimate is close -/

variable (O : Oracle E)

theorem oCount_le_t (θ σ : E → ℝ) (ω : ℕ → ℝ) (t : ℕ) (e : E) :
    Nc (oLearner O) θ σ t ω e ≤ t := by
  unfold Nc NF
  have : ∑ i : Fin t, (if (histF (oLearner O) θ σ t (Xp t ω) i).1 = e then (1 : ℕ) else 0)
      ≤ ∑ _i : Fin t, (1 : ℕ) := sum_le_sum fun i _ => by split_ifs <;> norm_num
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
  exact_mod_cast this

/-- The confidence event at round `s` fails. -/
def failAt (a : ℝ) (θ σ : E → ℝ) (s : ℕ) (ω : ℕ → ℝ) : Prop :=
  bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ s ω)
    < PaperA7Confidence.Qstat a (Sc (oLearner O) θ σ s ω) (Nc (oLearner O) θ σ s ω)

theorem measurableSet_failAt (a : ℝ) (θ σ : E → ℝ) (s : ℕ) :
    MeasurableSet {ω | failAt O a θ σ s ω} :=
  measurableSet_lt (measurable_bthr (oLearner O) θ σ a _ s)
    (measurable_Qstat (oLearner O) θ σ a s)

theorem bthr_le_bS (a : ℝ) (ha : 0 < a) (θ σ : E → ℝ) (s : ℕ) (hs : 1 ≤ s) (ω : ℕ → ℝ) :
    bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ s ω) ≤ bS (Fintype.card E) a s := by
  unfold bthr bS
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h1 : Real.log (1 / ((s : ℝ) ^ 4)⁻¹) = 4 * Real.log s := by
    rw [one_div, inv_inv, Real.log_pow]; norm_num
  rw [h1]
  have hsum : ∑ e, Real.log (1 + Nc (oLearner O) θ σ s ω e / a)
      ≤ ∑ _e : E, Real.log (1 + s / a) := by
    refine sum_le_sum fun e _ => ?_
    have hN0 : 0 ≤ Nc (oLearner O) θ σ s ω e := by unfold Nc; exact Nat.cast_nonneg _
    exact Real.log_le_log (by positivity)
      (by have := oCount_le_t O θ σ ω s e; gcongr)
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum
  have : (∑ e, Real.log (1 + Nc (oLearner O) θ σ s ω e / a)) / 2
      ≤ (Fintype.card E : ℝ) / 2 * Real.log (1 + s / a) := by
    have := div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 2)
    linarith [show (Fintype.card E : ℝ) * Real.log (1 + s / a) / 2
      = (Fintype.card E : ℝ) / 2 * Real.log (1 + s / a) by ring]
  linarith

/-- **After `s0`, on the good event, every estimate is within `rho0` of the truth.** -/
theorem close_of_good (a : ℝ) (ha : 0 < a) (θ σ : E → ℝ) (hσ : ∀ e, 0 < σ e) (σ2 : ℝ)
    (hσ2 : ∀ e, σ e ^ 2 ≤ σ2) (ρ₀ : ℝ) (s₀ : ℕ) (hs₀K : Fintype.card E ≤ s₀) (hs₀1 : 1 ≤ s₀)
    (hs₀ : ∀ s : ℕ, s₀ ≤ s → ∀ N : ℝ,
      Real.sqrt (s : ℝ) / Fintype.card E - ((Fintype.card E : ℝ) - 1) ≤ N →
        1 ≤ N ∧ σ2 * (2 * (a + N) * bS (Fintype.card E) a s) < ρ₀ ^ 2 * N ^ 2)
    (hρ : 0 < ρ₀) (s : ℕ) (hs : s₀ ≤ s) (ω : ℕ → ℝ) (hgood : ¬ failAt O a θ σ s ω) (e : E) :
    |hMu (oRun O θ σ s ω) e - θ e| < ρ₀ := by
  obtain ⟨k, rfl⟩ : ∃ k, s = Fintype.card E + k := ⟨s - Fintype.card E, by omega⟩
  set s := Fintype.card E + k with hsdef
  set N := Nc (oLearner O) θ σ s ω e with hNdef
  have hfloor := oCount_ge O θ σ ω k e
  obtain ⟨hN1, hsmall⟩ := hs₀ s hs N hfloor
  have hQ : PaperA7Confidence.Qstat a (Sc (oLearner O) θ σ s ω) (Nc (oLearner O) θ σ s ω)
      ≤ bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ s ω) := not_lt.mp hgood
  have hNe : 0 < NF (oLearner O) θ σ s (Xp s ω) e := by
    have : (1 : ℝ) ≤ (NF (oLearner O) θ σ s (Xp s ω) e : ℝ) := hN1
    exact_mod_cast (lt_of_lt_of_le zero_lt_one this)
  have hrad := radius_of_good (oLearner O) θ σ a ha hσ s (Xp s ω) _ hQ e hNe
  have hmu : hMu (oRun O θ σ s ω) e
      = Ysum (oLearner O) θ σ s (Xp s ω) e / (NF (oLearner O) θ σ s (Xp s ω) e : ℝ) := by
    unfold hMu
    rw [hN_oRun]
    rfl
  rw [hmu]
  refine lt_of_le_of_lt hrad ?_
  have hb := bthr_le_bS O a ha θ σ s (by omega) ω
  have hNpos : (0 : ℝ) < (NF (oLearner O) θ σ s (Xp s ω) e : ℝ) := by exact_mod_cast hNe
  have hNN : ((NF (oLearner O) θ σ s (Xp s ω) e : ℕ) : ℝ) = N := rfl
  rw [hNN] at hNpos ⊢
  have hX0 : 0 ≤ 2 * (a + N) * bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ s ω) := by
    have hQ0 : 0 ≤ PaperA7Confidence.Qstat a (Sc (oLearner O) θ σ s ω) (Nc (oLearner O) θ σ s ω) := by
      unfold PaperA7Confidence.Qstat
      refine sum_nonneg fun e' _ => div_nonneg (sq_nonneg _) ?_
      have : 0 ≤ Nc (oLearner O) θ σ s ω e' := by unfold Nc; exact Nat.cast_nonneg _
      positivity
    have : 0 ≤ bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ s ω) := le_trans hQ0 hQ
    positivity
  have hle : Real.sqrt (2 * (a + N) * bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ s ω))
      ≤ Real.sqrt (2 * (a + N) * bS (Fintype.card E) a s) := by
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 2 * (a + N) := by positivity
    exact mul_le_mul_of_nonneg_left hb this
  have hX1 : 0 ≤ 2 * (a + N) * bS (Fintype.card E) a s := le_trans hX0
    (mul_le_mul_of_nonneg_left hb (by positivity))
  rw [div_lt_iff₀ hNpos]
  have hσe := hσ e
  have h1 : σ e * Real.sqrt (2 * (a + N) * bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ s ω))
      ≤ σ e * Real.sqrt (2 * (a + N) * bS (Fintype.card E) a s) :=
    mul_le_mul_of_nonneg_left hle hσe.le
  have h2 : σ e * Real.sqrt (2 * (a + N) * bS (Fintype.card E) a s) < ρ₀ * N := by
    have hsq : (σ e * Real.sqrt (2 * (a + N) * bS (Fintype.card E) a s)) ^ 2
        = σ e ^ 2 * (2 * (a + N) * bS (Fintype.card E) a s) := by
      rw [mul_pow, Real.sq_sqrt hX1]
    have hlt : (σ e * Real.sqrt (2 * (a + N) * bS (Fintype.card E) a s)) ^ 2 < (ρ₀ * N) ^ 2 := by
      rw [hsq, mul_pow]
      have := mul_le_mul_of_nonneg_right (hσ2 e) hX1
      linarith
    have h0 : 0 ≤ ρ₀ * N := by positivity
    exact lt_of_pow_lt_pow_left₀ 2 h0 hlt
  linarith

/-! ## 3. The number of bad rounds, in expectation -/

open Classical in
/-- The post-warm rounds before `t` at which some estimate is off by `rho0` or more. -/
noncomputable def badAll (θ σ : E → ℝ) (ρ₀ : ℝ) (ω : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ s ∈ range t, if Fintype.card E ≤ s ∧ ¬ (∀ e, |hMu (oRun O θ σ s ω) e - θ e| < ρ₀)
    then 1 else 0

theorem badAll_nonneg (θ σ : E → ℝ) (ρ₀ : ℝ) (ω : ℕ → ℝ) (t : ℕ) : 0 ≤ badAll O θ σ ρ₀ ω t :=
  sum_nonneg fun s _ => by split_ifs <;> norm_num

theorem badAll_mono (θ σ : E → ℝ) (ρ₀ : ℝ) (ω : ℕ → ℝ) {t t' : ℕ} (h : t ≤ t') :
    badAll O θ σ ρ₀ ω t ≤ badAll O θ σ ρ₀ ω t' := by
  unfold badAll
  exact sum_le_sum_of_subset_of_nonneg (range_mono h) fun s _ _ => by split_ifs <;> norm_num

theorem sum_inv_pow4_le : ∀ t : ℕ,
    ∑ s ∈ range t, (((s : ℝ) + 1) ^ 4)⁻¹ ≤ 2 - 2 / ((t : ℝ) + 1)
  | 0 => by simp
  | t + 1 => by
      rw [sum_range_succ]
      have ih := sum_inv_pow4_le t
      have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      have hstep : (((t : ℝ) + 1) ^ 4)⁻¹ ≤ 2 / ((t : ℝ) + 1) - 2 / (((t + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        have h1 : 2 / ((t : ℝ) + 1) - 2 / ((t : ℝ) + 1 + 1) = 2 / (((t : ℝ) + 1) * ((t : ℝ) + 2)) := by
          field_simp; try ring
        rw [h1, inv_le_comm₀ (by positivity) (by positivity), inv_div]
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        nlinarith [sq_nonneg ((t : ℝ) + 1), mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]
      linarith

/-- **`E[badAll t] <= s0 + 2`, for every horizon `t`.** -/
theorem badAll_expect (a : ℝ) (ha : 0 < a) (θ σ : E → ℝ) (hσ : ∀ e, 0 < σ e) (σ2 : ℝ)
    (hσ2 : ∀ e, σ e ^ 2 ≤ σ2) (ρ₀ : ℝ) (hρ : 0 < ρ₀) (s₀ : ℕ) (hs₀K : Fintype.card E ≤ s₀)
    (hs₀1 : 1 ≤ s₀)
    (hs₀ : ∀ s : ℕ, s₀ ≤ s → ∀ N : ℝ,
      Real.sqrt (s : ℝ) / Fintype.card E - ((Fintype.card E : ℝ) - 1) ≤ N →
        1 ≤ N ∧ σ2 * (2 * (a + N) * bS (Fintype.card E) a s) < ρ₀ ^ 2 * N ^ 2)
    (t : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (badAll O θ σ ρ₀ ω t) ∂streamMeasure ≤ ENNReal.ofReal ((s₀ : ℝ) + 2) := by
  classical
  set A : ℕ → Set (ℕ → ℝ) := fun s => {ω | s₀ ≤ s ∧ failAt O a θ σ s ω} with hA
  have hAm : ∀ s, MeasurableSet (A s) := fun s =>
    (MeasurableSet.const _).inter (measurableSet_failAt O a θ σ s)
  -- pathwise: before `s0` at most one per round, after it only failures of the good event
  have hterm : ∀ ω, ∀ s ∈ range t,
      ENNReal.ofReal (if Fintype.card E ≤ s ∧ ¬ (∀ e, |hMu (oRun O θ σ s ω) e - θ e| < ρ₀)
        then (1 : ℝ) else 0)
        ≤ (if s < s₀ then (1 : ℝ≥0∞) else 0) + (A s).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω s _
    by_cases hs : s < s₀
    · rw [if_pos hs]
      have h1 : ENNReal.ofReal (if Fintype.card E ≤ s ∧
          ¬ (∀ e, |hMu (oRun O θ σ s ω) e - θ e| < ρ₀) then (1 : ℝ) else 0) ≤ 1 := by
        split_ifs <;> simp
      exact le_trans h1 le_self_add
    · rw [if_neg hs, zero_add]
      by_cases hb : Fintype.card E ≤ s ∧ ¬ (∀ e, |hMu (oRun O θ σ s ω) e - θ e| < ρ₀)
      · rw [if_pos hb, ENNReal.ofReal_one]
        have hfail : failAt O a θ σ s ω := by
          by_contra hg
          exact hb.2 (fun e => close_of_good O a ha θ σ hσ σ2 hσ2 ρ₀ s₀ hs₀K hs₀1 hs₀ hρ s
            (not_lt.mp hs) ω hg e)
        have hmem : ω ∈ A s := ⟨not_lt.mp hs, hfail⟩
        rw [Set.indicator_of_mem hmem]
      · rw [if_neg hb, ENNReal.ofReal_zero]
        exact zero_le
  have hpath : ∀ ω, ENNReal.ofReal (badAll O θ σ ρ₀ ω t)
      ≤ (s₀ : ℝ≥0∞) + ∑ s ∈ range t, (A s).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    intro ω
    unfold badAll
    rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by split_ifs <;> norm_num)]
    refine le_trans (sum_le_sum (hterm ω)) ?_
    rw [sum_add_distrib]
    have hcount : ∑ s ∈ range t, (if s < s₀ then (1 : ℝ≥0∞) else 0) ≤ s₀ := by
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have hsub : (range t).filter (fun s => s < s₀) ⊆ range s₀ := by
        intro s hs
        simp only [mem_filter, mem_range] at hs ⊢
        exact hs.2
      have := card_le_card hsub
      rw [card_range] at this
      exact_mod_cast this
    exact add_le_add hcount le_rfl
  refine le_trans (lintegral_mono hpath) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_finset_sum _ fun s _ => (measurable_const.indicator (hAm s))]
  have hsum_eq : ∑ s ∈ range t, ∫⁻ ω, (A s).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂streamMeasure
      = ∑ s ∈ range t, streamMeasure (A s) :=
    Finset.sum_congr rfl fun s _ => by rw [lintegral_indicator_const (hAm s), one_mul]
  rw [hsum_eq]
  -- each failure has probability at most `s^{-4}`
  have hfs : ∀ s ∈ range t, streamMeasure (A s)
      ≤ ENNReal.ofReal (if s₀ ≤ s then ((s : ℝ) ^ 4)⁻¹ else 0) := by
    intro s _
    by_cases hs : s₀ ≤ s
    · rw [if_pos hs]
      have hs1 : 1 ≤ s := le_trans hs₀1 hs
      have hw := good_window_real (oLearner O) θ σ a ha s s hs1
      have hsub : A s ⊆ {ω | ∃ j, s ≤ j ∧ j ≤ s ∧
          bthr a ((j : ℝ) ^ 4)⁻¹ (Nc (oLearner O) θ σ j ω)
            < PaperA7Confidence.Qstat a (Sc (oLearner O) θ σ j ω) (Nc (oLearner O) θ σ j ω)} :=
        fun ω hω => ⟨s, le_rfl, le_rfl, hω.2⟩
      have hreal := (measureReal_mono hsub (measure_ne_top _ _)).trans hw
      rw [← ENNReal.ofReal_toReal (measure_ne_top streamMeasure (A s))]
      exact ENNReal.ofReal_le_ofReal hreal
    · rw [if_neg hs, ENNReal.ofReal_zero]
      have : A s = ∅ := by
        ext ω
        simp only [hA, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd h hs
      rw [this, measure_empty]
  have hstep : (s₀ : ℝ≥0∞) + ∑ s ∈ range t, streamMeasure (A s)
      ≤ (s₀ : ℝ≥0∞) + ∑ s ∈ range t, ENNReal.ofReal (if s₀ ≤ s then ((s : ℝ) ^ 4)⁻¹ else 0) :=
    add_le_add le_rfl (sum_le_sum hfs)
  refine le_trans hstep ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => by split_ifs <;> positivity),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_add (Nat.cast_nonneg _)
      (sum_nonneg fun s _ => by split_ifs <;> positivity)]
  apply ENNReal.ofReal_le_ofReal
  have htail : ∑ s ∈ range t, (if s₀ ≤ s then ((s : ℝ) ^ 4)⁻¹ else 0) ≤ 2 := by
    rcases Nat.eq_zero_or_pos t with ht | ht
    · subst ht; simp
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
    rw [sum_range_succ']
    have h0 : (if s₀ ≤ 0 then (((0 : ℕ) : ℝ) ^ 4)⁻¹ else 0) = 0 := if_neg (by omega)
    rw [h0, add_zero]
    have hle : ∀ i ∈ range n, (if s₀ ≤ i + 1 then (((i + 1 : ℕ) : ℝ) ^ 4)⁻¹ else 0)
        ≤ (((i : ℝ) + 1) ^ 4)⁻¹ := by
      intro i _
      split_ifs
      · push_cast; exact le_rfl
      · positivity
    refine le_trans (sum_le_sum hle) ?_
    have := sum_inv_pow4_le n
    have : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
    linarith
  linarith

#print axioms radius_eventually
#print axioms close_of_good
#print axioms badAll_expect

end CIGAMF.P13.PaperA6BadRounds
