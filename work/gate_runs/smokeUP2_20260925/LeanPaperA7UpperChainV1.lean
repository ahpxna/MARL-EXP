import «LeanPaperAENatExpectV1»
import «LeanPaperA7ThresholdV1»
import «LeanPaperAEndgameV1»

/-!
# Paper A7: from a direct lower bound on the statistic to the rate, on `ℕ∞`

Blueprint 02, sections 7 and 8, rebuilt on the untruncated hitting time.  The earlier chain
(`LeanPaperA7ChainV1`) takes `tau : Ω → ℕ` and an increment hypothesis `hinit`; this module
takes instead

* `tau : Ω → ℕ∞`, the first CHECK time (a multiple of `c`, `c = 50` in the code) at which the
  certified statistic exceeds the threshold (`hfire` records only that property);
* a window event `Gd t` on which the statistic has already crossed at time `t`
  (`hwin`) -- produced by `win_of_direct` from a DIRECT lower bound `Gm t - D <= Zlo t`
  (`LeanPaperA7DirectLowerV1`) and the code's threshold
  `log(1/alpha) + (K/2) log(1 + t/a)` (`threshold_crossing_time`);
* a summable bound on the probability of the window's failure at the last check time.

`expect_le` gives `E tau <= t1 + c + sum f` directly, through the layer-cake identity of
`LeanPaperAENatExpectV1`; no truncation, no assumption that `tau` is finite.
`upper_rate_of_bound` turns bounds `E tau_delta <= log(1/delta)/(Gamma - eta) + A_eta`, for
every slack `eta > 0`, into `UpperRate` at `Gamma`.
-/

namespace CIGAMF.P13.PaperA7UpperChain

open MeasureTheory
open scoped ENNReal
open CIGAMF.P13.PaperAENatExpect CIGAMF.P13.PaperA7Threshold

/-- The last check time at or before `t`. -/
def lastCheck (c t : ℕ) : ℕ := t / c * c

theorem lastCheck_le (c t : ℕ) : lastCheck c t ≤ t := Nat.div_mul_le_self t c

theorem lastCheck_dvd (c t : ℕ) : c ∣ lastCheck c t := Dvd.intro_left _ rfl

theorem lastCheck_gt (c t : ℕ) (hc : 0 < c) : t < lastCheck c t + c := by
  unfold lastCheck
  have := (Nat.div_lt_iff_lt_mul hc).mp (Nat.lt_succ_self (t / c))
  rw [Nat.succ_mul] at this
  exact this

/-- **Tail inclusion and the expected hitting time.** -/
theorem expect_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → ℕ∞) (hτ : Measurable τ) (c : ℕ) (hc : 0 < c) (Zlo thr : Ω → ℕ → ℝ)
    (Gd : ℕ → Set Ω)
    (hfire : ∀ ω t, c ∣ t → thr ω t < Zlo ω t → τ ω ≤ t)
    (t1 : ℕ) (hwin : ∀ ω t, t1 ≤ t → ω ∈ Gd t → thr ω t < Zlo ω t)
    (f : ℕ → ℝ) (hf0 : ∀ t, 0 ≤ f t) (hfs : Summable f)
    (hbad : ∀ t, t1 + c ≤ t → μ (Gd (lastCheck c t))ᶜ ≤ ENNReal.ofReal (f t)) :
    ∫⁻ ω, (τ ω : ℝ≥0∞) ∂μ ≤ ((t1 + c : ℕ) : ℝ≥0∞) + ENNReal.ofReal (∑' t, f t) := by
  refine lintegral_le_of_tail μ τ hτ (t1 + c) f hf0 hfs fun t ht => ?_
  refine le_trans (measure_mono fun ω hω => ?_) (hbad t ht)
  intro hG
  have hlc : t1 ≤ lastCheck c t := by have := lastCheck_gt c t hc; omega
  have hle := hfire ω _ (lastCheck_dvd c t) (hwin ω _ hlc hG)
  have hlt : (t : ℕ∞) < (lastCheck c t : ℕ∞) := lt_of_lt_of_le hω hle
  have : t < lastCheck c t := by exact_mod_cast hlt
  exact absurd (lastCheck_le c t) (not_le.mpr this)

/-- The sublinear part of the code's threshold, at slope `kappa Gm`. -/
noncomputable def thrI (K a κ Gm : ℝ) : ℝ :=
  (K / 2) * (2 * a * κ * Gm / K - Real.log (2 * a * κ * Gm / K) - 1)

theorem half_log_le (K a κ Gm t : ℝ) (hK : 0 < K) (ha : 0 < a) (hκ : 0 < κ) (hGm : 0 < Gm)
    (ht : 0 ≤ t) :
    (K / 2) * Real.log (1 + t / a) ≤ κ * Gm * t + thrI K a κ Gm := by
  have hc : 0 < 2 * a * κ * Gm / K := by positivity
  have hy : 0 < 1 + t / a := by positivity
  have h := log_le_linear (2 * a * κ * Gm / K) (1 + t / a) hc hy
  have hK2 : 0 ≤ K / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hK2
  unfold thrI
  have heq : K / 2 * (2 * a * κ * Gm / K * (1 + t / a) - Real.log (2 * a * κ * Gm / K) - 1)
      = κ * Gm * t + K / 2 * (2 * a * κ * Gm / K - Real.log (2 * a * κ * Gm / K) - 1) := by
    field_simp
    ring
  linarith

/-- The crossing time of the code's threshold. -/
noncomputable def crossT (L D K a κ Gm : ℝ) : ℕ :=
  ⌈(L + D + thrI K a κ Gm) / ((1 - κ) * Gm)⌉₊ + 1

/-- **Threshold crossing**: past `crossT`, the direct bound exceeds the code's threshold. -/
theorem threshold_crossing_time (L D K a κ Gm : ℝ) (hK : 0 < K) (ha : 0 < a) (hκ : 0 < κ)
    (hκ1 : κ < 1) (hGm : 0 < Gm) (t : ℕ) (ht : crossT L D K a κ Gm ≤ t) :
    L + (K / 2) * Real.log (1 + t / a) < Gm * t - D := by
  have hden : 0 < (1 - κ) * Gm := by nlinarith
  have hceil := Nat.le_ceil ((L + D + thrI K a κ Gm) / ((1 - κ) * Gm))
  have htR : ((L + D + thrI K a κ Gm) / ((1 - κ) * Gm)) < t := by
    have : (⌈(L + D + thrI K a κ Gm) / ((1 - κ) * Gm)⌉₊ : ℝ) + 1 ≤ t := by
      unfold crossT at ht; exact_mod_cast ht
    linarith
  have h1 : L + D + thrI K a κ Gm < (1 - κ) * Gm * t := by
    rw [div_lt_iff₀ hden] at htR; linarith
  have h2 := half_log_le K a κ Gm t hK ha hκ hGm (Nat.cast_nonneg t)
  nlinarith

/-- **The window condition from the direct bound.** -/
theorem win_of_direct {Ω : Type*} (Zlo thr : Ω → ℕ → ℝ) (Gd : ℕ → Set Ω) (L D K a κ Gm : ℝ)
    (hK : 0 < K) (ha : 0 < a) (hκ : 0 < κ) (hκ1 : κ < 1) (hGm : 0 < Gm) (T0 : ℕ)
    (hdirect : ∀ ω t, T0 ≤ t → ω ∈ Gd t → Gm * t - D ≤ Zlo ω t)
    (hthr : ∀ ω (t : ℕ), thr ω t ≤ L + (K / 2) * Real.log (1 + t / a)) :
    ∀ ω t, max T0 (crossT L D K a κ Gm) ≤ t → ω ∈ Gd t → thr ω t < Zlo ω t := by
  intro ω t ht hG
  have h1 := hdirect ω t (le_trans (le_max_left _ _) ht) hG
  have h2 := threshold_crossing_time L D K a κ Gm hK ha hκ hκ1 hGm t
    (le_trans (le_max_right _ _) ht)
  linarith [hthr ω t]

/-- The code's threshold is at most `log(1/alpha) + (K/2) log(1 + t/a)` when every count is at
most `t`. -/
theorem code_thr_le {E : Type*} [Fintype E] (a : ℝ) (ha : 0 < a) (N : E → ℝ)
    (hN0 : ∀ e, 0 ≤ N e) (t : ℝ) (hNt : ∀ e, N e ≤ t) (L : ℝ) :
    L + (∑ e, Real.log (1 + N e / a)) / 2
      ≤ L + ((Fintype.card E : ℝ) / 2) * Real.log (1 + t / a) := by
  have h : ∑ e, Real.log (1 + N e / a) ≤ ∑ _e : E, Real.log (1 + t / a) :=
    Finset.sum_le_sum fun e _ => Real.log_le_log (by have := hN0 e; positivity)
      (by have := hNt e; have : N e / a ≤ t / a := div_le_div_of_nonneg_right this ha.le
          linarith)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  linarith

/-- **The rate from the expectation bounds.**  If for every slack `eta` the expected hitting
time at level `delta` is at most `log(1/delta)/(Gamma - eta) + A_eta`, the rate is `1/Gamma`. -/
theorem upper_rate_of_bound (Eτ : ℝ → ℝ) (Γ : ℝ) (hΓ : 0 < Γ)
    (hbound : ∀ η, 0 < η → η < Γ → ∃ A : ℝ, ∀ δ, 0 < δ → δ < 1 →
      Eτ δ ≤ Real.log (1 / δ) / (Γ - η) + A) :
    CIGAMF.P13.PaperAEndgame.UpperRate Eτ Γ := by
  intro ε hε
  -- a slack whose rate loss is at most eps/2
  obtain ⟨η, hη, hηΓ, hηrate⟩ : ∃ η, 0 < η ∧ η < Γ ∧ 1 / (Γ - η) ≤ 1 / Γ + ε / 2 := by
    refine ⟨min (Γ / 2) (ε * Γ ^ 2 / (2 * (2 + ε * Γ))), lt_min (by positivity) (by positivity),
      lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
    set η := min (Γ / 2) (ε * Γ ^ 2 / (2 * (2 + ε * Γ))) with hηdef
    have hη1 : η ≤ Γ / 2 := min_le_left _ _
    have hη2 : η ≤ ε * Γ ^ 2 / (2 * (2 + ε * Γ)) := min_le_right _ _
    have hηpos : 0 < η := lt_min (by positivity) (by positivity)
    have hΓη : 0 < Γ - η := by linarith
    rw [div_le_iff₀ hΓη]
    have h3 : η * (2 + ε * Γ) ≤ ε * Γ ^ 2 / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 + ε * Γ))] at hη2
      nlinarith
    rw [show (1 / Γ + ε / 2) * (Γ - η) = 1 - η / Γ + ε * Γ / 2 - ε * η / 2 by
      field_simp; try ring]
    have : η / Γ + ε * η / 2 ≤ ε * Γ / 2 := by
      rw [div_add_div _ _ hΓ.ne' (by norm_num : (2 : ℝ) ≠ 0), div_le_div_iff₀ (by positivity)
        (by norm_num)]
      nlinarith
    linarith
  obtain ⟨A, hA⟩ := hbound η hη hηΓ
  -- a level below which A / log(1/delta) <= eps/2
  set Mx : ℝ := 2 * max A 0 / ε + 1 with hMx
  have hMx0 : 0 < Mx := by positivity
  refine ⟨Real.exp (-Mx), Real.exp_pos _, fun δ hδ hδ0 => ?_⟩
  have hδ1 : δ < 1 := lt_of_lt_of_le hδ0 (min_le_right _ _)
  have hδM : δ < Real.exp (-Mx) := lt_of_lt_of_le hδ0 (min_le_left _ _)
  have hL : Mx < Real.log (1 / δ) := by
    rw [one_div, Real.log_inv]
    have := Real.log_lt_log hδ hδM
    rw [Real.log_exp] at this
    linarith
  have hLpos : 0 < Real.log (1 / δ) := lt_trans hMx0 hL
  have hΓη : 0 < Γ - η := by linarith
  have hAL : A / Real.log (1 / δ) ≤ ε / 2 := by
    rw [div_le_iff₀ hLpos]
    have : 2 * max A 0 / ε < Real.log (1 / δ) := by linarith
    rw [div_lt_iff₀ hε] at this
    nlinarith [le_max_left A 0, le_max_right A 0]
  have h := hA δ hδ hδ1
  show Eτ δ / Real.log (1 / δ) ≤ 1 / Γ + ε
  rw [div_le_iff₀ hLpos]
  have : Real.log (1 / δ) / (Γ - η) + A
      = (1 / (Γ - η) + A / Real.log (1 / δ)) * Real.log (1 / δ) := by
    field_simp
  rw [this] at h
  have := mul_le_mul_of_nonneg_right (add_le_add hηrate hAL) hLpos.le
  nlinarith

#print axioms lastCheck_gt
#print axioms expect_le
#print axioms half_log_le
#print axioms threshold_crossing_time
#print axioms win_of_direct
#print axioms code_thr_le
#print axioms upper_rate_of_bound

end CIGAMF.P13.PaperA7UpperChain
