import «LeanPaperA7IdealBoundsV1»
import «LeanPaperA7DirectFreeV1»

/-!
# Paper A7: the ideal learner's statistic grows at the rate of the game, on the good window

`ideal_direct`: in a world `theta` whose correct answer is `Tst` (it lies in every other
answer's alternative), for every `eta > 0` there is a time `T0` after which, on the event that
the confidence statistic at the true world stays below its level `s^(-4)` threshold at every
time of the window `[sqrt t, t]`, the stopping statistic of `Tst` satisfies

    (Gamma - eta) t  <=  Zh Tst (history at t),     Gamma = GamT Tst theta.

Everything is derived from the learner's own definition:
* `count_floor` -- every count is eventually at least `max(a, 1)` and `sqrt s / (2K)`
  (`run_count_ge`);
* `round_good` -- at every round `s >= S` of the good event, the raw mean is within the radius
  `rbar <= 1` (`radius_run`, `bthr_le`), the oracle selects `Tst` and its design has true
  information `>= Gamma - eta/4` (`round_info`, `net_factor`);
* `acc_lower` -- the window average of `(1 - rho_s)(Gamma - eta/4)` is at least
  `Gamma - eta/4 - Gamma (n + K)/t - 2 Gamma / sqrt t` (`sum_rho_le`);
* the multiplicative tracking factor `2K(K-1)/sqrt t` (`run_track`, `avgTarget_floor`,
  `mult_of_additive`), the ridge factor `a / N_min`, and the raw-mean radius at time `t`, all
  vanishing -- assembled by `direct_lower_free`.
-/

namespace CIGAMF.P13.PaperA7IdealDirect

open Finset MeasureTheory
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop
open CIGAMF.P13.PaperA7IdealRun CIGAMF.P13.PaperA7IdealSelect CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Asym CIGAMF.P13.PaperA7IdealBounds
open CIGAMF.P13.PaperA7DirectFree CIGAMF.P13.PaperA7FreeAccum CIGAMF.P13.PaperA7GLRMeas

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

/-- The confidence event at time `s`, at the true world, at the code's level `s^(-4)`. -/
def GoodAt (a : ℝ) (θ : E → ℝ) (s : ℕ) (ω : ℕ → ℝ) : Prop :=
  PaperA7Stream.Qstat a P.σ (Nc (idealLearner P) θ P.σ s ω) (muHat (idealLearner P) θ P.σ s ω) θ
    ≤ bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (idealLearner P) θ P.σ s ω)

/-- The good window ending at `t`. -/
def GoodWin (a : ℝ) (θ : E → ℝ) (t : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∀ s, Nat.sqrt t ≤ s → s ≤ t → GoodAt P a θ s ω}

/-! ## 1. Counts -/

/-- **Every count is eventually large.** -/
theorem count_floor (a : ℝ) (ha : 0 < a) (θ : E → ℝ) :
    ∃ S : ℕ, Fintype.card E ≤ S ∧ ∀ s, S ≤ s → ∀ ω e,
      max a 1 ≤ Real.sqrt s / (2 * Fintype.card E) ∧
      Real.sqrt s / (2 * Fintype.card E) ≤ Nc (idealLearner P) θ P.σ s ω e := by
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  obtain ⟨S1, hS1⟩ := eventually_inv_sqrt (2 * K * (K - 1 + max a 1)) 1 (by
    have : 0 ≤ K - 1 := by linarith
    have : 0 < max a 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity) one_pos
  refine ⟨max S1 (Fintype.card E), le_max_right _ _, fun s hs ω e => ?_⟩
  have hsK : Fintype.card E ≤ s := le_trans (le_max_right _ _) hs
  have h1 := hS1 s (le_trans (le_max_left _ _) hs)
  have hs1 : (1 : ℝ) ≤ s := by
    have : 1 ≤ s := le_trans Fintype.card_pos hsK
    exact_mod_cast this
  have hsq : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_one hsq] at h1
  have hmx : 0 < max a 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith
  · have hc := run_count_ge P θ ω (s - Fintype.card E) e
    rw [show Fintype.card E + (s - Fintype.card E) = s by omega] at hc
    have hA : 2 * K * (K - 1) ≤ Real.sqrt s := by
      have : 2 * K * (K - 1) ≤ 2 * K * (K - 1 + max a 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    have hB : K - 1 ≤ Real.sqrt s / (2 * K) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have hC : Real.sqrt s / K - Real.sqrt s / (2 * K) = Real.sqrt s / (2 * K) := by
      field_simp; ring
    have : Real.sqrt s / (2 * K) ≤ Real.sqrt s / K - (K - 1) := by linarith
    linarith

/-! ## 2. One good round -/

/-- **The radius on the good event is eventually below any target.** -/
theorem radius_eventually (a : ℝ) (ha : 0 < a) (θ : E → ℝ) (rb : ℝ) (hrb : 0 < rb) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ s, S ≤ s → ∀ ω, GoodAt P a θ s ω →
      ∀ e, |muHat (idealLearner P) θ P.σ s ω e - θ e| ≤ rb := by
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  have hσM : 0 < smax P := lt_of_lt_of_le (P.σ_pos (Classical.arbitrary E)) (le_smax P _)
  set C := C1 (Fintype.card E) a
  have hC : 0 ≤ C := C1_nonneg _ _ (Nat.cast_nonneg _)
  obtain ⟨Sc, hScK, hSc⟩ := count_floor P a ha θ
  obtain ⟨Sr, hSr⟩ := eventually_inv_sqrt_sqrt (2 * K * C) ((rb / (2 * smax P)) ^ 2)
    (by positivity) (by positivity)
  refine ⟨max (max Sc Sr) 1, le_max_right _ _, fun s hs ω hgood e => ?_⟩
  have hsc : Sc ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hsr : Sr ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hs1' : 1 ≤ s := le_trans (le_max_right _ _) hs
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs1'
  have hs0 : (0 : ℝ) < s := by linarith
  have hmx := (hSc s hsc ω e).1
  have hNall : ∀ e', Real.sqrt s / (2 * K) ≤ Nc (idealLearner P) θ P.σ s ω e' :=
    fun e' => (hSc s hsc ω e').2
  set Nmin := Real.sqrt s / (2 * K) with hNmin
  have haN : a ≤ Nmin := le_trans (le_max_left _ _) hmx
  set b := bthr a ((s : ℝ) ^ 4)⁻¹ (Nc (idealLearner P) θ P.σ s ω) with hb
  have hb0 : 0 ≤ b := bthr_nonneg a ha _ (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ hs1)) _ fun e => Nat.cast_nonneg _
  have hbC : b ≤ C * Real.sqrt (Real.sqrt s) :=
    bthr_le a ha s hs1' _ (fun e => Nat.cast_nonneg _) (run_count_le P θ ω s)
  have hrad := radius_run P a ha θ s ω b hb0 hgood Nmin haN hNall e
  have hss : Real.sqrt (Real.sqrt s) * Real.sqrt (Real.sqrt s) = Real.sqrt s :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hssp : 0 < Real.sqrt (Real.sqrt s) := by
    apply Real.sqrt_pos.mpr; exact Real.sqrt_pos.mpr hs0
  have hsp : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hs0
  have hbN : b / Nmin ≤ 2 * K * C / Real.sqrt (Real.sqrt s) := by
    rw [hNmin, div_div_eq_mul_div, div_le_div_iff₀ hsp hssp]
    have h1 : b * (2 * K) * Real.sqrt (Real.sqrt s)
        ≤ C * Real.sqrt (Real.sqrt s) * (2 * K) * Real.sqrt (Real.sqrt s) := by
      have := mul_le_mul_of_nonneg_right hbC (by positivity : (0 : ℝ) ≤ 2 * K)
      exact mul_le_mul_of_nonneg_right this hssp.le
    have h2 : C * Real.sqrt (Real.sqrt s) * (2 * K) * Real.sqrt (Real.sqrt s)
        = 2 * K * C * (Real.sqrt (Real.sqrt s) * Real.sqrt (Real.sqrt s)) := by ring
    rw [h2, hss] at h1
    exact h1
  have h2 : Real.sqrt (b / Nmin) ≤ rb / (2 * smax P) := by
    rw [show rb / (2 * smax P) = Real.sqrt ((rb / (2 * smax P)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (le_trans hbN (hSr s hsr))
  have h3 : 2 * smax P * Real.sqrt (b / Nmin) ≤ rb := by
    calc 2 * smax P * Real.sqrt (b / Nmin) ≤ 2 * smax P * (rb / (2 * smax P)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = rb := by field_simp
  exact le_trans hrad h3

/-- **A good round after `S`**: the design is informative and the mean is close. -/
theorem round_good (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (hkf : ∀ s : ℕ, (s : ℝ) + 1 ≤ P.kf s)
    (hΓ : 0 < GamT P Tst θ) (η : ℝ) (hη : 0 < η) :
    ∃ S : ℕ, 1 ≤ S ∧ ∀ s, S ≤ s → ∀ ω, GoodAt P a θ s ω →
      (∀ e, |muHat (idealLearner P) θ P.σ s ω e - θ e| ≤ 1) ∧
      GamT P Tst θ - η / 4
        ≤ Jval (sc P.σ '' P.Alt Tst) (design P s (hMu (runH P θ s ω))) (sc P.σ θ) := by
  set Γ := GamT P Tst θ with hΓdef
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  have hσm := smin_pos P
  obtain ⟨ν0, hν0⟩ := P.Alt_ne Tst
  set U := Ubd P Tst θ ν0 with hUdef
  have hΓU : Γ ≤ U := GamT_le P Tst θ ν0 hν0 θ fun e => by simp
  have hU0 : 0 < U := lt_of_lt_of_le hΓ hΓU
  -- the radius target, in unit-variance units
  set q : ℝ := min (min (1 / smin P) (η / (16 * (Real.sqrt (2 * U) + 1))))
    (min (Γ / (2 * (Real.sqrt (2 * Γ) + 1))) (Real.sqrt Γ / 2)) with hq
  have hsΓ := Real.sqrt_pos.mpr hΓ
  have hq0 : 0 < q := by
    refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  have hq1 : q ≤ 1 / smin P := le_trans (min_le_left _ _) (min_le_left _ _)
  have hq2 : q ≤ η / (16 * (Real.sqrt (2 * U) + 1)) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hq3 : q ≤ Γ / (2 * (Real.sqrt (2 * Γ) + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hq4 : q ≤ Real.sqrt Γ / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  set rb := q * smin P with hrb
  have hrb0 : 0 < rb := mul_pos hq0 hσm
  have hrb1 : rb ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hq1 hσm.le
    rwa [one_div_mul_cancel hσm.ne'] at this
  have hrbq : rb / smin P = q := mul_div_cancel_right₀ q hσm.ne'
  -- thresholds
  obtain ⟨Sr, hSr1, hSr⟩ := radius_eventually P a ha θ rb hrb0
  obtain ⟨Sn, hSn⟩ := eventually_inv_sqrt (K + 1) (min (1 / 2) (η / (8 * (U + 1)))) (by linarith)
    (lt_min (by norm_num) (by positivity))
  refine ⟨max (max Sr Sn) (Fintype.card E ^ 2 + 1), le_trans hSr1
    (le_trans (le_max_left _ _) (le_max_left _ _)), fun s hs ω hgood => ?_⟩
  have hsr : Sr ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hsn : Sn ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hsK2 : Fintype.card E ^ 2 + 1 ≤ s := le_trans (le_max_right _ _) hs
  have hs0 : (0 : ℝ) < s := by
    have : 0 < s := by omega
    exact_mod_cast this
  have hclose := hSr s hsr ω hgood
  refine ⟨fun e => le_trans (hclose e) hrb1, ?_⟩
  -- the grid factor at s
  have hkfs : K ^ 2 ≤ P.kf s := by
    have h1 := hkf s
    have h2 : ((Fintype.card E ^ 2 + 1 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast hsK2
    push_cast at h2
    rw [hKdef]; linarith
  obtain ⟨hβ0, hβ1, hkβ, hcge⟩ := net_factor K (P.kf s) hK hkfs
  set β := K / Real.sqrt (P.kf s) with hβ
  set c := (1 - K / (P.kf s * β)) * (1 - β) with hc
  have hkn : (K + 1) / Real.sqrt (P.kf s) ≤ min (1 / 2) (η / (8 * (U + 1))) := by
    have h1 := hSn s hsn
    have hsqk : Real.sqrt s ≤ Real.sqrt (P.kf s) := Real.sqrt_le_sqrt (by linarith [hkf s])
    exact le_trans (div_le_div_of_nonneg_left (by linarith) (Real.sqrt_pos.mpr hs0) hsqk) h1
  have hc12 : 1 / 2 ≤ c := by
    have := le_trans hkn (min_le_left _ _); linarith
  have hcU : (1 - c) * U ≤ η / 8 := by
    have h1 := le_trans hkn (min_le_right _ _)
    have h2 : 1 - c ≤ η / (8 * (U + 1)) := by linarith
    have h3 : (1 - c) * U ≤ η / (8 * (U + 1)) * U := mul_le_mul_of_nonneg_right h2 hU0.le
    have h4 : η / (8 * (U + 1)) * U ≤ η / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have : η * U * 8 ≤ η * 8 * (U + 1) := by
        have := mul_le_mul_of_nonneg_left (show U ≤ U + 1 by linarith) (by positivity : (0:ℝ) ≤ η * 8)
        linarith
      linarith
    linarith
  -- selection holds
  have h1 : q * Real.sqrt (2 * Γ) ≤ Γ / 2 := by
    have hA : q * Real.sqrt (2 * Γ) ≤ q * (Real.sqrt (2 * Γ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0.le
    have hB : q * (Real.sqrt (2 * Γ) + 1)
        ≤ Γ / (2 * (Real.sqrt (2 * Γ) + 1)) * (Real.sqrt (2 * Γ) + 1) :=
      mul_le_mul_of_nonneg_right hq3 (by positivity)
    have hC : Γ / (2 * (Real.sqrt (2 * Γ) + 1)) * (Real.sqrt (2 * Γ) + 1) = Γ / 2 := by
      field_simp
    linarith
  have h2 : q ^ 2 ≤ Γ / 4 := by
    calc q ^ 2 ≤ (Real.sqrt Γ / 2) ^ 2 := pow_le_pow_left₀ hq0.le hq4 2
      _ = Γ / 4 := by rw [div_pow, Real.sq_sqrt hΓ.le]; ring
  have hsel : (rb / smin P) ^ 2 / 2 < c * (Γ - (rb / smin P) * Real.sqrt (2 * Γ)) := by
    rw [hrbq]
    have hD : Γ / 2 ≤ Γ - q * Real.sqrt (2 * Γ) := by linarith
    have hE : 1 / 2 * (Γ / 2) ≤ c * (Γ - q * Real.sqrt (2 * Γ)) :=
      mul_le_mul hc12 hD (by positivity) (by linarith)
    linarith
  -- the round's information
  have hmu : hMu (runH P θ s ω) = muHat (idealLearner P) θ P.σ s ω := hMu_runH P θ s ω
  have hU2 : GamT P Tst (muHat (idealLearner P) θ P.σ s ω) ≤ U :=
    GamT_le P Tst θ ν0 hν0 _ fun e => le_trans (hclose e) hrb1
  have hinfo := round_info P Tst θ hwrong s (muHat (idealLearner P) θ P.σ s ω) (smin P) hσm
    (smin_le P) rb hrb0.le hclose U hΓU hU2 β hβ0 hβ1 hkβ (by linarith) hsel
  rw [hmu]
  have hr2 : 2 * (rb / smin P) * Real.sqrt (2 * U) ≤ η / 8 := by
    rw [hrbq]
    have hA : 2 * q * Real.sqrt (2 * U) ≤ 2 * q * (Real.sqrt (2 * U) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hB : 2 * q * (Real.sqrt (2 * U) + 1)
        ≤ 2 * (η / (16 * (Real.sqrt (2 * U) + 1))) * (Real.sqrt (2 * U) + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 (by norm_num)) (by positivity)
    have hC : 2 * (η / (16 * (Real.sqrt (2 * U) + 1))) * (Real.sqrt (2 * U) + 1) = η / 8 := by
      field_simp; ring
    linarith
  linarith

/-! ## 3. The window average -/

theorem acc_lower (Γ η' : ℝ) (hη' : 0 ≤ η') (hΓη : η' ≤ Γ) (hΓ : 0 ≤ Γ) (n t : ℕ) (hnt : n ≤ t) (ht : 0 < t)
    (ρ : ℕ → ℝ) (hρ : ∀ s, 0 ≤ ρ s ∧ ρ s ≤ 1) (B : ℝ)
    (hsum : ∑ s ∈ range t, ρ s ≤ B) :
    Γ - η' - Γ * n / t - Γ * B / t
      ≤ (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η') := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hsplit : ∑ s ∈ Ico n t, (1 - ρ s) * (Γ - η')
      = ∑ s ∈ Ico n t, (Γ - η') - ∑ s ∈ Ico n t, ρ s * (Γ - η') := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun s _ => by ring
  have hcard : ∑ s ∈ Ico n t, (Γ - η') = ((t : ℝ) - n) * (Γ - η') := by
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hnt]
  have hρsum : ∑ s ∈ Ico n t, ρ s * (Γ - η') ≤ Γ * B := by
    calc ∑ s ∈ Ico n t, ρ s * (Γ - η') ≤ ∑ s ∈ Ico n t, ρ s * Γ :=
          sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (by linarith) (hρ s).1
      _ ≤ ∑ s ∈ range t, ρ s * Γ := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro s hs; rw [mem_Ico] at hs; exact mem_range.mpr hs.2
          · intro s _ _; exact mul_nonneg (hρ s).1 hΓ
      _ = Γ * ∑ s ∈ range t, ρ s := by rw [← sum_mul, mul_comm]
      _ ≤ Γ * B := mul_le_mul_of_nonneg_left hsum hΓ
  rw [hsplit, hcard]
  have hnΓ : (n : ℝ) * (Γ - η') ≤ n * Γ := mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg n)
  rw [mul_sub, one_div_mul_eq_div, one_div_mul_eq_div]
  have e1 : ((t : ℝ) - n) * (Γ - η') / t = Γ - η' - n * (Γ - η') / t := by
    field_simp
  rw [e1]
  have e2 : Γ * (n : ℝ) / t ≥ n * (Γ - η') / t := by
    rw [ge_iff_le, div_le_div_iff_of_pos_right htR]; linarith
  have e3 : (∑ s ∈ Ico n t, ρ s * (Γ - η')) / t ≤ Γ * B / t :=
    div_le_div_of_nonneg_right hρsum htR.le
  linarith

#print axioms count_floor
#print axioms radius_eventually
#print axioms round_good
#print axioms acc_lower

end CIGAMF.P13.PaperA7IdealDirect
