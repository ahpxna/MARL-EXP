import «LeanPaperA7IdealDirectV1»

/-!
# Paper A7: the direct lower bound for the ideal learner, assembled

`ideal_direct`: for every `eta > 0` there is `T0` such that, for every `t >= T0` and every run in
the good window `GoodWin t` (the confidence event at the true world holds at every time of
`[sqrt t, t]`),

    (Gamma - eta) t <= Zh Tst (history at t),      Gamma = GamT Tst theta.

The error budget, all explicit and all from the learner's own definition: the per-round loss
`eta/4` (`round_good`), the head of the window and the forcing `Gamma (n + K)/t + 2 Gamma/sqrt t`
(`acc_lower`), the multiplicative tracking `2K(K-1)/sqrt t`, the ridge `a / N_min`, and the
raw-mean radius at time `t`, `R sqrt(2U)/sqrt t` -- each below its share for `t` large
(`LeanPaperA7AsymV1`), combined by `budget`.
-/

namespace CIGAMF.P13.PaperA7IdealDirect2

open Finset MeasureTheory
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop
open CIGAMF.P13.PaperA7IdealRun CIGAMF.P13.PaperA7IdealSelect CIGAMF.P13.PaperA7DirectLower
open CIGAMF.P13.PaperA7OracleSelect CIGAMF.P13.PaperA7Asym CIGAMF.P13.PaperA7IdealBounds
open CIGAMF.P13.PaperA7DirectFree CIGAMF.P13.PaperA7FreeAccum CIGAMF.P13.PaperA7GLRMeas
open CIGAMF.P13.PaperA7IdealDirect CIGAMF.P13.PaperA7WarmTrack

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

/-- The final arithmetic of the budget. -/
theorem budget (Γ η c e Acc Rt : ℝ) (hΓ : 0 < Γ) (hη : 0 < η) (hηΓ : η < Γ)
    (hc : 1 - η / (8 * (Γ + 1)) ≤ c) (hc1 : c ≤ 1) (he : 1 - η / (8 * (Γ + 1)) ≤ e)
    (he1 : e ≤ 1) (hAcc : Γ - 3 * η / 8 ≤ Acc) (hR0 : 0 ≤ Rt) (hRt : Rt ≤ η / 16) :
    Γ - η ≤ c * (e * Acc - Rt) := by
  set ε1 := η / (8 * (Γ + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  have hε18 : ε1 ≤ 1 / 8 := by
    rw [hε1, div_le_iff₀ (by positivity)]; nlinarith
  have hA0 : 0 ≤ Γ - 3 * η / 8 := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hce : 1 - 2 * ε1 ≤ c * e := by nlinarith
  have hce0 : 0 ≤ 1 - 2 * ε1 := by linarith
  have h1 : (1 - 2 * ε1) * (Γ - 3 * η / 8) ≤ c * e * Acc := by
    calc (1 - 2 * ε1) * (Γ - 3 * η / 8) ≤ (1 - 2 * ε1) * Acc :=
          mul_le_mul_of_nonneg_left hAcc hce0
      _ ≤ c * e * Acc := mul_le_mul_of_nonneg_right hce (le_trans hA0 hAcc)
  have h2 : 2 * ε1 * Γ ≤ η / 4 := by
    rw [hε1]
    have : η / (8 * (Γ + 1)) * Γ ≤ η / 8 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have h3 : 2 * ε1 * (Γ - 3 * η / 8) ≤ 2 * ε1 * Γ :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : c * Rt ≤ Rt := by nlinarith
  nlinarith

/-- The window-average share of the budget. -/
theorem acc_budget (Γ η K st t n Acc : ℝ) (hΓ : 0 < Γ) (hst : 0 < st) (htt : st * st = t)
    (hn : n ≤ st) (hacc : Γ - η / 4 - Γ * n / t - Γ * (K + 2 * st) / t ≤ Acc)
    (hB1 : Γ * K / t ≤ η / 16) (hB2 : 3 * Γ / st ≤ η / 16) :
    Γ - 3 * η / 8 ≤ Acc := by
  have ht : 0 < t := by rw [← htt]; positivity
  have hA1 : Γ * n / t ≤ Γ / st := by
    rw [div_le_div_iff₀ ht hst]
    calc Γ * n * st ≤ Γ * st * st :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hΓ.le) hst.le
      _ = Γ * t := by rw [mul_assoc, htt]
  have hA2 : Γ * (K + 2 * st) / t = Γ * K / t + 2 * Γ / st := by
    rw [← htt]; field_simp
  have h3 : Γ / st + 2 * Γ / st = 3 * Γ / st := by ring
  linarith

/-- The radius share of the budget. -/
theorem radius_budget (r b C st sst U η : ℝ) (hr1 : r ≤ 1) (hb0 : 0 ≤ b)
    (hC : 0 ≤ C) (hbC : b ≤ C * st) (hsst : 0 < sst) (hss : sst * sst = st)
    (h5 : 2 * Real.sqrt C * Real.sqrt (2 * U) / sst ≤ η / 16) :
    Real.sqrt (2 * (1 + r) * b) * Real.sqrt (2 * U) / st ≤ η / 16 := by
  have hst : 0 < st := by rw [← hss]; positivity
  have h1 : 2 * (1 + r) * b ≤ 4 * (C * st) := by
    have h2 : 2 * (1 + r) ≤ 4 := by linarith
    calc 2 * (1 + r) * b ≤ 4 * b := mul_le_mul_of_nonneg_right h2 hb0
      _ ≤ 4 * (C * st) := mul_le_mul_of_nonneg_left hbC (by norm_num)
  have hsC : Real.sqrt (4 * (C * st)) = 2 * Real.sqrt C * sst := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul hC, ← hss,
      Real.sqrt_mul_self hsst.le,
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)]
    ring
  have hR : Real.sqrt (2 * (1 + r) * b) ≤ 2 * Real.sqrt C * sst := by
    rw [← hsC]; exact Real.sqrt_le_sqrt h1
  calc Real.sqrt (2 * (1 + r) * b) * Real.sqrt (2 * U) / st
      ≤ 2 * Real.sqrt C * sst * Real.sqrt (2 * U) / st := by
        apply div_le_div_of_nonneg_right _ hst.le
        exact mul_le_mul_of_nonneg_right hR (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt C * Real.sqrt (2 * U) / sst := by
        rw [div_eq_div_iff hst.ne' hsst.ne', ← hss]; ring
    _ ≤ η / 16 := h5

theorem ridge_eq (a st K : ℝ) (hst : 0 < st) (hK : 0 < K) :
    a / (st / (2 * K)) = 2 * K * a / st := by
  field_simp

/-- **The ideal learner's direct lower bound.** -/
theorem ideal_direct (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (hkf : ∀ s : ℕ, (s : ℝ) + 1 ≤ P.kf s)
    (hΓ : 0 < GamT P Tst θ) (η : ℝ) (hη : 0 < η) :
    ∃ T0 : ℕ, ∀ t : ℕ, T0 ≤ t → ∀ ω ∈ GoodWin P a θ t,
      (GamT P Tst θ - η) * t ≤ Zh P a Tst (runH P θ t ω) := by
  set Γ := GamT P Tst θ with hΓdef
  -- the statistic is nonnegative
  have hZ0 : ∀ t ω, 0 ≤ Zh P a Tst (runH P θ t ω) := by
    intro t ω
    unfold Zh glr
    obtain ⟨ν, hν⟩ := P.Alt_ne Tst
    exact le_csInf ((P.Alt_ne Tst).image _) (by
      rintro _ ⟨l, -, rfl⟩; exact qAbs_nonneg a ha P.σ _ l)
  rcases le_or_gt Γ η with hηΓ | hηΓ
  · refine ⟨0, fun t _ ω _ => le_trans ?_ (hZ0 t ω)⟩
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg t)
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 1 ≤ K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  obtain ⟨ν0, hν0⟩ := P.Alt_ne Tst
  set U := Ubd P Tst θ ν0 with hUdef
  have hΓU : Γ ≤ U := GamT_le P Tst θ ν0 hν0 θ fun e => by simp
  have hU0 : 0 < U := lt_of_lt_of_le hΓ hΓU
  set C := C1 (Fintype.card E) a
  have hC : 0 ≤ C := C1_nonneg _ _ (Nat.cast_nonneg _)
  set ε1 := η / (8 * (Γ + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  -- thresholds
  obtain ⟨S, hS1, hS⟩ := round_good P a ha Tst θ hwrong hkf hΓ η hη
  obtain ⟨Sc, hScK, hSc⟩ := count_floor P a ha θ
  obtain ⟨T1, hT1⟩ := eventually_inv (Γ * K) (η / 16) (by positivity) (by positivity)
  obtain ⟨T2, hT2⟩ := eventually_inv_sqrt (3 * Γ) (η / 16) (by positivity) (by positivity)
  obtain ⟨T3, hT3⟩ := eventually_inv_sqrt (2 * K * a) ε1 (by positivity) hε1pos
  obtain ⟨T4, hT4⟩ := eventually_inv_sqrt (2 * K * (K - 1)) ε1
    (by have : 0 ≤ K - 1 := by linarith
        positivity) hε1pos
  obtain ⟨T5, hT5⟩ := eventually_inv_sqrt_sqrt (2 * Real.sqrt C * Real.sqrt (2 * U)) (η / 16)
    (by positivity) (by positivity)
  refine ⟨max (max (max (S * S) Sc) (max T1 T2)) (max (max T3 T4) T5), fun t ht ω hω => ?_⟩
  have htS : S * S ≤ t := by omega
  have htSc : Sc ≤ t := by omega
  have htK : Fintype.card E ≤ t := le_trans hScK htSc
  have hn : S ≤ Nat.sqrt t := Nat.le_sqrt.mpr htS
  have ht1' : 1 ≤ t := le_trans Fintype.card_pos htK
  have htR1 : (1 : ℝ) ≤ t := by exact_mod_cast ht1'
  have htR : (0 : ℝ) < t := by linarith
  have ht0 : 0 < t := by omega
  set n := Nat.sqrt t with hndef
  have hnt : n ≤ t := Nat.sqrt_le_self t
  -- the rounds of the window are good
  have hgood : ∀ s, n ≤ s → s < t → Γ - η / 4
      ≤ Jval (sc P.σ '' P.Alt Tst) (design P s (hMu (runH P θ s ω))) (sc P.σ θ) :=
    fun s hns hst => (hS s (le_trans hn hns) ω (hω s hns hst.le)).2
  -- counts, tracking
  obtain ⟨hmx, -⟩ := hSc t htSc ω (Classical.arbitrary E)
  have hNall : ∀ e, Real.sqrt t / (2 * K) ≤ Nc (idealLearner P) θ P.σ t ω e :=
    fun e => (hSc t htSc ω e).2
  set Nmin := Real.sqrt t / (2 * K) with hNmin
  have haN : a ≤ Nmin := le_trans (le_max_left _ _) hmx
  have hNmin0 : 0 < Nmin := lt_of_lt_of_le ha haN
  set w : ℕ → E → ℝ := fun s => design P s (hMu (runH P θ s ω)) with hw
  have hwalloc : ∀ s, IsAlloc (w s) := fun s => design_alloc P s _
  have hρ : ∀ s, 0 ≤ rho (E := E) s ∧ rho (E := E) s ≤ 1 := by
    intro s
    have h := target_alloc P s (runH P θ s ω)
    unfold rho
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · refine ⟨by positivity, ?_⟩
      rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
      exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
  have hsqt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htR
  have htt : Real.sqrt (t : ℝ) * Real.sqrt t = t := Real.mul_self_sqrt htR.le
  have htrack0 := run_track P θ ω (t - Fintype.card E)
  rw [show Fintype.card E + (t - Fintype.card E) = t by omega] at htrack0
  have hfloor : ∀ e, 1 / (K * Real.sqrt t) ≤ PaperA7Accumulation.avgTarget w (rho (E := E)) unif t e :=
    fun e => avgTarget_floor w (fun s e => (hwalloc s).1 e) rho (fun s => (hρ s).2)
      (fun s => by
        unfold rho
        split_ifs
        · rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
          exact Real.one_le_sqrt.mpr (by linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)])
        · exact le_rfl) unif (fun e => rfl) t ht0 e
  have hmult := mult_of_additive (fun e => Nc (idealLearner P) θ P.σ t ω e)
    (PaperA7Accumulation.avgTarget w (rho (E := E)) unif t) (t : ℝ) (2 * ((Fintype.card E : ℝ) - 1))
    (1 / (K * Real.sqrt t)) htR (by positivity) (by linarith) hfloor htrack0
  set ε := 2 * ((Fintype.card E : ℝ) - 1) / ((t : ℝ) * (1 / (K * Real.sqrt t))) with hεdef
  have hden : (t : ℝ) * (1 / (K * Real.sqrt t)) = Real.sqrt t / K := by
    calc (t : ℝ) * (1 / (K * Real.sqrt t))
        = (Real.sqrt t * Real.sqrt t) * (1 / (K * Real.sqrt t)) := by rw [htt]
      _ = Real.sqrt t / K := by field_simp
  have hεeq : ε = 2 * K * (K - 1) / Real.sqrt t := by
    rw [hεdef, hden]
    field_simp
    ring
  have hK1 : 0 ≤ K - 1 := by linarith
  have hε0 : 0 ≤ ε := by
    rw [hεeq]
    exact div_nonneg (mul_nonneg (by positivity) hK1) (Real.sqrt_nonneg _)
  have hεle : ε ≤ ε1 := by rw [hεeq]; exact hT4 t (by omega)
  have hε1le : ε1 ≤ 1 := by
    rw [hε1, div_le_one (by positivity)]; nlinarith
  -- the allocation of the counts
  have hNsum : ∑ e, Nc (idealLearner P) θ P.σ t ω e = t := by
    have := (warmRunOf P θ ω).N_sum (t - Fintype.card E)
    have h2 : ∑ e, (warmRunOf P θ ω).N (t - Fintype.card E) e
        = ∑ e, Nc (idealLearner P) θ P.σ t ω e := by
      refine sum_congr rfl fun e _ => ?_
      show Nc (idealLearner P) θ P.σ (Fintype.card E + (t - Fintype.card E)) ω e = _
      rw [show Fintype.card E + (t - Fintype.card E) = t by omega]
    rw [h2] at this
    rw [this]; push_cast [Nat.cast_sub htK]; ring
  have hNalloc : IsAlloc (fun e => Nc (idealLearner P) θ P.σ t ω e / t) := by
    refine ⟨fun e => div_nonneg (Nat.cast_nonneg _) htR.le, ?_⟩
    rw [← sum_div, hNsum, div_self htR.ne']
  have hU : Jval (sc P.σ '' P.Alt Tst) (fun e => Nc (idealLearner P) θ P.σ t ω e / t) (sc P.σ θ)
      ≤ U := le_trans ((GamT_isLUB P Tst θ).1 ⟨_, hNalloc, rfl⟩) hΓU
  -- the confidence at time t and the solver contract (exact infimum)
  have hconf := hω t hnt le_rfl
  set b := bthr a ((t : ℝ) ^ 4)⁻¹ (Nc (idealLearner P) θ P.σ t ω) with hb
  have hb0 : 0 ≤ b := bthr_nonneg a ha _ (by positivity)
    (inv_le_one_of_one_le₀ (one_le_pow₀ htR1)) _ fun e => Nat.cast_nonneg _
  have hsolver : sInf ((fun l => PaperA7Stream.Qstat a P.σ (Nc (idealLearner P) θ P.σ t ω)
      (muHat (idealLearner P) θ P.σ t ω) l) '' P.Alt Tst) - t * 0
      ≤ Zh P a Tst (runH P θ t ω) := by
    rw [mul_zero, sub_zero]
    show _ ≤ glr a P.σ (P.Alt Tst) (hN (runH P θ t ω), hMu (runH P θ t ω))
    rw [hN_runH, hMu_runH, (glr_run_measurable (idealLearner P) θ P.σ a ha
      (fun e => (P.σ_pos e).ne') (P.Alt Tst) (P.Alt_ne Tst) t).2 ω]
  have hD := direct_lower_free a ha (P.Alt Tst) (P.Alt_ne Tst) P.σ P.σ_pos θ
    (muHat (idealLearner P) θ P.σ t ω) Γ n t hnt ht0 w hwalloc rho hρ unif unif_alloc
    (fun _ => η / 4) hgood (fun e => Nc (idealLearner P) θ P.σ t ω e) ε hε0
    (le_trans hεle hε1le) hmult Nmin haN hNall U hU b hb0 hconf (Zh P a Tst (runH P θ t ω)) 0
    hsolver
  -- the window average
  have hacc := acc_lower Γ (η / 4) (by positivity) (by linarith) hΓ.le n t hnt ht0 rho hρ
    (K + 2 * Real.sqrt t) (sum_rho_le t)
  have hn_le : (n : ℝ) ≤ Real.sqrt t := Real.nat_sqrt_le_real_sqrt
  have hAcc : Γ - 3 * η / 8 ≤ (1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - rho (E := E) s) * (Γ - η / 4) :=
    acc_budget Γ η K (Real.sqrt t) t n _ hΓ hsqt htt hn_le hacc (hT1 t (by omega)) (hT2 t (by omega))
  -- the ridge and tracking factors
  have hcr : 1 - ε1 ≤ 1 - a / Nmin := by
    have h3 : 2 * K * a / Real.sqrt t ≤ ε1 := hT3 t (by omega)
    have : a / Nmin = 2 * K * a / Real.sqrt t := by
      rw [hNmin]; exact ridge_eq a _ K hsqt (by linarith)
    linarith
  have hcr1 : 1 - a / Nmin ≤ 1 := by have := div_nonneg ha.le hNmin0.le; linarith
  have he : 1 - ε1 ≤ 1 - ε := by linarith
  -- the radius term at t
  have haN1 : a / Nmin ≤ 1 := (div_le_one hNmin0).mpr haN
  have hbC : b ≤ C * Real.sqrt t :=
    le_trans (bthr_le a ha t ht1' _ (fun e => Nat.cast_nonneg _) (run_count_le P θ ω t))
      (mul_le_mul_of_nonneg_left (sqrt_sqrt_le_sqrt t htR1) hC)
  have hss : Real.sqrt (Real.sqrt t) * Real.sqrt (Real.sqrt t) = Real.sqrt t :=
    Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hssp : 0 < Real.sqrt (Real.sqrt (t : ℝ)) := Real.sqrt_pos.mpr hsqt
  have hRt : Real.sqrt (2 * (1 + a / Nmin) * b) * Real.sqrt (2 * U) / Real.sqrt t ≤ η / 16 :=
    radius_budget (a / Nmin) b C (Real.sqrt t) (Real.sqrt (Real.sqrt t)) U η
      haN1 hb0 hC hbC hssp hss (hT5 t (by omega))
  have hfin := budget Γ η (1 - a / Nmin) (1 - ε)
    ((1 / (t : ℝ)) * ∑ s ∈ Ico n t, (1 - rho (E := E) s) * (Γ - η / 4))
    (Real.sqrt (2 * (1 + a / Nmin) * b) * Real.sqrt (2 * U) / Real.sqrt t)
    hΓ hη hηΓ hcr hcr1 he (by linarith) hAcc (by positivity) hRt
  have hfin2 : Γ - η ≤ Zh P a Tst (runH P θ t ω) / t := by
    refine le_trans hfin ?_
    have := hD
    rw [sub_zero] at this
    exact this
  rw [le_div_iff₀ htR] at hfin2
  exact hfin2

#print axioms budget
#print axioms acc_budget
#print axioms radius_budget
#print axioms ideal_direct

end CIGAMF.P13.PaperA7IdealDirect2
