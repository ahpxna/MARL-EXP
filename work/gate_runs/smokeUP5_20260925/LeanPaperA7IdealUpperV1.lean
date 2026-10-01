import «LeanPaperA7IdealDirect2V1»
import «LeanPaperA7UpperChainV1»

/-!
# Paper A7: the upper rate and the correctness of the ideal learner

* `ideal_expect_bound` -- for every slack `eta in (0, Gamma)` there is `A` such that, for every
  `delta in (0,1)`, the expected stopping time is finite and

      E tau_delta <= log(1/delta) / (Gamma - eta) + A,        Gamma = GamT Tst theta;

* `ideal_upper_rate` -- hence `UpperRate (E tau) Gamma`;
* `ideal_correct` -- the probability of stopping with a wrong answer is at most
  `(|Ans| - 1) delta`.

The ingredients are all theorems about the learner that is actually defined
(`idealLearner`, `tauI`): the direct bound on the good window (`ideal_direct`), the code's
threshold `log(1/delta) + (K/2) log(1 + t/a)` (`code_thr_le`, with every count at most `t`), the
crossing time (`win_of_direct`), and the window failure probability
`sqrt(t)^(-4) <= 16/t^2` (`good_window_real` at the truth, via `qstat_truth_eq`), summed by
`expect_le`.  No parameter of the world enters the learner: `theta` appears only as the law of
the stream.
-/

namespace CIGAMF.P13.PaperA7IdealUpper

open Finset MeasureTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop
open CIGAMF.P13.PaperA7IdealRun CIGAMF.P13.PaperA7IdealSelect CIGAMF.P13.PaperA7IdealBounds
open CIGAMF.P13.PaperA7IdealDirect CIGAMF.P13.PaperA7IdealDirect2 CIGAMF.P13.PaperA7UpperChain
open CIGAMF.P13.PaperAStopping

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans)

theorem hitTime_le_of {p : ℕ → Prop} [DecidablePred p] (t : ℕ) (ht : p t) :
    hitTime p ≤ (t : ℕ∞) := by
  rw [hitTime_eq_find ⟨t, ht⟩]
  exact_mod_cast Nat.find_min' _ ht

/-- `sqrt(t)^(-4) <= 16 / t^2`. -/
theorem inv_sqrt_pow4_le (t : ℕ) (ht : 1 ≤ t) :
    ((Nat.sqrt t : ℝ) ^ 4)⁻¹ ≤ 16 * (1 / (t : ℝ) ^ 2) := by
  have hn : 0 < Nat.sqrt t := Nat.sqrt_pos.mpr ht
  have hnR : (1 : ℝ) ≤ Nat.sqrt t := by exact_mod_cast hn
  have hlt : (t : ℝ) < ((Nat.sqrt t : ℝ) + 1) * ((Nat.sqrt t : ℝ) + 1) := by
    have := Nat.lt_succ_sqrt t
    rw [Nat.succ_eq_add_one] at this
    exact_mod_cast this
  have h4 : (t : ℝ) ≤ 4 * (Nat.sqrt t : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Nat.sqrt t + 1)
      (by linarith : (0 : ℝ) ≤ Nat.sqrt t - 1)]
  have h16 : (t : ℝ) ^ 2 ≤ 16 * (Nat.sqrt t : ℝ) ^ 4 :=
    calc (t : ℝ) ^ 2 ≤ (4 * (Nat.sqrt t : ℝ) ^ 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg t) h4 2
      _ = 16 * (Nat.sqrt t : ℝ) ^ 4 := by ring
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  rw [← one_div, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **The window failure probability** at the truth. -/
theorem goodWin_compl_le (a : ℝ) (ha : 0 < a) (θ : E → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    streamMeasure (GoodWin P a θ t)ᶜ ≤ ENNReal.ofReal (16 * (1 / (t : ℝ) ^ 2)) := by
  have hn : 1 ≤ Nat.sqrt t := Nat.sqrt_pos.mpr ht
  have hsub : (GoodWin P a θ t)ᶜ ⊆ {ω | ∃ j, Nat.sqrt t ≤ j ∧ j ≤ t ∧
      bthr a ((j : ℝ) ^ 4)⁻¹ (Nc (idealLearner P) θ P.σ j ω)
        < PaperA7Confidence.Qstat a (Sc (idealLearner P) θ P.σ j ω)
            (Nc (idealLearner P) θ P.σ j ω)} := by
    intro ω hω
    simp only [GoodWin, GoodAt, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hω
    obtain ⟨j, hnj, hjt, hj⟩ := hω
    refine ⟨j, hnj, hjt, ?_⟩
    rw [← qstat_truth_eq (idealLearner P) θ P.σ a P.σ_pos j ω]
    exact hj
  have hreal := good_window_real (idealLearner P) θ P.σ a ha (Nat.sqrt t) t hn
  refine le_trans (measure_mono hsub) ?_
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact le_trans (ENNReal.ofReal_le_ofReal hreal) (ENNReal.ofReal_le_ofReal (inv_sqrt_pow4_le t ht))

theorem thrI_nonneg (K a κ Gm : ℝ) (hK : 0 < K) (ha : 0 < a) (hκ : 0 < κ) (hGm : 0 < Gm) :
    0 ≤ thrI K a κ Gm := by
  unfold thrI
  have hx : 0 < 2 * a * κ * Gm / K := by positivity
  have := Real.log_le_sub_one_of_pos hx
  exact mul_nonneg (by positivity) (by linarith)

/-- **The expected stopping time of the ideal learner.** -/
theorem ideal_expect_bound (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (hkf : ∀ s : ℕ, (s : ℝ) + 1 ≤ P.kf s)
    (hΓ : 0 < GamT P Tst θ) (η : ℝ) (hη : 0 < η) (hηΓ : η < GamT P Tst θ) :
    ∃ A : ℝ, ∀ δ, 0 < δ → δ < 1 →
      (∫⁻ ω, (tauI P a δ θ ω).toENNReal ∂streamMeasure) ≠ ⊤ ∧
      (∫⁻ ω, (tauI P a δ θ ω).toENNReal ∂streamMeasure).toReal
        ≤ Real.log (1 / δ) / (GamT P Tst θ - η) + A := by
  set Γ := GamT P Tst θ with hΓdef
  set K : ℝ := (Fintype.card E : ℝ) with hKdef
  have hK : 0 < K := by rw [hKdef]; exact_mod_cast Fintype.card_pos
  set κ := η / (2 * Γ) with hκ
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ < 1 := by rw [hκ, div_lt_one (by positivity)]; linarith
  set Gm := Γ - η / 2 with hGm
  have hGm0 : 0 < Gm := by linarith
  have hden : Γ - η ≤ (1 - κ) * Gm := by
    rw [hκ, hGm]
    have h : (1 - η / (2 * Γ)) * (Γ - η / 2) = Γ - η + η ^ 2 / (4 * Γ) := by
      field_simp; ring
    rw [h]
    have : 0 ≤ η ^ 2 / (4 * Γ) := by positivity
    linarith
  have hdenpos : 0 < (1 - κ) * Gm := mul_pos (by linarith) hGm0
  obtain ⟨T0, hT0⟩ := ideal_direct P a ha Tst θ hwrong hkf hΓ (η / 2) (by positivity)
  set T0' := max T0 (Fintype.card E) with hT0'
  set f : ℕ → ℝ := fun t => 16 * (1 / (t : ℝ) ^ 2) with hf
  have hf0 : ∀ t, 0 ≤ f t := fun t => by positivity
  have hfs : Summable f := (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 16
  have hI0 : 0 ≤ thrI K a κ Gm := thrI_nonneg K a κ Gm hK ha hκ0 hGm0
  refine ⟨(T0' : ℝ) + 3 + thrI K a κ Gm / ((1 - κ) * Gm) + ∑' t, f t, fun δ hδ hδ1 => ?_⟩
  set L := Real.log (1 / δ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  set Zlo : (ℕ → ℝ) → ℕ → ℝ := fun ω t =>
    if Fintype.card E ≤ t then Zh P a Tst (runH P θ t ω) else 0 with hZlo
  set thr : (ℕ → ℝ) → ℕ → ℝ := fun ω t => bthr a δ (hN (runH P θ t ω)) with hthr
  have hfire : ∀ ω t, 1 ∣ t → thr ω t < Zlo ω t → tauI P a δ θ ω ≤ t := by
    intro ω t _ hlt
    change bthr a δ (hN (runH P θ t ω))
      < (if Fintype.card E ≤ t then Zh P a Tst (runH P θ t ω) else 0) at hlt
    split_ifs at hlt with hc
    · unfold tauI
      classical
      exact hitTime_le_of t ⟨hc, Tst, hlt⟩
    · exfalso
      have := bthr_nonneg a ha δ hδ hδ1.le (hN (runH P θ t ω)) (fun e => by
        rw [hN_runH]; exact Nat.cast_nonneg _)
      linarith
  have hthrle : ∀ ω (t : ℕ), thr ω t ≤ L + (K / 2) * Real.log (1 + t / a) := by
    intro ω t
    change bthr a δ (hN (runH P θ t ω)) ≤ _
    rw [hN_runH]
    unfold bthr
    exact code_thr_le a ha _ (fun e => Nat.cast_nonneg _) (t : ℝ)
      (fun e => run_count_le P θ ω t e) L
  have hdirect : ∀ ω t, T0' ≤ t → ω ∈ GoodWin P a θ t → Gm * t - 0 ≤ Zlo ω t := by
    intro ω t ht hω
    have hc : Fintype.card E ≤ t := le_trans (le_max_right _ _) ht
    change _ ≤ (if Fintype.card E ≤ t then Zh P a Tst (runH P θ t ω) else 0)
    rw [ite_cond_eq_true _ _ (eq_true hc), sub_zero]
    exact hT0 t (le_trans (le_max_left _ _) ht) ω hω
  have hwin := win_of_direct Zlo thr (GoodWin P a θ) L 0 K a κ Gm hK ha hκ0 hκ1 hGm0 T0'
    hdirect hthrle
  set t1 := max T0' (crossT L 0 K a κ Gm) with ht1
  have hbad : ∀ t, t1 + 1 ≤ t →
      streamMeasure (GoodWin P a θ (lastCheck 1 t))ᶜ ≤ ENNReal.ofReal (f t) := by
    intro t ht
    rw [show lastCheck 1 t = t by simp [lastCheck]]
    exact goodWin_compl_le P a ha θ t (by omega)
  have hE := expect_le streamMeasure (tauI P a δ θ) (measurable_tauI P a δ ha θ) 1 one_pos Zlo thr
    (GoodWin P a θ) hfire t1 hwin f hf0 hfs hbad
  have hRHS : ((t1 + 1 : ℕ) : ℝ≥0∞) + ENNReal.ofReal (∑' t, f t) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, ENNReal.ofReal_ne_top⟩
  refine ⟨ne_top_of_le_ne_top hRHS hE, ?_⟩
  have hreal : (∫⁻ ω, (tauI P a δ θ ω).toENNReal ∂streamMeasure).toReal
      ≤ ((t1 + 1 : ℕ) : ℝ) + ∑' t, f t := by
    have := ENNReal.toReal_mono hRHS hE
    rwa [ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal (tsum_nonneg hf0)] at this
  -- the crossing time
  have hy0 : 0 ≤ (L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm) :=
    div_nonneg (by linarith) hdenpos.le
  have hcross : (crossT L 0 K a κ Gm : ℝ) ≤ (L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm) + 2 := by
    unfold crossT
    push_cast
    have := Nat.ceil_lt_add_one hy0
    linarith
  have ht1R : ((t1 + 1 : ℕ) : ℝ)
      ≤ T0' + ((L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm) + 2) + 1 := by
    have h1 : t1 ≤ T0' + crossT L 0 K a κ Gm :=
      max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
    have h2 : ((t1 : ℕ) : ℝ) ≤ (T0' : ℝ) + (crossT L 0 K a κ Gm : ℝ) := by exact_mod_cast h1
    push_cast
    linarith
  have hLq : L / ((1 - κ) * Gm) ≤ L / (Γ - η) :=
    div_le_div_of_nonneg_left hL0 (by linarith) hden
  have hsplit : (L + 0 + thrI K a κ Gm) / ((1 - κ) * Gm)
      = L / ((1 - κ) * Gm) + thrI K a κ Gm / ((1 - κ) * Gm) := by
    rw [add_zero, add_div]
  linarith

/-- **The upper rate of the ideal learner.** -/
theorem ideal_upper_rate (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (hkf : ∀ s : ℕ, (s : ℝ) + 1 ≤ P.kf s)
    (hΓ : 0 < GamT P Tst θ) :
    CIGAMF.P13.PaperAEndgame.UpperRate
      (fun δ => (∫⁻ ω, (tauI P a δ θ ω).toENNReal ∂streamMeasure).toReal) (GamT P Tst θ) :=
  upper_rate_of_bound _ _ hΓ fun η hη hηΓ => by
    obtain ⟨A, hA⟩ := ideal_expect_bound P a ha Tst θ hwrong hkf hΓ η hη hηΓ
    exact ⟨A, fun δ hδ hδ1 => (hA δ hδ hδ1).2⟩

/-- **The expected stopping time is finite** at every level. -/
theorem ideal_finite (a : ℝ) (ha : 0 < a) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (hkf : ∀ s : ℕ, (s : ℝ) + 1 ≤ P.kf s)
    (hΓ : 0 < GamT P Tst θ) :
    ∀ δ, 0 < δ → δ < 1 → (∫⁻ ω, (tauI P a δ θ ω).toENNReal ∂streamMeasure) ≠ ⊤ := by
  obtain ⟨A, hA⟩ := ideal_expect_bound P a ha Tst θ hwrong hkf hΓ (GamT P Tst θ / 2)
    (by positivity) (by linarith)
  exact fun δ hδ hδ1 => (hA δ hδ hδ1).1

/-- **Correctness**: a wrong answer is returned with probability at most `(|Ans| - 1) delta`. -/
theorem ideal_correct (a : ℝ) (ha : 0 < a) (δ : ℝ) (hδ : 0 < δ) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) :
    streamMeasure {ω | ∃ t, stopAt P a δ t (runH P θ t ω) ∧ answerAt P a (runH P θ t ω) ≠ Tst}
      ≤ ((Fintype.card Ans - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal δ := by
  have hsub : {ω | ∃ t, stopAt P a δ t (runH P θ t ω) ∧ answerAt P a (runH P θ t ω) ≠ Tst}
      ⊆ ⋃ T ∈ (univ.erase Tst : Finset Ans),
          {ω | ∃ t, stopAt P a δ t (runH P θ t ω) ∧ answerAt P a (runH P θ t ω) = T} := by
    rintro ω ⟨t, hs, hne⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨_, hne, t, hs, rfl⟩
  refine le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le _ _) ?_)
  refine le_trans (sum_le_sum fun T hT =>
    wrong_answer_le P a δ ha hδ θ T (hwrong T (mem_erase.mp hT).1)) (le_of_eq ?_)
  rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul]

#print axioms inv_sqrt_pow4_le
#print axioms goodWin_compl_le
#print axioms ideal_expect_bound
#print axioms ideal_upper_rate
#print axioms ideal_finite
#print axioms ideal_correct

end CIGAMF.P13.PaperA7IdealUpper
