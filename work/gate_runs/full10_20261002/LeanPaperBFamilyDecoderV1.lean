import «LeanPaperBFamilyLawV1»
import «LeanPaperBParityDecoderV1»

/-!
# Paper B: the latent family's decoders, and both rates on the Gaussian model

`LeanPaperBFamilyChannelV1` proved the lower rates on the latent family.  This module gives
the matching upper rates, by explicit decoders on the same Gaussian channel, so both minimax
rates on the latent family are theorems.

* `near_error`: a generic nearest-mean test.  On ANY channel, a scheduled policy compares the
  sum of a bounded feature over the rounds given to query `j` with two candidate means.  If the
  true mean is `b`, choosing `a` has probability at most `2 exp(-(n |a - b| / 2)^2 / (2H))`.
  This is `test_upper_tail` and `test_lower_tail`.
* `dChan`: the latent family's channel with the dummy, the decision probe `z_1`, and the tail
  probe `(1/r) sum z_tail`.
* `safe_decoder`: `N` rounds of the decision probe with feature `cos`.  The nearest candidate
  mean decides `u`, and the answer is safe with probability `>= 1 - delta` at every world once
  `N >= 8 log(2/delta) / (G_dec h)^2`.
* `id_decoder`: `N` rounds of each probe; the `cos` test decides `u` and the `feat r` test decides
  `v`.  Both are right with probability `>= 1 - delta` once `N >= 16 log(4/delta) / (G_I h^r)^2`.
* `family_safe_rate`, `family_id_rate`: together with the lower rates,
  `c log(1/delta)/h^2 <= N*_safe <= C log(1/delta)/h^2` and the same with `h^{2r}` for
  identification, on the latent Gaussian family.  The decoders also show that the lower-rate
  theorems' hypotheses are satisfiable.
-/

namespace CIGAMF.P13.PaperBFamilyDecoder

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBRates CIGAMF.P13.PaperBWorlds CIGAMF.P13.PaperBParityChiSq
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration CIGAMF.P13.PaperBSchedule
open CIGAMF.P13.PaperBSchedTest CIGAMF.P13.PaperBParityLaw CIGAMF.P13.PaperBParityGap
open CIGAMF.P13.PaperBParityTest CIGAMF.P13.PaperBParityDecoder
open CIGAMF.P13.PaperBFamilyChannel CIGAMF.P13.PaperBFamilyLaw

/-! ## 1. A nearest-mean test on any channel -/

section Generic

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- The raw sum of a feature over the rounds the schedule gives to `j`. -/
noncomputable def rawS (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ) (H : ℕ) (ω : Hist Q H) : ℝ :=
  ∑ i : Fin H, if sched i = j then f (ω i).2 else 0

/-- The number of rounds the schedule gives to `j`. -/
noncomputable def cntS (sched : ℕ → Q) (j : Q) (H : ℕ) : ℝ :=
  ∑ i : Fin H, if sched i = j then (1 : ℝ) else 0

theorem cntS_nonneg (sched : ℕ → Q) (j : Q) (H : ℕ) : 0 ≤ cntS sched j H :=
  Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

theorem testSum_eq_rawS (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ) (c : ℝ) (H : ℕ) (ω : Hist Q H) :
    testSum sched j f c H ω = rawS sched j f H ω - cntS sched j H * c := by
  unfold testSum rawS cntS
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

theorem measurable_rawS (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ) (hf : Measurable f) (H : ℕ) :
    Measurable (rawS sched j f H) := by
  unfold rawS
  refine Finset.measurable_sum _ fun i _ => ?_
  split_ifs
  · exact hf.comp (measurable_snd.comp (measurable_pi_apply i))
  · exact measurable_const

theorem measurableSet_near (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ) (hf : Measurable f) (H : ℕ)
    (a b : ℝ) :
    MeasurableSet {ω : Hist Q H | |rawS sched j f H ω - cntS sched j H * a|
      ≤ |rawS sched j f H ω - cntS sched j H * b|} :=
  measurableSet_le ((measurable_rawS sched j f hf H).sub_const _).abs
    ((measurable_rawS sched j f hf H).sub_const _).abs

/-- **The nearest-mean test errs with exponentially small probability.**  If the true mean of
the feature at query `j` is `b`, the event that the sum is at least as near `n a` as `n b` has
probability at most `2 exp(-(n |b - a| / 2)^2 / (2H))`. -/
theorem near_error (C : Channel W Q) (w : W) (sched : ℕ → Q) (j : Q) (f : ℝ → ℝ)
    (hf : Measurable f) (hb : ∀ y, |f y| ≤ 1) (H : ℕ) (hH : 0 < H) (a b : ℝ)
    (htrue : fmean C w (onQuery j f hf hb) j = b) :
    hist C (schedPolicy sched) w H
        {ω | |rawS sched j f H ω - cntS sched j H * a|
          ≤ |rawS sched j f H ω - cntS sched j H * b|}
      ≤ 2 * ENNReal.ofReal (Real.exp (-((cntS sched j H * |b - a| / 2) ^ 2) / (2 * H))) := by
  set ε := cntS sched j H * |b - a| / 2 with hε
  have hε0 : 0 ≤ ε := div_nonneg (mul_nonneg (cntS_nonneg _ _ _) (abs_nonneg _)) (by norm_num)
  have hsub : {ω | |rawS sched j f H ω - cntS sched j H * a|
      ≤ |rawS sched j f H ω - cntS sched j H * b|}
      ⊆ {ω | ε ≤ testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω}
        ∪ {ω | testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω ≤ -ε} := by
    intro ω hω
    have hdev := dev_of_nearer (rawS sched j f H ω) (cntS sched j H) b a (cntS_nonneg _ _ _) hω
    simp only [Set.mem_union, Set.mem_setOf_eq, htrue, testSum_eq_rawS]
    rcases abs_ge_split _ _ hdev with h1 | h1
    · left; exact h1
    · right; exact h1
  calc hist C (schedPolicy sched) w H _
      ≤ hist C (schedPolicy sched) w H
          ({ω | ε ≤ testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω}
            ∪ {ω | testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω ≤ -ε}) :=
        measure_mono hsub
    _ ≤ hist C (schedPolicy sched) w H
          {ω | ε ≤ testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω}
        + hist C (schedPolicy sched) w H
          {ω | testSum sched j f (fmean C w (onQuery j f hf hb) j) H ω ≤ -ε} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * H)))
        + ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * H))) :=
        add_le_add (test_upper_tail C w sched j f hf hb H hH ε hε0)
          (test_lower_tail C w sched j f hf hb H hH ε hε0)
    _ = 2 * ENNReal.ofReal (Real.exp (-(ε ^ 2) / (2 * H))) := (two_mul _).symm

/-- An exponential error below a target, from a sample size. -/
theorem exp_le_of_budget (n g H L : ℝ) (hH : 0 < H) (hbig : L ≤ (n * g / 2) ^ 2 / (2 * H)) :
    Real.exp (-((n * g / 2) ^ 2) / (2 * H)) ≤ Real.exp (-L) := by
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith

end Generic

/-! ## 2. The latent family's two-probe channel -/

noncomputable def dAH : Fin 3 → Fin 3 → ℝ := ![decH, decH, tailH]
noncomputable def dAT (r : ℕ) : Fin 3 → Fin r → ℝ := ![decT r, decT r, tailT r]

theorem dNorm (r : ℕ) (hr : 0 < r) : ∀ q, ∑ i, |dAH q i| + ∑ i, |dAT r q i| ≤ 1 := by
  intro q
  fin_cases q
  · exact decNorm r
  · exact decNorm r
  · exact tailNorm r hr

/-- The channel the decoders run on. -/
noncomputable def dChan (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) : Channel (Bool × Bool) (Fin 3) :=
  famChan σ h hσ dAH (dAT r)

/-- The decision probe's candidate mean at `u`. -/
noncomputable def cDec (σ h u : ℝ) : ℝ :=
  Real.cos (3 * u + h) * Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2))

/-- The tail probe's candidate mean at `v`. -/
noncomputable def dTail (r : ℕ) (σ h v : ℝ) : ℝ :=
  Real.cos 3 * Real.cos 2 ^ 2 * featMean r (obsLaw r v h (var2 σ))

theorem hcos : Measurable Real.cos := Real.continuous_cos.measurable
theorem hbcos : ∀ y, |Real.cos y| ≤ 1 := fun y => Real.abs_cos_le_one y

theorem fmean_dec (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) (w : Bool × Bool) :
    fmean (dChan r σ h hσ) w (onQuery 1 Real.cos hcos hbcos) 1 = cDec σ h (uOf w) := by
  unfold fmean onQuery
  simp only [if_true]
  unfold dChan
  rw [obsLawC_famChan σ h hσ dAH (dAT r) w 1 (by decide)]
  have e1 : dAH 1 = decH := rfl
  have e2 : dAT r 1 = decT r := rfl
  rw [e1, e2, decMean_eq σ h (uOf w) (vOf w) (sgnB_pm _) (sgnB_pm _)]
  rfl

theorem fmean_tail (r : ℕ) (σ h : ℝ) (hσ : 0 < σ) (w : Bool × Bool) :
    fmean (dChan r σ h hσ) w (onQuery 2 (feat r) (continuous_feat r).measurable (feat_abs_le r)) 2
      = dTail r σ h (vOf w) := by
  unfold fmean onQuery
  simp only [if_true]
  unfold dChan
  rw [obsLawC_famChan σ h hσ dAH (dAT r) w 2 (by decide)]
  have e1 : dAH 2 = tailH := rfl
  have e2 : dAT r 2 = tailT r := rfl
  rw [e1, e2]
  exact tailMean_eq σ h (uOf w) (vOf w) (sgnB_pm _)

/-! ## 3. The safe decoder -/

/-- The decision gap constant. -/
noncomputable def Gdec (σ : ℝ) : ℝ :=
  3 / 2 * Real.sin 3 * Real.cos 2 ^ 2 * Real.cos 1 * Real.exp (-(σ ^ 2 / 2))

theorem cos2_ne_zero : Real.cos 2 ≠ 0 := by
  have : Real.cos 2 < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [pi_lt_d2])
    (by linarith [pi_gt_three])
  exact this.ne

theorem Gdec_pos (σ : ℝ) : 0 < Gdec σ := by
  unfold Gdec
  have hs3 : 0 < Real.sin 3 := Real.sin_pos_of_pos_of_lt_pi (by norm_num) pi_gt_three
  have hc1 : 0 < Real.cos 1 := Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_gt_three],
    by linarith [pi_gt_three]⟩
  have hc2 : 0 < Real.cos 2 ^ 2 := by have := cos2_ne_zero; positivity
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hs3) hc2) hc1) (Real.exp_pos _)

theorem dec_gap (r : ℕ) (σ h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    Gdec σ * h ≤ |cDec σ h 1 - cDec σ h (-1)| := by
  have := dec_gap_lower (r := r) σ h 1 hh hh1 (Or.inl rfl)
  rw [decMean_eq σ h 1 1 (Or.inl rfl) (Or.inl rfl),
    decMean_eq σ h (-1) 1 (Or.inr rfl) (Or.inl rfl)] at this
  exact this

/-- The safe decoder's schedule: every round queries the decision probe. -/
def schedS : ℕ → Fin 3 := fun _ => 1

theorem cntS_schedS (N : ℕ) : cntS schedS (1 : Fin 3) N = N := by
  unfold cntS schedS
  simp

/-- The safe decoder's answer: the nearer candidate mean decides `u`. -/
noncomputable def safeOut (r : ℕ) (σ h : ℝ) (N : ℕ) (ω : Hist (Fin 3) N) : Fin (r + 3) :=
  if |rawS schedS 1 Real.cos N ω - cntS schedS 1 N * cDec σ h 1|
      ≤ |rawS schedS 1 Real.cos N ω - cntS schedS 1 N * cDec σ h (-1)| then 1 else 0

theorem measurable_safeOut (r : ℕ) (σ h : ℝ) (N : ℕ) : Measurable (safeOut r σ h N) := by
  unfold safeOut
  exact Measurable.ite (measurableSet_near schedS 1 Real.cos hcos N _ _) measurable_const
    measurable_const

/-- The safe decoder's sample size. -/
noncomputable def NS (σ h δ : ℝ) : ℕ := ⌈8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2⌉₊ + 1

/-- **The safe decoder is safe with probability at least `1 - delta` at every world.** -/
theorem safe_decoder_error (r : ℕ) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (w : Bool × Bool) :
    hist (dChan r σ h hσ) (schedPolicy schedS) w (NS σ h δ)
        {ω | safeOut r σ h (NS σ h δ) ω ∉ famSafe r w} ≤ ENNReal.ofReal δ := by
  set N := NS σ h δ with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hg := dec_gap r σ h hh hh1
  have hG := Gdec_pos σ
  have hGh : 0 < Gdec σ * h := mul_pos hG hh
  -- the budget makes each exponential at most delta / 2
  have hL : Real.log (2 / δ) ≤ (N * |cDec σ h 1 - cDec σ h (-1)| / 2) ^ 2 / (2 * N) := by
    have hceil : 8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2 ≤ N := by
      rw [hN]; unfold NS; push_cast
      linarith [Nat.le_ceil (8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2)]
    have hsq : (Gdec σ * h) ^ 2 ≤ |cDec σ h 1 - cDec σ h (-1)| ^ 2 :=
      pow_le_pow_left₀ hGh.le hg 2
    have hform : (N * |cDec σ h 1 - cDec σ h (-1)| / 2) ^ 2 / (2 * N)
        = N * |cDec σ h 1 - cDec σ h (-1)| ^ 2 / 8 := by
      field_simp; ring
    rw [hform]
    rw [div_le_iff₀ (by positivity)] at hceil
    nlinarith [hceil, hsq, hNR.le]
  have hexp : Real.exp (-((N * |cDec σ h 1 - cDec σ h (-1)| / 2) ^ 2) / (2 * N)) ≤ δ / 2 := by
    refine (exp_le_of_budget _ _ _ _ (by positivity) hL).trans (le_of_eq ?_)
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hbound : 2 * ENNReal.ofReal (Real.exp (-((N * |cDec σ h 1 - cDec σ h (-1)| / 2) ^ 2)
      / (2 * N))) ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  rcases Bool.eq_false_or_eq_true w.1 with hw | hw
  · -- u = +1: the answer is unsafe only if the decoder chose `cDec (-1)`
    have hsub : {ω | safeOut r σ h N ω ∉ famSafe r w}
        ⊆ {ω | |rawS schedS 1 Real.cos N ω - cntS schedS 1 N * cDec σ h (-1)|
            ≤ |rawS schedS 1 Real.cos N ω - cntS schedS 1 N * cDec σ h 1|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, safeOut, famSafe, hw, if_true] at hω ⊢
      split_ifs at hω with hc
      · simp at hω
      · push Not at hc; exact hc.le
    have huw : uOf w = 1 := by unfold uOf; rw [hw]; rfl
    have h := near_error (dChan r σ h hσ) w schedS 1 Real.cos hcos hbcos N hNpos
      (cDec σ h (-1)) (cDec σ h 1) (by rw [fmean_dec, huw])
    rw [cntS_schedS] at h
    refine (measure_mono hsub).trans ?_
    rw [cntS_schedS]
    exact h.trans hbound
  · -- u = -1: the answer is unsafe only if the decoder chose `cDec 1`
    have hsub : {ω | safeOut r σ h N ω ∉ famSafe r w}
        ⊆ {ω | |rawS schedS 1 Real.cos N ω - cntS schedS 1 N * cDec σ h 1|
            ≤ |rawS schedS 1 Real.cos N ω - cntS schedS 1 N * cDec σ h (-1)|} := by
      intro ω hω
      simp only [Set.mem_setOf_eq, safeOut, famSafe, hw, Bool.false_eq_true, if_false] at hω ⊢
      split_ifs at hω with hc
      · exact hc
      · simp at hω
    have huw : uOf w = -1 := by unfold uOf; rw [hw]; rfl
    have h := near_error (dChan r σ h hσ) w schedS 1 Real.cos hcos hbcos N hNpos
      (cDec σ h 1) (cDec σ h (-1)) (by rw [fmean_dec, huw])
    rw [cntS_schedS] at h
    refine (measure_mono hsub).trans ?_
    rw [cntS_schedS]
    rw [abs_sub_comm] at h
    exact h.trans hbound

/-- The safe decoder's cost is its horizon. -/
theorem safe_decoder_cost (r : ℕ) (σ h δ : ℝ) (hσ : 0 < σ) (w : Bool × Bool) :
    costN (dChan r σ h hσ) (schedPolicy schedS) w (NS σ h δ) ≤ (NS σ h δ : ℝ≥0∞) := by
  rw [costN_sched]
  exact_mod_cast schedCost_le schedS _ _

theorem NS_le (σ h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (NS σ h δ : ℝ) ≤ 8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2 + 2 := by
  unfold NS
  push_cast
  have hnn : 0 ≤ 8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2 := by
    have : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    positivity
  linarith [Nat.ceil_lt_add_one hnn]

/-! ## 4. The identification decoder -/

/-- The tail gap constant. -/
noncomputable def Gtail (r : ℕ) (σ : ℝ) : ℝ :=
  |Real.cos 3| * Real.cos 2 ^ 2 * (2 * Real.sin 1 * (3 / (4 * (r : ℝ))) ^ r * Real.exp (-(σ ^ 2 / 2)))

theorem Gtail_pos (r : ℕ) (hr : 0 < r) (σ : ℝ) : 0 < Gtail r σ := by
  unfold Gtail
  have hc3 : Real.cos 3 < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith [pi_lt_d2])
    (by linarith [pi_gt_three])
  have hs1 : 0 < Real.sin 1 := Real.sin_pos_of_pos_of_lt_pi one_pos (by linarith [pi_gt_three])
  have hc2 : 0 < Real.cos 2 ^ 2 := by have := cos2_ne_zero; positivity
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have : 0 < |Real.cos 3| := abs_pos.mpr hc3.ne
  positivity

theorem tail_gap (r : ℕ) (hr : 0 < r) (σ h : ℝ) (hh : 0 < h) (hhr : h ≤ r) :
    Gtail r σ * h ^ r ≤ |dTail r σ h 1 - dTail r σ h (-1)| := by
  have := tail_gap_lower hr σ h 1 (Or.inl rfl) hh hhr
  rw [tailMean_eq σ h 1 1 (Or.inl rfl), tailMean_eq σ h 1 (-1) (Or.inl rfl)] at this
  unfold Gtail dTail
  calc _ = |Real.cos 3| * Real.cos 2 ^ 2
        * (2 * Real.sin 1 * (3 / (4 * (r : ℝ))) ^ r * h ^ r * Real.exp (-(σ ^ 2 / 2))) := by ring
    _ ≤ _ := this

/-- The identification gap constant, uniform over both tests at order `h^r`. -/
noncomputable def GI (r : ℕ) (σ : ℝ) : ℝ := min (Gdec σ) (Gtail r σ)

theorem GI_pos (r : ℕ) (hr : 0 < r) (σ : ℝ) : 0 < GI r σ :=
  lt_min (Gdec_pos σ) (Gtail_pos r hr σ)

/-- The identification decoder's schedule: `N` rounds of the decision probe, then the tail. -/
def schedI (N : ℕ) : ℕ → Fin 3 := fun i => if i < N then 1 else 2

theorem cntS_schedI_one (N : ℕ) : cntS (schedI N) (1 : Fin 3) (2 * N) = N := by
  unfold cntS schedI
  rw [Fin.sum_univ_eq_sum_range (fun i => if (if i < N then (1 : Fin 3) else 2) = 1 then (1 : ℝ)
    else 0) (2 * N), two_mul, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range N, (if (if x < N then (1 : Fin 3) else 2) = 1 then (1 : ℝ) else 0)
      = N := by
    rw [Finset.sum_congr rfl fun x hx => by
      rw [if_pos (Finset.mem_range.mp hx), if_pos rfl]]
    simp
  have h2 : ∑ x ∈ Finset.range N,
      (if (if N + x < N then (1 : Fin 3) else 2) = 1 then (1 : ℝ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    have hx : ¬ (N + x < N) := by omega
    simp [hx]
  rw [h1, h2, add_zero]

theorem cntS_schedI_two (N : ℕ) : cntS (schedI N) (2 : Fin 3) (2 * N) = N := by
  unfold cntS schedI
  rw [Fin.sum_univ_eq_sum_range (fun i => if (if i < N then (1 : Fin 3) else 2) = 2 then (1 : ℝ)
    else 0) (2 * N), two_mul, Finset.sum_range_add]
  have h1 : ∑ x ∈ Finset.range N, (if (if x < N then (1 : Fin 3) else 2) = 2 then (1 : ℝ) else 0)
      = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [if_pos (Finset.mem_range.mp hx)]
    simp
  have h2 : ∑ x ∈ Finset.range N,
      (if (if N + x < N then (1 : Fin 3) else 2) = 2 then (1 : ℝ) else 0) = N := by
    have hx : ∀ x, ¬ (N + x < N) := fun x => by omega
    simp [hx]
  rw [h1, h2, zero_add]

/-- The identification decoder's guess: the `cos` test decides `u`, the `feat r` test `v`. -/
noncomputable def idOut (r : ℕ) (σ h : ℝ) (N : ℕ) (ω : Hist (Fin 3) (2 * N)) : Bool × Bool :=
  (if |rawS (schedI N) 1 Real.cos (2 * N) ω - cntS (schedI N) 1 (2 * N) * cDec σ h 1|
      ≤ |rawS (schedI N) 1 Real.cos (2 * N) ω - cntS (schedI N) 1 (2 * N) * cDec σ h (-1)|
    then true else false,
   if |rawS (schedI N) 2 (feat r) (2 * N) ω - cntS (schedI N) 2 (2 * N) * dTail r σ h 1|
      ≤ |rawS (schedI N) 2 (feat r) (2 * N) ω - cntS (schedI N) 2 (2 * N) * dTail r σ h (-1)|
    then true else false)

theorem measurable_idOut (r : ℕ) (σ h : ℝ) (N : ℕ) : Measurable (idOut r σ h N) := by
  unfold idOut
  exact Measurable.prodMk
    (Measurable.ite (measurableSet_near (schedI N) 1 Real.cos hcos (2 * N) _ _) measurable_const
      measurable_const)
    (Measurable.ite (measurableSet_near (schedI N) 2 (feat r) (continuous_feat r).measurable
      (2 * N) _ _) measurable_const measurable_const)

/-- The identification decoder's sample size per probe. -/
noncomputable def NI (r : ℕ) (σ h δ : ℝ) : ℕ := ⌈16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2⌉₊ + 1

/-- One test of the identification decoder errs with probability at most `delta / 2`. -/
theorem id_test_error (C : Channel (Bool × Bool) (Fin 3)) (w : Bool × Bool) (N : ℕ) (hN : 0 < N)
    (j : Fin 3) (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ y, |f y| ≤ 1) (a b g δ : ℝ) (hδ : 0 < δ)
    (hg : 0 < g) (hgab : g ≤ |b - a|) (hcnt : cntS (schedI N) j (2 * N) = N)
    (hbudget : 16 * Real.log (4 / δ) / g ^ 2 ≤ N)
    (htrue : fmean C w (onQuery j f hf hb) j = b) :
    hist C (schedPolicy (schedI N)) w (2 * N)
        {ω | |rawS (schedI N) j f (2 * N) ω - cntS (schedI N) j (2 * N) * a|
          ≤ |rawS (schedI N) j f (2 * N) ω - cntS (schedI N) j (2 * N) * b|}
      ≤ ENNReal.ofReal (δ / 2) := by
  have hH : 0 < 2 * N := by omega
  have h := near_error C w (schedI N) j f hf hb (2 * N) hH a b htrue
  rw [hcnt] at h
  rw [hcnt]
  refine h.trans ?_
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : Real.log (4 / δ) ≤ ((N : ℝ) * |b - a| / 2) ^ 2 / (2 * ((2 * N : ℕ) : ℝ)) := by
    have hsq : g ^ 2 ≤ |b - a| ^ 2 := pow_le_pow_left₀ hg.le hgab 2
    have hform : ((N : ℝ) * |b - a| / 2) ^ 2 / (2 * ((2 * N : ℕ) : ℝ)) = N * |b - a| ^ 2 / 16 := by
      push_cast; field_simp; ring
    rw [hform]
    rw [div_le_iff₀ (by positivity)] at hbudget
    nlinarith [hbudget, hsq, hNR.le]
  have hexp : Real.exp (-(((N : ℝ) * |b - a| / 2) ^ 2) / (2 * ((2 * N : ℕ) : ℝ))) ≤ δ / 4 := by
    refine (exp_le_of_budget _ _ _ _ (by positivity) hL).trans (le_of_eq ?_)
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **The identification decoder names the world with probability at least `1 - delta`.** -/
theorem id_decoder_error (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (w : Bool × Bool) :
    hist (dChan r σ h hσ) (schedPolicy (schedI (NI r σ h δ))) w (2 * NI r σ h δ)
        {ω | idOut r σ h (NI r σ h δ) ω ∉ ({w} : Finset (Bool × Bool))} ≤ ENNReal.ofReal δ := by
  set N := NI r σ h δ with hN
  have hNpos : 0 < N := Nat.succ_pos _
  have hG := GI_pos r hr σ
  have hhr : h ^ r ≤ h := by
    calc h ^ r ≤ h ^ 1 := pow_le_pow_of_le_one hh.le hh1 hr
      _ = h := pow_one h
  have hGh : 0 < GI r σ * h ^ r := mul_pos hG (pow_pos hh r)
  have hbudget : 16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2 ≤ N := by
    rw [hN]; unfold NI; push_cast
    linarith [Nat.le_ceil (16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2)]
  -- the two gaps dominate G_I h^r
  have hgu : GI r σ * h ^ r ≤ |cDec σ h 1 - cDec σ h (-1)| :=
    (mul_le_mul (min_le_left _ _) hhr (pow_pos hh r).le (Gdec_pos σ).le).trans (dec_gap r σ h hh hh1)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hgv : GI r σ * h ^ r ≤ |dTail r σ h 1 - dTail r σ h (-1)| :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_pos hh r).le).trans
      (tail_gap r hr σ h hh (by linarith))
  -- a wrong guess forces one test to err
  set Eu := {ω : Hist (Fin 3) (2 * N) | |rawS (schedI N) 1 Real.cos (2 * N) ω
      - cntS (schedI N) 1 (2 * N) * cDec σ h (if w.1 then -1 else 1)|
      ≤ |rawS (schedI N) 1 Real.cos (2 * N) ω
      - cntS (schedI N) 1 (2 * N) * cDec σ h (if w.1 then 1 else -1)|} with hEu
  set Ev := {ω : Hist (Fin 3) (2 * N) | |rawS (schedI N) 2 (feat r) (2 * N) ω
      - cntS (schedI N) 2 (2 * N) * dTail r σ h (if w.2 then -1 else 1)|
      ≤ |rawS (schedI N) 2 (feat r) (2 * N) ω
      - cntS (schedI N) 2 (2 * N) * dTail r σ h (if w.2 then 1 else -1)|} with hEv
  have hsub : {ω | idOut r σ h N ω ∉ ({w} : Finset (Bool × Bool))} ⊆ Eu ∪ Ev := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Finset.mem_singleton] at hω
    rcases w with ⟨u, v⟩
    by_contra hcon
    simp only [Set.mem_union, hEu, hEv, Set.mem_setOf_eq, not_or, not_le] at hcon
    apply hω
    unfold idOut
    obtain ⟨hcu, hcv⟩ := hcon
    refine Prod.ext ?_ ?_
    · cases u <;> simp only [if_true, Bool.false_eq_true, if_false] at hcu ⊢
      · rw [if_neg (not_le.mpr hcu)]
      · rw [if_pos hcu.le]
    · cases v <;> simp only [if_true, Bool.false_eq_true, if_false] at hcv ⊢
      · rw [if_neg (not_le.mpr hcv)]
      · rw [if_pos hcv.le]
  have huTrue : fmean (dChan r σ h hσ) w (onQuery 1 Real.cos hcos hbcos) 1
      = cDec σ h (if w.1 then 1 else -1) := by
    rw [fmean_dec]; unfold uOf; cases w.1 <;> rfl
  have hvTrue : fmean (dChan r σ h hσ) w
      (onQuery 2 (feat r) (continuous_feat r).measurable (feat_abs_le r)) 2
      = dTail r σ h (if w.2 then 1 else -1) := by
    rw [fmean_tail]; unfold vOf; cases w.2 <;> rfl
  have hgu' : GI r σ * h ^ r ≤ |cDec σ h (if w.1 then 1 else -1) - cDec σ h (if w.1 then -1 else 1)| := by
    cases w.1
    · simp only [Bool.false_eq_true, if_false]; rw [abs_sub_comm]; exact hgu
    · simp only [if_true]; exact hgu
  have hgv' : GI r σ * h ^ r ≤ |dTail r σ h (if w.2 then 1 else -1) - dTail r σ h (if w.2 then -1 else 1)| := by
    cases w.2
    · simp only [Bool.false_eq_true, if_false]; rw [abs_sub_comm]; exact hgv
    · simp only [if_true]; exact hgv
  have hu := id_test_error (dChan r σ h hσ) w N hNpos 1 Real.cos hcos hbcos _ _ _ δ hδ hGh hgu'
    (cntS_schedI_one N) hbudget huTrue
  have hv := id_test_error (dChan r σ h hσ) w N hNpos 2 (feat r) (continuous_feat r).measurable
    (feat_abs_le r) _ _ _ δ hδ hGh hgv' (cntS_schedI_two N) hbudget hvTrue
  calc hist (dChan r σ h hσ) (schedPolicy (schedI N)) w (2 * N) _
      ≤ hist (dChan r σ h hσ) (schedPolicy (schedI N)) w (2 * N) (Eu ∪ Ev) := measure_mono hsub
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hu hv
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

theorem id_decoder_cost (r : ℕ) (σ h δ : ℝ) (hσ : 0 < σ) (w : Bool × Bool) :
    costN (dChan r σ h hσ) (schedPolicy (schedI (NI r σ h δ))) w (2 * NI r σ h δ)
      ≤ ((2 * NI r σ h δ : ℕ) : ℝ≥0∞) := by
  rw [costN_sched]
  exact_mod_cast schedCost_le _ _ _

theorem NI_le (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hh : 0 < h) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (NI r σ h δ : ℝ) ≤ 16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2 + 2 := by
  unfold NI
  push_cast
  have hnn : 0 ≤ 16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2 := by
    have : 0 ≤ Real.log (4 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
    positivity
  linarith [Nat.ceil_lt_add_one hnn]

/-! ## 5. Both rates on the latent Gaussian family -/

theorem prob_of_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : Set Ω) (hS : MeasurableSet S) (δ : ℝ) (hδ : 0 ≤ δ) (h : μ Sᶜ ≤ ENNReal.ofReal δ) :
    1 - δ ≤ μ.real S := by
  have hc : μ.real Sᶜ ≤ δ := by
    rw [measureReal_def]
    exact (ENNReal.toReal_le_of_le_ofReal hδ h)
  rw [measureReal_compl hS, probReal_univ] at hc
  linarith

/-- **The safe decision's rate on the latent Gaussian family, both sides.**  The decoder is
safe with probability `>= 1 - delta` at every world and costs at most
`8 log(2/delta)/(G_dec h)^2 + 2` queries; and every finite-horizon policy that is safe with
probability `>= 1 - delta` on this channel pays `((1-delta) log(1/delta) - log 2)/(Cu h^2)`
queries at the world `u = v = +1` (`family_safe_lower`, applied here to the decoder itself). -/
theorem family_safe_rate (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∀ w, 1 - δ ≤ (hist (dChan r σ h hσ) (schedPolicy schedS) w (NS σ h δ)).real
        {ω | safeOut r σ h (NS σ h δ) ω ∈ famSafe r w})
      ∧ (∀ w, costN (dChan r σ h hσ) (schedPolicy schedS) w (NS σ h δ)
          ≤ ENNReal.ofReal (8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2 + 2))
      ∧ ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
          ≤ ENNReal.ofReal (Cu σ 1 * h ^ 2)
            * costN (dChan r σ h hσ) (schedPolicy schedS) (true, true) (NS σ h δ) := by
  have hmeas : ∀ w, MeasurableSet {ω | safeOut r σ h (NS σ h δ) ω ∈ famSafe r w} :=
    fun w => measurable_safeOut r σ h _ (MeasurableSet.of_discrete)
  have hcorr : ∀ w, 1 - δ ≤ (hist (dChan r σ h hσ) (schedPolicy schedS) w (NS σ h δ)).real
      {ω | safeOut r σ h (NS σ h δ) ω ∈ famSafe r w} := by
    intro w
    haveI := hist_prob (dChan r σ h hσ) (schedPolicy schedS) w (NS σ h δ)
    refine prob_of_error _ _ (hmeas w) δ hδ.le ?_
    have := safe_decoder_error r σ h δ hσ hh hh1 hδ hδ1 w
    rwa [show {ω | safeOut r σ h (NS σ h δ) ω ∈ famSafe r w}ᶜ
      = {ω | safeOut r σ h (NS σ h δ) ω ∉ famSafe r w} from rfl]
  refine ⟨hcorr, fun w => (safe_decoder_cost r σ h δ hσ w).trans ?_, ?_⟩
  · rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (NS_le σ h δ hh hδ hδ1)
  · exact family_safe_lower σ h 1 hσ hh.le hh1 dAH (dAT r) (dNorm r hr) _ _ _ hmeas δ hδ hδ1 hcorr

/-- **Identification's rate on the latent Gaussian family, both sides.**  The decoder names the
world with probability `>= 1 - delta` at every world and costs at most
`2 (16 log(4/delta)/(G_I h^r)^2 + 2)` queries; every finite-horizon policy that identifies with
probability `>= 1 - delta` pays `((1-delta) log(1/delta) - log 2)/(Cv h^{2r})` queries. -/
theorem family_id_rate (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∀ w, 1 - δ ≤ (hist (dChan r σ h hσ) (schedPolicy (schedI (NI r σ h δ))) w
        (2 * NI r σ h δ)).real {ω | idOut r σ h (NI r σ h δ) ω ∈ ({w} : Finset (Bool × Bool))})
      ∧ (∀ w, costN (dChan r σ h hσ) (schedPolicy (schedI (NI r σ h δ))) w (2 * NI r σ h δ)
          ≤ ENNReal.ofReal (2 * (16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2 + 2)))
      ∧ ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
          ≤ ENNReal.ofReal (Cv r σ 1 * h ^ (2 * r))
            * costN (dChan r σ h hσ) (schedPolicy (schedI (NI r σ h δ))) (true, true)
                (2 * NI r σ h δ) := by
  have hmeas : ∀ w, MeasurableSet {ω | idOut r σ h (NI r σ h δ) ω ∈ ({w} : Finset (Bool × Bool))} :=
    fun w => measurable_idOut r σ h _ ((Set.to_countable _).measurableSet)
  have hcorr : ∀ w, 1 - δ ≤ (hist (dChan r σ h hσ) (schedPolicy (schedI (NI r σ h δ))) w
      (2 * NI r σ h δ)).real {ω | idOut r σ h (NI r σ h δ) ω ∈ ({w} : Finset (Bool × Bool))} := by
    intro w
    haveI := hist_prob (dChan r σ h hσ) (schedPolicy (schedI (NI r σ h δ))) w (2 * NI r σ h δ)
    refine prob_of_error _ _ (hmeas w) δ hδ.le ?_
    exact id_decoder_error r hr σ h δ hσ hh hh1 hδ w
  refine ⟨hcorr, fun w => (id_decoder_cost r σ h δ hσ w).trans ?_, ?_⟩
  · rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    linarith [NI_le r hr σ h δ hh hδ hδ1]
  · exact family_id_lower σ h 1 hσ hh.le hh1 dAH (dAT r) (dNorm r hr) _ _ _ hmeas δ hδ hδ1 hcorr

/-- **The safe decision's minimax rate on the latent Gaussian family.**  Some finite probe
family, policy and decoder are safe with probability `>= 1 - delta` at every world within
`8 log(2/delta)/(G_dec h)^2 + 2` queries; and EVERY finite probe family of unit `l1` norm, with
every finite-horizon adaptive policy and decoder safe with probability `>= 1 - delta`, pays at
least `((1-delta) log(1/delta) - log 2)/(Cu h^2)` queries at the world `u = v = +1`. -/
theorem family_safe_minimax (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∃ (k : ℕ) (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
        (_ : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1)
        (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Fin (r + 3)),
        (∀ w, 1 - δ ≤ (hist (famChan σ h hσ aH aT) pol w n).real {ω | out ω ∈ famSafe r w})
        ∧ ∀ w, costN (famChan σ h hσ aH aT) pol w n
            ≤ ENNReal.ofReal (8 * Real.log (2 / δ) / (Gdec σ * h) ^ 2 + 2))
    ∧ ∀ (k : ℕ) (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
        (_ : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1)
        (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Fin (r + 3))
        (_ : ∀ w, MeasurableSet {ω | out ω ∈ famSafe r w})
        (_ : ∀ w, 1 - δ ≤ (hist (famChan σ h hσ aH aT) pol w n).real
          {ω | out ω ∈ famSafe r w}),
        ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
          ≤ ENNReal.ofReal (Cu σ 1 * h ^ 2) * costN (famChan σ h hσ aH aT) pol (true, true) n := by
  obtain ⟨hc, hcost, -⟩ := family_safe_rate r hr σ h δ hσ hh hh1 hδ hδ1
  exact ⟨⟨2, dAH, dAT r, dNorm r hr, _, _, _, hc, hcost⟩,
    fun k aH aT hn pol n out hm hcorr =>
      family_safe_lower σ h 1 hσ hh.le hh1 aH aT hn pol n out hm δ hδ hδ1 hcorr⟩

/-- **Identification's minimax rate on the latent Gaussian family.**  Some finite probe family,
policy and decoder name the world with probability `>= 1 - delta` within
`2 (16 log(4/delta)/(G_I h^r)^2 + 2)` queries; and every finite probe family of unit `l1` norm,
with every finite-horizon adaptive policy and decoder that identifies with probability
`>= 1 - delta`, pays at least `((1-delta) log(1/delta) - log 2)/(Cv h^{2r})` queries. -/
theorem family_id_minimax (r : ℕ) (hr : 0 < r) (σ h δ : ℝ) (hσ : 0 < σ) (hh : 0 < h)
    (hh1 : h ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∃ (k : ℕ) (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
        (_ : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1)
        (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Bool × Bool),
        (∀ w, 1 - δ ≤ (hist (famChan σ h hσ aH aT) pol w n).real
          {ω | out ω ∈ ({w} : Finset (Bool × Bool))})
        ∧ ∀ w, costN (famChan σ h hσ aH aT) pol w n
            ≤ ENNReal.ofReal (2 * (16 * Real.log (4 / δ) / (GI r σ * h ^ r) ^ 2 + 2)))
    ∧ ∀ (k : ℕ) (aH : Fin (k + 1) → Fin 3 → ℝ) (aT : Fin (k + 1) → Fin r → ℝ)
        (_ : ∀ q, ∑ i, |aH q i| + ∑ i, |aT q i| ≤ 1)
        (pol : Policy (Fin (k + 1))) (n : ℕ) (out : Hist (Fin (k + 1)) n → Bool × Bool)
        (_ : ∀ w, MeasurableSet {ω | out ω ∈ ({w} : Finset (Bool × Bool))})
        (_ : ∀ w, 1 - δ ≤ (hist (famChan σ h hσ aH aT) pol w n).real
          {ω | out ω ∈ ({w} : Finset (Bool × Bool))}),
        ENNReal.ofReal ((1 - δ) * Real.log (1 / δ) - Real.log 2)
          ≤ ENNReal.ofReal (Cv r σ 1 * h ^ (2 * r))
            * costN (famChan σ h hσ aH aT) pol (true, true) n := by
  obtain ⟨hc, hcost, -⟩ := family_id_rate r hr σ h δ hσ hh hh1 hδ hδ1
  exact ⟨⟨2, dAH, dAT r, dNorm r hr, _, _, _, hc, hcost⟩,
    fun k aH aT hn pol n out hm hcorr =>
      family_id_lower σ h 1 hσ hh.le hh1 aH aT hn pol n out hm δ hδ hδ1 hcorr⟩

#print axioms near_error
#print axioms fmean_dec
#print axioms fmean_tail
#print axioms safe_decoder_error
#print axioms id_decoder_error
#print axioms family_safe_rate
#print axioms family_id_rate
#print axioms family_safe_minimax
#print axioms family_id_minimax

end CIGAMF.P13.PaperBFamilyDecoder
