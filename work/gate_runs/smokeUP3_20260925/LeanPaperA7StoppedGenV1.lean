import «LeanPaperA7IdealStoppedV1»

/-!
# Paper A7: the GLR stop and the stopped policy, for ANY base learner

`LeanPaperA7IdealStopV1`, `LeanPaperA7IdealUpperV1` (correctness) and
`LeanPaperA7IdealStoppedV1` are stated for the ideal learner.  Nothing in them uses its
oracle: the stop reads only the history, and the coupling only the rule.  This module states
them for an arbitrary measurable learner `L : Learner E` run with the GLR stop of a
specification `P` (its noise and alternatives), so that the same lower-bound machinery applies
to other allocation rules -- in Paper A6, the surrogate's.

* `runG`, `tauG` -- the run and the untruncated hitting time of the GLR stop;
* `wrong_answer_leG`, `correctG` -- delta-correctness, for every allocation rule;
* `stoppedG`, `runSG_eq` -- the stopped policy on `E ⊕ Unit` and its pathwise coupling;
* `ansEv_alt_leG`, `ansEv_true_geG` -- the answer event's two probability bounds;
* `cnt_eq_at_min` -- **the stopped history's real-cell counts are the run's counts at
  `m = min(n, tau)`**, cell by cell, with the same `m` for every cell.
-/

namespace CIGAMF.P13.PaperA7StoppedGen

open Finset MeasureTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop
open CIGAMF.P13.PaperA7IdealRun CIGAMF.P13.PaperAStopping CIGAMF.P13.PaperA7IdealStopped
open CIGAMF.P13.PaperABridgeDummy CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperA7GLRMeas

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans) (a δ : ℝ) (L : Learner E)

/-! ## 1. The run, the stop, the hitting time -/

/-- The observed history of `t` rounds in world `theta`. -/
noncomputable def runG (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) : Fin t → E × ℝ :=
  histF L θ P.σ t (Xp t ω)

theorem measurable_runG (θ : E → ℝ) (t : ℕ) : Measurable (runG P L θ t) :=
  (measurable_histF L θ P.σ t).comp (measurable_Xp t)

theorem hN_runG (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    hN (runG P L θ t ω) = Nc L θ P.σ t ω := by
  funext e
  unfold hN runG Nc NF
  push_cast
  rfl

theorem hMu_runG (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    hMu (runG P L θ t ω) = muHat L θ P.σ t ω := by
  funext e
  unfold hMu muHat
  rw [hN_runG]
  rfl

theorem restr_runG (θ : E → ℝ) (t s : ℕ) (hs : s ≤ t) (ω : ℕ → ℝ) :
    restr s hs (runG P L θ t ω) = runG P L θ s ω := by
  unfold runG
  rw [histF_restr]
  rfl

theorem Nc_succG (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) (e : E) :
    Nc L θ P.σ (t + 1) ω e
      = Nc L θ P.σ t ω e + if e = L.rule t (runG P L θ t ω) then 1 else 0 := by
  have hq : qF L θ P.σ t (Xp t ω) = L.rule t (runG P L θ t ω) := rfl
  unfold Nc
  rw [Xp_succ, NF_snoc, hq]
  push_cast
  by_cases h : e = L.rule t (runG P L θ t ω)
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem Nc_zeroG (θ : E → ℝ) (ω : ℕ → ℝ) (e : E) : Nc L θ P.σ 0 ω e = 0 := by
  unfold Nc NF; simp

/-- **The hitting time of the GLR stop.** -/
noncomputable def tauG (θ : E → ℝ) (ω : ℕ → ℝ) : ℕ∞ := by
  classical
  exact hitTime fun t => stopAt P a δ t (runG P L θ t ω)

theorem measurableSet_stopG (ha : 0 < a) (θ : E → ℝ) (t : ℕ) :
    MeasurableSet {ω | stopAt P a δ t (runG P L θ t ω)} :=
  measurableSet_setOfPred.mpr ((measurable_stopH P a δ ha t).comp (measurable_runG P L θ t))

/-- **The hitting time is measurable.** -/
theorem measurable_tauG (ha : 0 < a) (θ : E → ℝ) : Measurable (tauG P a δ L θ) := by
  classical
  refine measurable_to_countable' fun n => ?_
  induction n using ENat.recTopCoe with
  | top =>
      have : tauG P a δ L θ ⁻¹' {⊤} = ⋂ t, {ω | stopAt P a δ t (runG P L θ t ω)}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
          Set.mem_setOf_eq]
        unfold tauG
        exact hitTime_eq_top_iff
      rw [this]
      exact MeasurableSet.iInter fun t => (measurableSet_stopG P a δ L ha θ t).compl
  | coe k =>
      have : tauG P a δ L θ ⁻¹' {(k : ℕ∞)} = {ω | stopAt P a δ k (runG P L θ k ω)} ∩
          ⋂ j ∈ Finset.range k, {ω | stopAt P a δ j (runG P L θ j ω)}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
        unfold tauG
        constructor
        · intro h
          obtain ⟨hk, hlow⟩ := hitTime_eq_coe h
          exact ⟨hk, fun j hj => hlow j hj⟩
        · rintro ⟨hk, hlow⟩
          have hex : ∃ n, stopAt P a δ n (runG P L θ n ω) := ⟨k, hk⟩
          rw [hitTime_eq_find hex]
          have : Nat.find hex = k := by
            apply le_antisymm (Nat.find_min' hex hk)
            by_contra hlt
            exact hlow _ (not_le.mp hlt) (Nat.find_spec hex)
          rw [this]
      rw [this]
      exact (measurableSet_stopG P a δ L ha θ k).inter
        (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
          (measurableSet_stopG P a δ L ha θ j).compl)

theorem tauG_eq_coe (θ : E → ℝ) (ω : ℕ → ℝ) {k : ℕ} (hk : tauG P a δ L θ ω = k) :
    stopAt P a δ k (runG P L θ k ω) ∧ ∀ s < k, ¬ stopAt P a δ s (runG P L θ s ω) := by
  classical
  unfold tauG at hk
  exact hitTime_eq_coe hk

theorem before_tauG (θ : E → ℝ) (ω : ℕ → ℝ) (m : ℕ) (hm : (m : ℕ∞) ≤ tauG P a δ L θ ω) :
    ∀ s < m, ¬ stopAt P a δ s (runG P L θ s ω) := by
  classical
  intro s hs
  have hlt : (s : ℕ∞) < tauG P a δ L θ ω := lt_of_lt_of_le (by exact_mod_cast hs) hm
  unfold tauG at hlt
  exact (lt_hitTime_iff s).mp hlt s le_rfl

/-! ## 2. Delta-correctness, for every allocation rule -/

/-- **Stopping with `T0` has probability at most `delta` in every world of `Alt T0`.** -/
theorem wrong_answer_leG (ha : 0 < a) (hδ : 0 < δ) (θ : E → ℝ) (T0 : Ans) (hθ : θ ∈ P.Alt T0) :
    streamMeasure {ω | ∃ t, stopAt P a δ t (runG P L θ t ω) ∧ answerAt P a (runG P L θ t ω) = T0}
      ≤ ENNReal.ofReal δ := by
  set Z : ℕ → (ℕ → ℝ) → ℝ := fun j ω => Zh P a T0 (runG P L θ j ω) with hZ
  have hZle : ∀ j ω, Z j ω ≤ PaperA7Stream.Qstat a P.σ (Nc L θ P.σ j ω) (muHat L θ P.σ j ω) θ := by
    intro j ω
    show glr a P.σ (P.Alt T0) (hN (runG P L θ j ω), hMu (runG P L θ j ω)) ≤ _
    rw [hN_runG, hMu_runG, (glr_run_measurable L θ P.σ a ha
      (fun e => (P.σ_pos e).ne') (P.Alt T0) (P.Alt_ne T0) j).2 ω]
    exact sInf_le_truth θ P.σ a ha (P.Alt T0) hθ _ _ fun e => Nat.cast_nonneg _
  have hsub : {ω | ∃ t, stopAt P a δ t (runG P L θ t ω) ∧ answerAt P a (runG P L θ t ω) = T0}
      ⊆ {ω | ∃ j, bthr a δ (Nc L θ P.σ j ω) < Z j ω} := by
    rintro ω ⟨t, ⟨-, T, hT⟩, hans⟩
    refine ⟨t, ?_⟩
    have hmax := answerAt_spec P a (runG P L θ t ω) T
    rw [hans] at hmax
    rw [← hN_runG]
    exact lt_of_lt_of_le hT hmax
  exact le_trans (measure_mono hsub)
    (wrong_stop_ever_le L θ P.σ a δ ha hδ P.σ_pos Z hZle)

/-- **A wrong answer has probability at most `(|Ans| - 1) delta`.** -/
theorem correctG (ha : 0 < a) (hδ : 0 < δ) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) :
    streamMeasure {ω | ∃ t, stopAt P a δ t (runG P L θ t ω) ∧ answerAt P a (runG P L θ t ω) ≠ Tst}
      ≤ ((Fintype.card Ans - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal δ := by
  have hsub : {ω | ∃ t, stopAt P a δ t (runG P L θ t ω) ∧ answerAt P a (runG P L θ t ω) ≠ Tst}
      ⊆ ⋃ T ∈ (univ.erase Tst : Finset Ans),
          {ω | ∃ t, stopAt P a δ t (runG P L θ t ω) ∧ answerAt P a (runG P L θ t ω) = T} := by
    rintro ω ⟨t, hs, hne⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨_, hne, t, hs, rfl⟩
  refine le_trans (measure_mono hsub) (le_trans (measure_biUnion_finset_le _ _) ?_)
  refine le_trans (sum_le_sum fun T hT =>
    wrong_answer_leG P a δ L ha hδ θ T (hwrong T (mem_erase.mp hT).1)) (le_of_eq ?_)
  rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul]

/-! ## 3. The stopped policy and its coupling -/

open Classical in
/-- **The stopped policy**: `L` on the projected history until the stop has fired, the fresh
dummy from then on. -/
noncomputable def stoppedG (ha : 0 < a) : Learner (E ⊕ Unit) where
  rule t h := if fired P a δ t h then dummyQ else Sum.inl (L.rule t (prH h))
  meas t := by
    refine Measurable.ite (measurableSet_setOfPred.mpr (measurable_fired P a δ ha t))
      measurable_const ?_
    exact measurable_inl.comp ((L.meas t).comp (measurable_prH t))

theorem fired_liftHG (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    fired P a δ t (liftH (runG P L θ t ω)) ↔ ∃ s ≤ t, stopAt P a δ s (runG P L θ s ω) := by
  unfold fired
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, Nat.lt_succ_iff.mp s.2, ?_⟩
    rwa [restr_prH, prH_liftH, restr_runG] at hs
  · rintro ⟨s, hst, hs⟩
    refine ⟨⟨s, Nat.lt_succ_of_le hst⟩, ?_⟩
    rw [restr_prH, prH_liftH, restr_runG]
    exact hs

theorem rule_liftHG (ha : 0 < a) (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ)
    (hno : ∀ s ≤ t, ¬ stopAt P a δ s (runG P L θ s ω)) :
    (stoppedG P a δ L ha).rule t (liftH (runG P L θ t ω))
      = Sum.inl (L.rule t (runG P L θ t ω)) := by
  classical
  show (if fired P a δ t (liftH (runG P L θ t ω)) then (dummyQ : E ⊕ Unit) else
    Sum.inl (L.rule t (prH (liftH (runG P L θ t ω))))) = _
  rw [if_neg (fun h => by
    obtain ⟨s, hs, h'⟩ := (fired_liftHG P a δ L θ t ω).mp h
    exact hno s hs h'), prH_liftH]

/-- The stopped policy's history in the lifted world. -/
noncomputable def runSG (ha : 0 < a) (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    Fin t → (E ⊕ Unit) × ℝ :=
  histF (stoppedG P a δ L ha) (lift θ) (liftS P.σ) t (Xp t ω)

theorem measurable_runSG (ha : 0 < a) (θ : E → ℝ) (t : ℕ) :
    Measurable (runSG P a δ L ha θ t) :=
  (measurable_histF _ _ _ t).comp (measurable_Xp t)

/-- **The coupling.** -/
theorem runSG_eq (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (m : ℕ)
    (hm : ∀ s < m, ¬ stopAt P a δ s (runG P L θ s ω)) :
    runSG P a δ L ha θ m ω = liftH (runG P L θ m ω) :=
  histF_lift L (stoppedG P a δ L ha) θ P.σ ω m fun t ht =>
    rule_liftHG P a δ L ha θ t ω fun s hs => hm s (by omega)

theorem restr_runSG (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    restr m hm (runSG P a δ L ha θ n ω) = runSG P a δ L ha θ m ω := by
  unfold runSG
  rw [histF_restr]
  rfl

theorem prH_runSG (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n m : ℕ) (hmn : m ≤ n)
    (hm : (m : ℕ∞) ≤ tauG P a δ L θ ω) :
    prH (restr m hmn (runSG P a δ L ha θ n ω)) = runG P L θ m ω := by
  rw [restr_runSG, runSG_eq P a δ L ha θ ω m (before_tauG P a δ L θ ω m hm), prH_liftH]

theorem first_le_tauG (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n t : ℕ) (htn : t ≤ n)
    (hfirst : ∀ s (hs : s ≤ n), s < t →
      ¬ stopAt P a δ s (prH (restr s hs (runSG P a δ L ha θ n ω)))) :
    (t : ℕ∞) ≤ tauG P a δ L θ ω := by
  by_contra hc
  push Not at hc
  have hne : tauG P a δ L θ ω ≠ ⊤ := ne_top_of_lt hc
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hkt : k < t := by rw [← hk] at hc; exact_mod_cast hc
  have hstop := (tauG_eq_coe P a δ L θ ω hk.symm).1
  refine hfirst k (by omega) hkt ?_
  rw [prH_runSG P a δ L ha θ ω n k (by omega) hk.le]
  exact hstop

/-- After the stopping time the stopped policy queries the dummy. -/
theorem query_dummyG (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (i k : ℕ)
    (hk : tauG P a δ L θ ω = k) (hki : k ≤ i) :
    (stoppedG P a δ L ha).rule i (runSG P a δ L ha θ i ω) = dummyQ := by
  classical
  have hfired : fired P a δ i (runSG P a δ L ha θ i ω) := by
    refine ⟨⟨k, Nat.lt_succ_of_le hki⟩, ?_⟩
    rw [prH_runSG P a δ L ha θ ω i k hki hk.symm.le]
    exact (tauG_eq_coe P a δ L θ ω hk).1
  show (if fired P a δ i (runSG P a δ L ha θ i ω) then (dummyQ : E ⊕ Unit) else _) = dummyQ
  rw [if_pos hfired]

/-! ## 4. The stopped counts are the run's counts at `min(n, tau)` -/

theorem cntQ_snoc (q : E ⊕ Unit) (n : ℕ) (h : Fin n → (E ⊕ Unit) × ℝ) (x : (E ⊕ Unit) × ℝ) :
    cntQ q (n + 1) (Fin.snoc (α := fun _ => (E ⊕ Unit) × ℝ) h x)
      = cntQ q n h + if x.1 = q then 1 else 0 := by
  unfold cntQ
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem cntQ_runSG_succ (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n : ℕ) (q : E ⊕ Unit) :
    cntQ q (n + 1) (runSG P a δ L ha θ (n + 1) ω)
      = cntQ q n (runSG P a δ L ha θ n ω)
        + if (stoppedG P a δ L ha).rule n (runSG P a δ L ha θ n ω) = q then 1 else 0 := by
  unfold runSG
  rw [Xp_succ, histF_snoc, cntQ_snoc]

/-- **The count identity.**  For every horizon `n` there is one `m <= n`, with `m <= tau`,
at which every real cell's stopped count equals the run's count. -/
theorem cnt_eq_at_min (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) :
    ∀ n : ℕ, ∃ m : ℕ, m ≤ n ∧ (m : ℕ∞) ≤ tauG P a δ L θ ω ∧ (m < n → tauG P a δ L θ ω = m) ∧
      ∀ e, cntQ (Sum.inl e) n (runSG P a δ L ha θ n ω)
        = ENNReal.ofReal (Nc L θ P.σ m ω e)
  | 0 => ⟨0, le_rfl, by simp, fun h => absurd h (lt_irrefl 0), fun e => by
      rw [Nc_zeroG]; simp [cntQ]⟩
  | n + 1 => by
      obtain ⟨m, hmn, hmτ, hlt, hcnt⟩ := cnt_eq_at_min ha θ ω n
      rcases lt_or_eq_of_le hmn with hm | hm
      · -- already stopped at `m < n`: the dummy is queried
        have hτ := hlt hm
        refine ⟨m, by omega, hmτ, fun _ => hτ, fun e => ?_⟩
        rw [cntQ_runSG_succ, query_dummyG P a δ L ha θ ω n m hτ hm.le, hcnt e]
        simp [dummyQ]
      · subst hm
        by_cases hlt' : (m : ℕ∞) < tauG P a δ L θ ω
        · -- still running: the query is the run's
          have hno : ∀ s ≤ m, ¬ stopAt P a δ s (runG P L θ s ω) := fun s hs =>
            (before_tauG P a δ L θ ω (m + 1)
              (by exact Order.add_one_le_of_lt hlt') s (by omega))
          have hcpl := runSG_eq P a δ L ha θ ω m fun s hs => hno s hs.le
          have hrule := rule_liftHG P a δ L ha θ m ω hno
          refine ⟨m + 1, le_rfl, Order.add_one_le_of_lt hlt', fun h => absurd h (lt_irrefl _),
            fun e => ?_⟩
          rw [cntQ_runSG_succ, hcnt e, hcpl, hrule, Nc_succG]
          by_cases he : e = L.rule m (runG P L θ m ω)
          · rw [if_pos (by rw [he]), if_pos he,
              ENNReal.ofReal_add (by unfold Nc; exact Nat.cast_nonneg _) zero_le_one,
              ENNReal.ofReal_one]
          · rw [if_neg (fun h => he (Sum.inl_injective h).symm), if_neg he, add_zero, add_zero]
        · -- stops exactly now
          have hτ : tauG P a δ L θ ω = m := le_antisymm (not_lt.mp hlt') hmτ
          refine ⟨m, by omega, hmτ, fun _ => hτ, fun e => ?_⟩
          rw [cntQ_runSG_succ, query_dummyG P a δ L ha θ ω m m hτ le_rfl, hcnt e]
          simp [dummyQ]

/-! ## 5. The answer event -/

theorem ansEv_subG (ha : 0 < a) (θ : E → ℝ) (Tst : Ans) (n : ℕ) (ω : ℕ → ℝ)
    (hω : runSG P a δ L ha θ n ω ∈ ansEv P a δ Tst n) :
    ∃ t, stopAt P a δ t (runG P L θ t ω) ∧
      ∀ T, Zh P a T (runG P L θ t ω) ≤ Zh P a Tst (runG P L θ t ω) := by
  obtain ⟨t, hfirst, hstop, hmax⟩ := hω
  have htn : (t : ℕ) ≤ n := Nat.lt_succ_iff.mp t.2
  have hle : ((t : ℕ) : ℕ∞) ≤ tauG P a δ L θ ω :=
    first_le_tauG P a δ L ha θ ω n t htn fun s hs hst =>
      hfirst ⟨s, Nat.lt_succ_of_le hs⟩ (Fin.mk_lt_mk.mpr hst)
  rw [prH_runSG P a δ L ha θ ω n t htn hle] at hstop hmax
  exact ⟨t, hstop, hmax⟩

/-- **In every world of `Alt Tst`, the answer event has probability at most `delta`.** -/
theorem ansEv_alt_leG (ha : 0 < a) (hδ : 0 < δ) (Tst : Ans) (lam : E → ℝ)
    (hlam : lam ∈ P.Alt Tst) (n : ℕ) :
    streamMeasure {ω | runSG P a δ L ha lam n ω ∈ ansEv P a δ Tst n} ≤ ENNReal.ofReal δ := by
  set Z : ℕ → (ℕ → ℝ) → ℝ := fun j ω => Zh P a Tst (runG P L lam j ω) with hZ
  have hZle : ∀ j ω, Z j ω ≤ PaperA7Stream.Qstat a P.σ (Nc L lam P.σ j ω)
      (muHat L lam P.σ j ω) lam := by
    intro j ω
    show glr a P.σ (P.Alt Tst) (hN (runG P L lam j ω), hMu (runG P L lam j ω)) ≤ _
    rw [hN_runG, hMu_runG, (glr_run_measurable L lam P.σ a ha
      (fun e => (P.σ_pos e).ne') (P.Alt Tst) (P.Alt_ne Tst) j).2 ω]
    exact sInf_le_truth lam P.σ a ha (P.Alt Tst) hlam _ _ fun e => Nat.cast_nonneg _
  have hsub : {ω | runSG P a δ L ha lam n ω ∈ ansEv P a δ Tst n}
      ⊆ {ω | ∃ j, bthr a δ (Nc L lam P.σ j ω) < Z j ω} := by
    intro ω hω
    obtain ⟨t, ⟨-, T, hT⟩, hmax⟩ := ansEv_subG P a δ L ha lam Tst n ω hω
    refine ⟨t, ?_⟩
    rw [← hN_runG]
    exact lt_of_lt_of_le hT (hmax T)
  exact le_trans (measure_mono hsub)
    (wrong_stop_ever_le L lam P.σ a δ ha hδ P.σ_pos Z hZle)

/-- **In a world whose answer is `Tst`, the answer event has probability at least
`1 - (|Ans| - 1) delta - P(tau > n)`.** -/
theorem ansEv_true_geG (ha : 0 < a) (hδ : 0 < δ) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (n : ℕ) :
    1 - (Fintype.card Ans - 1 : ℕ) * δ - streamMeasure.real {ω | (n : ℕ∞) < tauG P a δ L θ ω}
      ≤ streamMeasure.real {ω | runSG P a δ L ha θ n ω ∈ ansEv P a δ Tst n} := by
  classical
  set A := {ω | runSG P a δ L ha θ n ω ∈ ansEv P a δ Tst n} with hA
  set B := {ω | (n : ℕ∞) < tauG P a δ L θ ω} with hB
  set W := {ω | ∃ t, stopAt P a δ t (runG P L θ t ω) ∧ answerAt P a (runG P L θ t ω) ≠ Tst}
    with hW
  have hAm : MeasurableSet A :=
    (measurable_runSG P a δ L ha θ n) (measurableSet_ansEv P a δ ha Tst n)
  have hcompl : Aᶜ ⊆ B ∪ W := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨hnB, hnW⟩ := hc
    have hτ : tauG P a δ L θ ω ≤ n := not_lt.mp hnB
    have hne : tauG P a δ L θ ω ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hτ
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    have hkn : k ≤ n := by rw [← hk] at hτ; exact_mod_cast hτ
    obtain ⟨hstop, hbefore⟩ := tauG_eq_coe P a δ L θ ω hk.symm
    have hans : answerAt P a (runG P L θ k ω) = Tst := by
      by_contra hne'
      exact hnW ⟨k, hstop, hne'⟩
    apply hω
    refine ⟨⟨k, Nat.lt_succ_of_le hkn⟩, fun s hs => ?_, ?_, fun T => ?_⟩
    · have hsk : (s : ℕ) < k := hs
      rw [prH_runSG P a δ L ha θ ω n s (by omega) (by rw [← hk]; exact_mod_cast hsk.le)]
      exact hbefore s hsk
    · rw [prH_runSG P a δ L ha θ ω n k hkn hk.le]
      exact hstop
    · rw [prH_runSG P a δ L ha θ ω n k hkn hk.le, ← hans]
      exact answerAt_spec P a _ T
  have hWle : streamMeasure.real W ≤ (Fintype.card Ans - 1 : ℕ) * δ := by
    have h := correctG P a δ L ha hδ Tst θ hwrong
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hδ.le] at h2
  have hc1 : streamMeasure.real Aᶜ ≤ streamMeasure.real B + streamMeasure.real W :=
    le_trans (measureReal_mono hcompl (measure_ne_top _ _)) (measureReal_union_le _ _)
  have hc2 : streamMeasure.real Aᶜ = 1 - streamMeasure.real A := probReal_compl_eq_one_sub hAm
  linarith

#print axioms measurable_tauG
#print axioms correctG
#print axioms runSG_eq
#print axioms cnt_eq_at_min
#print axioms ansEv_alt_leG
#print axioms ansEv_true_geG

end CIGAMF.P13.PaperA7StoppedGen
