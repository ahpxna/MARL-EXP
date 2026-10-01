import «LeanPaperA7IdealUpperV1»
import «LeanPaperABridgeDummyV1»
import «LeanPaperALowerKLV1»

/-!
# Paper A7: the ideal learner, stopped, as a policy of the kernel protocol

The lower bound of Paper A is proved for policies of the kernel protocol with a finite horizon
(`family_policy_lower`), whose query type carries a FRESH dummy `Sum.inr ()`
(`LeanPaperABridgeDummyV1`).  To apply it to the ideal learner:

* `stoppedLearner` -- the learner on `E ⊕ Unit` that runs the ideal learner on the (projected)
  history until the ideal stopping rule has fired, and queries the dummy from then on.  It is a
  measurable deterministic rule; it uses no parameter of the world.
* `runS_eq` -- **the coupling**: on the same innovation stream, up to the stopping time, the
  stopped learner's history in the lifted world `lift theta` IS the lifted history of the ideal
  learner in `theta` (noise `liftS sigma`, unit noise on the dummy);
* `cnt_le_tau` -- pathwise, the number of real-cell queries within any horizon `n` is at most
  the stopping time `tauI`;
* `ansEv` -- the answer event at horizon `n` (the projected history stops for the first time at
  some `t <= n`, with `Tst` a maximiser of the statistics), a measurable set of histories;
* `ansEv_alt_le` -- in every world of `Alt Tst`, the event has probability at most `delta`;
* `ansEv_true_ge` -- in a world whose answer is `Tst`, it has probability at least
  `1 - (|Ans| - 1) delta - P(tau > n)`.
-/

namespace CIGAMF.P13.PaperA7IdealStopped

open Finset MeasureTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7IdealLearner CIGAMF.P13.PaperA7IdealStop
open CIGAMF.P13.PaperA7IdealRun CIGAMF.P13.PaperA7IdealUpper CIGAMF.P13.PaperAStopping
open CIGAMF.P13.PaperABridgeDummy CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperA7GLRMeas

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]

/-! ## 1. Lifting and projecting histories -/

/-- The noise on the extended query type (the dummy has unit noise). -/
def liftS (σ : E → ℝ) : E ⊕ Unit → ℝ := Sum.elim σ (fun _ => 1)

theorem liftS_pos (σ : E → ℝ) (hσ : ∀ e, 0 < σ e) : ∀ q, 0 < liftS σ q
  | Sum.inl e => hσ e
  | Sum.inr _ => one_pos

/-- A history on the real cells, as a history on the extended query type. -/
def liftH {t : ℕ} (h : Fin t → E × ℝ) : Fin t → (E ⊕ Unit) × ℝ :=
  fun i => (Sum.inl (h i).1, (h i).2)

/-- One entry projected back to the real cells (the dummy goes to a fixed cell). -/
noncomputable def prE (x : (E ⊕ Unit) × ℝ) : E × ℝ :=
  (Sum.elim id (fun _ => Classical.arbitrary E) x.1, x.2)

noncomputable def prH {t : ℕ} (h : Fin t → (E ⊕ Unit) × ℝ) : Fin t → E × ℝ :=
  fun i => prE (h i)

theorem prH_liftH {t : ℕ} (h : Fin t → E × ℝ) : prH (liftH h) = h := by
  funext i; rfl

theorem measurable_prE : Measurable (prE (E := E)) :=
  ((measurable_of_countable _).comp measurable_fst).prodMk measurable_snd

theorem measurable_prH (t : ℕ) : Measurable (prH (E := E) (t := t)) :=
  measurable_pi_lambda _ fun i => measurable_prE.comp (measurable_pi_apply i)

theorem measurable_restr {α : Type*} [MeasurableSpace α] {t : ℕ} (s : ℕ) (hs : s ≤ t) :
    Measurable fun h : Fin t → α => (fun i : Fin s => h (Fin.castLE hs i)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem restr_prH {t : ℕ} (s : ℕ) (hs : s ≤ t) (h : Fin t → (E ⊕ Unit) × ℝ) :
    prH (restr s hs h) = restr s hs (prH h) := rfl

/-! ## 2. The stopped learner -/

variable (P : Spec E Ans) (a δ : ℝ)

/-- The stopping rule has fired at some time `s <= t` of the projected history. -/
def fired (t : ℕ) (h : Fin t → (E ⊕ Unit) × ℝ) : Prop :=
  ∃ s : Fin (t + 1), stopAt P a δ s (prH (restr s (Nat.lt_succ_iff.mp s.2) h))

theorem measurable_stopH (ha : 0 < a) (t : ℕ) :
    Measurable fun h : Fin t → E × ℝ => stopAt P a δ t h := by
  unfold stopAt
  refine Measurable.and measurable_const (Measurable.exists fun T => ?_)
  refine measurableSet_setOfPred.mp (measurableSet_lt ?_ (measurable_Zh P a ha T t))
  unfold bthr
  exact measurable_const.add ((Finset.measurable_sum _ fun e _ =>
    Real.measurable_log.comp (measurable_const.add ((measurable_hN t e).div_const a))).div_const 2)

theorem measurable_fired (ha : 0 < a) (t : ℕ) :
    Measurable fun h : Fin t → (E ⊕ Unit) × ℝ => fired P a δ t h := by
  unfold fired
  exact Measurable.exists fun s => (measurable_stopH P a δ ha s).comp
    ((measurable_prH (s : ℕ)).comp (measurable_restr _ _))

open Classical in
/-- **The stopped learner**: the ideal learner on the projected history until the stopping rule
has fired, the fresh dummy from then on. -/
noncomputable def stoppedLearner (ha : 0 < a) : Learner (E ⊕ Unit) where
  rule t h := if fired P a δ t h then dummyQ else Sum.inl ((idealLearner P).rule t (prH h))
  meas t := by
    refine Measurable.ite (measurableSet_setOfPred.mpr (measurable_fired P a δ ha t))
      measurable_const ?_
    exact measurable_inl.comp (((idealLearner P).meas t).comp (measurable_prH t))

/-! ## 3. The coupling -/

theorem histF_lift (L1 : Learner E) (L2 : Learner (E ⊕ Unit)) (θ σ : E → ℝ) (ω : ℕ → ℝ) :
    ∀ m : ℕ, (∀ t < m, L2.rule t (liftH (histF L1 θ σ t (Xp t ω)))
        = Sum.inl (L1.rule t (histF L1 θ σ t (Xp t ω)))) →
      histF L2 (lift θ) (liftS σ) m (Xp m ω) = liftH (histF L1 θ σ m (Xp m ω))
  | 0, _ => by funext i; exact i.elim0
  | m + 1, hyp => by
      have ih := histF_lift L1 L2 θ σ ω m fun t ht => hyp t (by omega)
      rw [Xp_succ, histF_snoc, histF_snoc, ih, hyp m (by omega)]
      funext i
      cases i using Fin.lastCases with
      | last => simp [liftH, lift, liftS]
      | cast j => simp [liftH]

theorem fired_liftH (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    fired P a δ t (liftH (runH P θ t ω)) ↔ ∃ s ≤ t, stopAt P a δ s (runH P θ s ω) := by
  unfold fired
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, Nat.lt_succ_iff.mp s.2, ?_⟩
    rwa [restr_prH, prH_liftH, restr_runH] at hs
  · rintro ⟨s, hst, hs⟩
    refine ⟨⟨s, Nat.lt_succ_of_le hst⟩, ?_⟩
    rw [restr_prH, prH_liftH, restr_runH]
    exact hs

theorem rule_liftH (ha : 0 < a) (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ)
    (hno : ∀ s ≤ t, ¬ stopAt P a δ s (runH P θ s ω)) :
    (stoppedLearner P a δ ha).rule t (liftH (runH P θ t ω))
      = Sum.inl ((idealLearner P).rule t (runH P θ t ω)) := by
  classical
  show (if fired P a δ t (liftH (runH P θ t ω)) then (dummyQ : E ⊕ Unit) else
    Sum.inl ((idealLearner P).rule t (prH (liftH (runH P θ t ω))))) = _
  rw [if_neg (fun h => by
    obtain ⟨s, hs, h'⟩ := (fired_liftH P a δ θ t ω).mp h
    exact hno s hs h'), prH_liftH]

/-- The stopped learner's history in the lifted world. -/
noncomputable def runS (ha : 0 < a) (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    Fin t → (E ⊕ Unit) × ℝ :=
  histF (stoppedLearner P a δ ha) (lift θ) (liftS P.σ) t (Xp t ω)

theorem measurable_runS (ha : 0 < a) (θ : E → ℝ) (t : ℕ) :
    Measurable (runS P a δ ha θ t) :=
  (measurable_histF _ _ _ t).comp (measurable_Xp t)

/-- **The coupling.** -/
theorem runS_eq (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (m : ℕ)
    (hm : ∀ s < m, ¬ stopAt P a δ s (runH P θ s ω)) :
    runS P a δ ha θ m ω = liftH (runH P θ m ω) :=
  histF_lift (idealLearner P) (stoppedLearner P a δ ha) θ P.σ ω m fun t ht =>
    rule_liftH P a δ ha θ t ω fun s hs => hm s (by omega)

theorem restr_runS (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n m : ℕ) (hm : m ≤ n) :
    restr m hm (runS P a δ ha θ n ω) = runS P a δ ha θ m ω := by
  unfold runS
  rw [histF_restr]
  rfl

/-! ## 4. The stopping time on the path -/

theorem hitTime_eq_coe {p : ℕ → Prop} [DecidablePred p] {k : ℕ} (h : hitTime p = k) :
    p k ∧ ∀ s < k, ¬ p s := by
  have hex : ∃ n, p n := by
    by_contra hne
    push_neg at hne
    rw [(hitTime_eq_top_iff (p := p)).mpr hne] at h
    simp at h
  rw [hitTime_eq_find hex] at h
  have hk : Nat.find hex = k := by exact_mod_cast h
  subst hk
  exact ⟨Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩

theorem tauI_eq_coe (θ : E → ℝ) (ω : ℕ → ℝ) {k : ℕ} (hk : tauI P a δ θ ω = k) :
    stopAt P a δ k (runH P θ k ω) ∧ ∀ s < k, ¬ stopAt P a δ s (runH P θ s ω) := by
  classical
  unfold tauI at hk
  exact hitTime_eq_coe hk

theorem before_tauI (θ : E → ℝ) (ω : ℕ → ℝ) (m : ℕ) (hm : (m : ℕ∞) ≤ tauI P a δ θ ω) :
    ∀ s < m, ¬ stopAt P a δ s (runH P θ s ω) := by
  classical
  intro s hs
  have hlt : (s : ℕ∞) < tauI P a δ θ ω := lt_of_lt_of_le (by exact_mod_cast hs) hm
  unfold tauI at hlt
  exact (lt_hitTime_iff s).mp hlt s le_rfl

/-- Up to the stopping time, the projected stopped history is the ideal learner's. -/
theorem prH_runS (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n m : ℕ) (hmn : m ≤ n)
    (hm : (m : ℕ∞) ≤ tauI P a δ θ ω) :
    prH (restr m hmn (runS P a δ ha θ n ω)) = runH P θ m ω := by
  rw [restr_runS, runS_eq P a δ ha θ ω m (before_tauI P a δ θ ω m hm), prH_liftH]

/-- The first stopping time of the projected stopped history is at most `tauI`. -/
theorem first_le_tauI (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n t : ℕ) (htn : t ≤ n)
    (hfirst : ∀ s (hs : s ≤ n), s < t →
      ¬ stopAt P a δ s (prH (restr s hs (runS P a δ ha θ n ω)))) :
    (t : ℕ∞) ≤ tauI P a δ θ ω := by
  by_contra hc
  push_neg at hc
  have hne : tauI P a δ θ ω ≠ ⊤ := ne_top_of_lt hc
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  have hkt : k < t := by rw [← hk] at hc; exact_mod_cast hc
  have hstop := (tauI_eq_coe P a δ θ ω hk.symm).1
  refine hfirst k (by omega) hkt ?_
  rw [prH_runS P a δ ha θ ω n k (by omega) hk.le]
  exact hstop

/-! ## 5. The count of real-cell queries -/

theorem histF_query (L : Learner (E ⊕ Unit)) (m s : E ⊕ Unit → ℝ) (n : ℕ)
    (ω : ℕ → ℝ) (i : Fin n) :
    (histF L m s n (Xp n ω) i).1 = L.rule i (histF L m s i (Xp i ω)) := by
  have h2 := congrArg Prod.fst (congrFun (histF_restr L m s n (i + 1) i.2 (Xp n ω)) (Fin.last i))
  unfold restr at h2
  rw [show Fin.castLE i.2 (Fin.last (i : ℕ)) = i from Fin.ext rfl] at h2
  rw [h2]
  simp only [histF, Fin.snoc_last]
  rfl

theorem query_dummy (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n : ℕ) (i : Fin n) (k : ℕ)
    (hk : tauI P a δ θ ω = k) (hki : k ≤ i) :
    (runS P a δ ha θ n ω i).1 = dummyQ := by
  classical
  unfold runS
  rw [histF_query]
  have hfired : fired P a δ i (runS P a δ ha θ i ω) := by
    refine ⟨⟨k, Nat.lt_succ_of_le hki⟩, ?_⟩
    rw [prH_runS P a δ ha θ ω i k hki hk.symm.le]
    exact (tauI_eq_coe P a δ θ ω hk).1
  show (if fired P a δ i (runS P a δ ha θ i ω) then (dummyQ : E ⊕ Unit) else _) = dummyQ
  rw [if_pos hfired]

theorem card_filter_lt_le (n k : ℕ) :
    ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i.val < k)).card ≤ k := by
  calc ((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i.val < k)).card
      ≤ (Finset.range k).card := by
        refine Finset.card_le_card_of_injOn (fun i : Fin n => i.val) (fun i hi => ?_) ?_
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hi
          simpa using hi
        · intro i _ j _ h
          exact Fin.ext h
    _ = k := Finset.card_range k

theorem sum_ite_inl_le (x : E ⊕ Unit) :
    ∑ e : E, (if x = Sum.inl e then (1 : ℝ≥0∞) else 0) ≤ 1 := by
  cases x with
  | inl e0 => simp
  | inr u => simp

/-- **Pathwise, the real-cell queries within any horizon number at most `tauI`.** -/
theorem cnt_le_tau (ha : 0 < a) (θ : E → ℝ) (ω : ℕ → ℝ) (n : ℕ) :
    ∑ e : E, cntQ (Sum.inl e) n (runS P a δ ha θ n ω) ≤ (tauI P a δ θ ω).toENNReal := by
  classical
  by_cases htop : tauI P a δ θ ω = ⊤
  · rw [htop]; simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hk]
  simp only [ENat.toENNReal_coe]
  unfold cntQ
  rw [Finset.sum_comm]
  calc ∑ i : Fin n, ∑ e : E,
        (if (runS P a δ ha θ n ω i).1 = Sum.inl e then (1 : ℝ≥0∞) else 0)
      ≤ ∑ i : Fin n, (if i.val < k then (1 : ℝ≥0∞) else 0) := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hik : i.val < k
        · rw [if_pos hik]; exact sum_ite_inl_le _
        · rw [if_neg hik, query_dummy P a δ ha θ ω n i k hk.symm (by omega)]
          simp [dummyQ]
    _ = (((Finset.univ : Finset (Fin n)).filter (fun i : Fin n => i.val < k)).card : ℝ≥0∞) := by
        rw [Finset.sum_boole]
    _ ≤ k := by exact_mod_cast card_filter_lt_le n k

/-! ## 6. The answer event -/

/-- The answer event at horizon `n`: the projected history stops for the FIRST time at some
`t <= n`, with `Tst` a maximiser of the statistics there. -/
def ansEv (Tst : Ans) (n : ℕ) : Set (Fin n → (E ⊕ Unit) × ℝ) :=
  {h | ∃ t : Fin (n + 1),
    (∀ s : Fin (n + 1), s < t →
      ¬ stopAt P a δ s (prH (restr s (Nat.lt_succ_iff.mp s.2) h))) ∧
    stopAt P a δ t (prH (restr t (Nat.lt_succ_iff.mp t.2) h)) ∧
    ∀ T, Zh P a T (prH (restr t (Nat.lt_succ_iff.mp t.2) h))
      ≤ Zh P a Tst (prH (restr t (Nat.lt_succ_iff.mp t.2) h))}

theorem measurableSet_ansEv (ha : 0 < a) (Tst : Ans) (n : ℕ) :
    MeasurableSet (ansEv P a δ Tst n) := by
  unfold ansEv
  refine measurableSet_setOfPred.mpr (Measurable.exists fun t => ?_)
  have hG : ∀ s : Fin (n + 1), Measurable fun h : Fin n → (E ⊕ Unit) × ℝ =>
      prH (restr s (Nat.lt_succ_iff.mp s.2) h) :=
    fun s => (measurable_prH (s : ℕ)).comp (measurable_restr _ _)
  refine Measurable.and (Measurable.forall fun s => Measurable.imp measurable_const
    ((measurable_stopH P a δ ha s).comp (hG s)).not) (Measurable.and
      ((measurable_stopH P a δ ha t).comp (hG t)) (Measurable.forall fun T => ?_))
  exact measurableSet_setOfPred.mp (measurableSet_le ((measurable_Zh P a ha T t).comp (hG t))
    ((measurable_Zh P a ha Tst t).comp (hG t)))

/-- On the answer event, the ideal learner itself stopped with `Tst` a maximiser. -/
theorem ansEv_sub (ha : 0 < a) (θ : E → ℝ) (Tst : Ans) (n : ℕ) (ω : ℕ → ℝ)
    (hω : runS P a δ ha θ n ω ∈ ansEv P a δ Tst n) :
    ∃ t, stopAt P a δ t (runH P θ t ω) ∧
      ∀ T, Zh P a T (runH P θ t ω) ≤ Zh P a Tst (runH P θ t ω) := by
  obtain ⟨t, hfirst, hstop, hmax⟩ := hω
  have htn : (t : ℕ) ≤ n := Nat.lt_succ_iff.mp t.2
  have hle : ((t : ℕ) : ℕ∞) ≤ tauI P a δ θ ω :=
    first_le_tauI P a δ ha θ ω n t htn fun s hs hst =>
      hfirst ⟨s, Nat.lt_succ_of_le hs⟩ (Fin.mk_lt_mk.mpr hst)
  rw [prH_runS P a δ ha θ ω n t htn hle] at hstop hmax
  exact ⟨t, hstop, hmax⟩

/-- **In every world of `Alt Tst`, the answer event has probability at most `delta`.** -/
theorem ansEv_alt_le (ha : 0 < a) (hδ : 0 < δ) (Tst : Ans) (lam : E → ℝ)
    (hlam : lam ∈ P.Alt Tst) (n : ℕ) :
    streamMeasure {ω | runS P a δ ha lam n ω ∈ ansEv P a δ Tst n} ≤ ENNReal.ofReal δ := by
  set Z : ℕ → (ℕ → ℝ) → ℝ := fun j ω => Zh P a Tst (runH P lam j ω) with hZ
  have hZle : ∀ j ω, Z j ω ≤ PaperA7Stream.Qstat a P.σ (Nc (idealLearner P) lam P.σ j ω)
      (muHat (idealLearner P) lam P.σ j ω) lam := by
    intro j ω
    show glr a P.σ (P.Alt Tst) (hN (runH P lam j ω), hMu (runH P lam j ω)) ≤ _
    rw [hN_runH, hMu_runH, (glr_run_measurable (idealLearner P) lam P.σ a ha
      (fun e => (P.σ_pos e).ne') (P.Alt Tst) (P.Alt_ne Tst) j).2 ω]
    exact sInf_le_truth lam P.σ a ha (P.Alt Tst) hlam _ _ fun e => Nat.cast_nonneg _
  have hsub : {ω | runS P a δ ha lam n ω ∈ ansEv P a δ Tst n}
      ⊆ {ω | ∃ j, bthr a δ (Nc (idealLearner P) lam P.σ j ω) < Z j ω} := by
    intro ω hω
    obtain ⟨t, ⟨-, T, hT⟩, hmax⟩ := ansEv_sub P a δ ha lam Tst n ω hω
    refine ⟨t, ?_⟩
    rw [← hN_runH]
    exact lt_of_lt_of_le hT (hmax T)
  exact le_trans (measure_mono hsub)
    (wrong_stop_ever_le (idealLearner P) lam P.σ a δ ha hδ P.σ_pos Z hZle)

/-- **In a world whose answer is `Tst`, the answer event has probability at least
`1 - (|Ans| - 1) delta - P(tau > n)`.** -/
theorem ansEv_true_ge (ha : 0 < a) (hδ : 0 < δ) (Tst : Ans) (θ : E → ℝ)
    (hwrong : ∀ T, T ≠ Tst → θ ∈ P.Alt T) (n : ℕ) :
    1 - (Fintype.card Ans - 1 : ℕ) * δ - streamMeasure.real {ω | (n : ℕ∞) < tauI P a δ θ ω}
      ≤ streamMeasure.real {ω | runS P a δ ha θ n ω ∈ ansEv P a δ Tst n} := by
  classical
  set A := {ω | runS P a δ ha θ n ω ∈ ansEv P a δ Tst n} with hA
  set B := {ω | (n : ℕ∞) < tauI P a δ θ ω} with hB
  set W := {ω | ∃ t, stopAt P a δ t (runH P θ t ω) ∧ answerAt P a (runH P θ t ω) ≠ Tst} with hW
  have hAm : MeasurableSet A :=
    (measurable_runS P a δ ha θ n) (measurableSet_ansEv P a δ ha Tst n)
  have hcompl : Aᶜ ⊆ B ∪ W := by
    intro ω hω
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨hnB, hnW⟩ := hc
    have hτ : tauI P a δ θ ω ≤ n := not_lt.mp hnB
    have hne : tauI P a δ θ ω ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top n) hτ
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
    have hkn : k ≤ n := by rw [← hk] at hτ; exact_mod_cast hτ
    obtain ⟨hstop, hbefore⟩ := tauI_eq_coe P a δ θ ω hk.symm
    have hans : answerAt P a (runH P θ k ω) = Tst := by
      by_contra hne'
      exact hnW ⟨k, hstop, hne'⟩
    apply hω
    refine ⟨⟨k, Nat.lt_succ_of_le hkn⟩, fun s hs => ?_, ?_, fun T => ?_⟩
    · have hsk : (s : ℕ) < k := hs
      rw [prH_runS P a δ ha θ ω n s (by omega) (by rw [← hk]; exact_mod_cast hsk.le)]
      exact hbefore s hsk
    · rw [prH_runS P a δ ha θ ω n k hkn hk.le]
      exact hstop
    · rw [prH_runS P a δ ha θ ω n k hkn hk.le, ← hans]
      exact answerAt_spec P a _ T
  have hWle : streamMeasure.real W ≤ (Fintype.card Ans - 1 : ℕ) * δ := by
    have h := ideal_correct P a ha δ hδ Tst θ hwrong
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      ENNReal.ofReal_ne_top) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hδ.le] at h2
  have hc1 : streamMeasure.real Aᶜ ≤ streamMeasure.real B + streamMeasure.real W :=
    le_trans (measureReal_mono hcompl (measure_ne_top _ _)) (measureReal_union_le _ _)
  have hc2 : streamMeasure.real Aᶜ = 1 - streamMeasure.real A := probReal_compl_eq_one_sub hAm
  linarith

#print axioms runS_eq
#print axioms cnt_le_tau
#print axioms measurableSet_ansEv
#print axioms ansEv_alt_le
#print axioms ansEv_true_ge

end CIGAMF.P13.PaperA7IdealStopped
