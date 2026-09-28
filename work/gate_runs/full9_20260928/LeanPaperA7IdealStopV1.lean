import «LeanPaperA7IdealLearnerV1»
import «LeanPaperA7GLRMeasV1»
import «LeanPaperAStoppingV1»

/-!
# Paper A7: the ideal learner's stopping rule, its hitting time, and delta-correctness

The stopping rule reads the observed history only:

* `Zh T h` -- the EXACT generalized-likelihood statistic of answer `T`, the infimum over the
  whole alternative `Alt T` of the code's ridge statistic at the history's counts and means
  (`glr`, `LeanPaperA7GLRMeasV1`);
* `stopAt t h` -- after the warm start, some answer's statistic exceeds the code's threshold
  `bthr(a, delta, N)`;
* `answerAt t h` -- the answer with the largest statistic (first maximiser);
* `tauI` -- the `ℕ∞`-valued hitting time of `stopAt` along the run in world `theta`; it is
  measurable (`measurable_tauI`).

`wrong_answer_le`: in any world `theta` that lies in `Alt T0` (so `T0` is wrong there), the
probability of ever stopping with answer `T0` is at most `delta`.  The proof is Ville's
inequality for the actual run (`wrong_stop_ever_le`, `LeanPaperA7CorrectV1`): stopping with
`T0` forces `bthr < Zh T0`, and the infimum over `Alt T0` is at most the statistic at the true
world.
-/

namespace CIGAMF.P13.PaperA7IdealStop

open Finset MeasureTheory
open scoped ENNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process CIGAMF.P13.PaperA7Confidence
open CIGAMF.P13.PaperA7Correct CIGAMF.P13.PaperA7GLRMeas CIGAMF.P13.PaperA7IdealLearner
open CIGAMF.P13.PaperAStopping CIGAMF.P13.PaperA7NetOracle

variable {E : Type*} [Fintype E] [DecidableEq E] [MeasurableSpace E] [MeasurableSingletonClass E]
  [Nonempty E]
variable {Ans : Type*} [Fintype Ans] [DecidableEq Ans] [Nonempty Ans]
variable (P : Spec E Ans) (a δ : ℝ)

/-! ## 1. The statistic and the rule, on the history -/

/-- The exact statistic of answer `T` on a history. -/
noncomputable def Zh (T : Ans) {t : ℕ} (h : Fin t → E × ℝ) : ℝ :=
  glr a P.σ (P.Alt T) (hN h, hMu h)

theorem measurable_Zh (ha : 0 < a) (T : Ans) (t : ℕ) :
    Measurable fun h : Fin t → E × ℝ => Zh P a T h :=
  (measurable_glr a ha P.σ (fun e => (P.σ_pos e).ne') (P.Alt T) (P.Alt_ne T)).comp
    ((measurable_pi_lambda _ fun e => measurable_hN t e).prodMk (measurable_hMu t))

/-- The stopping condition. -/
def stopAt (t : ℕ) (h : Fin t → E × ℝ) : Prop :=
  Fintype.card E ≤ t ∧ ∃ T : Ans, bthr a δ (hN h) < Zh P a T h

/-- The answer: the first maximiser of the statistics. -/
noncomputable def answerIdx {t : ℕ} (h : Fin t → E × ℝ) : Fin (Fintype.card Ans) :=
  argmaxIdx Fintype.card_pos (fun i (_ : E → ℝ) => Zh P a ((Fintype.equivFin Ans).symm i) h)
    (fun _ => 0)

noncomputable def answerAt {t : ℕ} (h : Fin t → E × ℝ) : Ans :=
  (Fintype.equivFin Ans).symm (answerIdx P a h)

theorem answerAt_spec {t : ℕ} (h : Fin t → E × ℝ) (T : Ans) :
    Zh P a T h ≤ Zh P a (answerAt P a h) h := by
  have hs := argmaxIdx_spec (Fintype.card_pos (α := Ans))
    (fun i (_ : E → ℝ) => Zh P a ((Fintype.equivFin Ans).symm i) h)
    (fun _ => 0) (Fintype.equivFin Ans T)
  rw [Equiv.symm_apply_apply] at hs
  exact hs

/-! ## 2. Along the run -/

/-- The observed history of `t` rounds in world `theta`. -/
noncomputable def runH (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) : Fin t → E × ℝ :=
  histF (idealLearner P) θ P.σ t (Xp t ω)

theorem measurable_runH (θ : E → ℝ) (t : ℕ) : Measurable (runH P θ t) :=
  (measurable_histF (idealLearner P) θ P.σ t).comp (measurable_Xp t)

theorem hN_runH (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    hN (runH P θ t ω) = Nc (idealLearner P) θ P.σ t ω := by
  funext e
  unfold hN runH Nc NF
  push_cast
  rfl

theorem hMu_runH (θ : E → ℝ) (t : ℕ) (ω : ℕ → ℝ) :
    hMu (runH P θ t ω) = muHat (idealLearner P) θ P.σ t ω := by
  funext e
  unfold hMu muHat
  rw [hN_runH]
  rfl

/-- **The hitting time.** -/
noncomputable def tauI (θ : E → ℝ) (ω : ℕ → ℝ) : ℕ∞ := by
  classical
  exact hitTime fun t => stopAt P a δ t (runH P θ t ω)

theorem measurableSet_stop (ha : 0 < a) (θ : E → ℝ) (t : ℕ) :
    MeasurableSet {ω | stopAt P a δ t (runH P θ t ω)} := by
  unfold stopAt
  by_cases hK : Fintype.card E ≤ t
  · simp only [hK, true_and]
    have : {ω | ∃ T : Ans, bthr a δ (hN (runH P θ t ω)) < Zh P a T (runH P θ t ω)}
        = ⋃ T : Ans, {ω | bthr a δ (hN (runH P θ t ω)) < Zh P a T (runH P θ t ω)} := by
      ext ω; simp
    rw [this]
    refine MeasurableSet.iUnion fun T => measurableSet_lt ?_ ?_
    · rw [show (fun ω => bthr a δ (hN (runH P θ t ω)))
          = fun ω => bthr a δ (Nc (idealLearner P) θ P.σ t ω) from
          funext fun ω => by rw [hN_runH]]
      exact measurable_bthr (idealLearner P) θ P.σ a δ t
    · exact (measurable_Zh P a ha T t).comp (measurable_runH P θ t)
  · simp only [hK, false_and, Set.setOf_false]
    exact MeasurableSet.empty

/-- **The hitting time is measurable.** -/
theorem measurable_tauI (ha : 0 < a) (θ : E → ℝ) : Measurable (tauI P a δ θ) := by
  classical
  refine measurable_to_countable' fun n => ?_
  induction n using ENat.recTopCoe with
  | top =>
      have : tauI P a δ θ ⁻¹' {⊤} = ⋂ t, {ω | stopAt P a δ t (runH P θ t ω)}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_compl_iff,
          Set.mem_setOf_eq]
        unfold tauI
        exact hitTime_eq_top_iff
      rw [this]
      exact MeasurableSet.iInter fun t => (measurableSet_stop P a δ ha θ t).compl
  | coe k =>
      have : tauI P a δ θ ⁻¹' {(k : ℕ∞)} = {ω | stopAt P a δ k (runH P θ k ω)} ∩
          ⋂ j ∈ Finset.range k, {ω | stopAt P a δ j (runH P θ j ω)}ᶜ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
          Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
        unfold tauI
        constructor
        · intro h
          have hex : ∃ n, stopAt P a δ n (runH P θ n ω) := by
            by_contra hne
            push Not at hne
            rw [(hitTime_eq_top_iff).mpr hne] at h
            exact ENat.top_ne_coe k h
          rw [hitTime_eq_find hex] at h
          have hk : Nat.find hex = k := by exact_mod_cast h
          refine ⟨hk ▸ Nat.find_spec hex, fun j hj => ?_⟩
          exact Nat.find_min hex (hk ▸ hj)
        · rintro ⟨hk, hlow⟩
          have hex : ∃ n, stopAt P a δ n (runH P θ n ω) := ⟨k, hk⟩
          rw [hitTime_eq_find hex]
          have : Nat.find hex = k := by
            apply le_antisymm (Nat.find_min' hex hk)
            by_contra hlt
            exact hlow _ (not_le.mp hlt) (Nat.find_spec hex)
          rw [this]
      rw [this]
      exact (measurableSet_stop P a δ ha θ k).inter
        (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
          (measurableSet_stop P a δ ha θ j).compl)

/-! ## 3. Delta-correctness -/

/-- **Stopping with a wrong answer has probability at most `delta`.** -/
theorem wrong_answer_le (ha : 0 < a) (hδ : 0 < δ) (θ : E → ℝ) (T0 : Ans) (hθ : θ ∈ P.Alt T0) :
    streamMeasure {ω | ∃ t, stopAt P a δ t (runH P θ t ω) ∧ answerAt P a (runH P θ t ω) = T0}
      ≤ ENNReal.ofReal δ := by
  set Z : ℕ → (ℕ → ℝ) → ℝ := fun j ω => Zh P a T0 (runH P θ j ω) with hZ
  have hZle : ∀ j ω, Z j ω ≤ PaperA7Stream.Qstat a P.σ (Nc (idealLearner P) θ P.σ j ω)
      (muHat (idealLearner P) θ P.σ j ω) θ := by
    intro j ω
    show glr a P.σ (P.Alt T0) (hN (runH P θ j ω), hMu (runH P θ j ω)) ≤ _
    rw [hN_runH, hMu_runH, (glr_run_measurable (idealLearner P) θ P.σ a ha
      (fun e => (P.σ_pos e).ne') (P.Alt T0) (P.Alt_ne T0) j).2 ω]
    exact sInf_le_truth θ P.σ a ha (P.Alt T0) hθ _ _ fun e => Nat.cast_nonneg _
  have hsub : {ω | ∃ t, stopAt P a δ t (runH P θ t ω) ∧ answerAt P a (runH P θ t ω) = T0}
      ⊆ {ω | ∃ j, bthr a δ (Nc (idealLearner P) θ P.σ j ω) < Z j ω} := by
    rintro ω ⟨t, ⟨-, T, hT⟩, hans⟩
    refine ⟨t, ?_⟩
    have hmax := answerAt_spec P a (runH P θ t ω) T
    rw [hans] at hmax
    rw [← hN_runH]
    exact lt_of_lt_of_le hT hmax
  exact le_trans (measure_mono hsub)
    (wrong_stop_ever_le (idealLearner P) θ P.σ a δ ha hδ P.σ_pos Z hZle)

#print axioms measurable_Zh
#print axioms measurable_tauI
#print axioms wrong_answer_le

end CIGAMF.P13.PaperA7IdealStop
