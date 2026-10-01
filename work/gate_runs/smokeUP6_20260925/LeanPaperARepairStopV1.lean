import «LeanPaperARepairBridgeV1»
import «LeanPaperBStoppedLawV1»

/-!
# Paper A: the budget law at the stopping time, for policies that stop almost surely

The budget classes of `LeanPaperAPolicyClassesV1` are stated at a horizon. A policy with an
unbounded stopping time is naturally constrained at its stop, and meeting the budget at the stop
says nothing about a truncation: a policy may break the budget early and repair it before it
stops. So the law is not obtained by asking every truncation to meet the budget. It is obtained
from the change of measure alone, which needs no budget at all.

* `trunc_event`: at a horizon where at most `ε` of the true world's runs are unstopped, the event
  "stopped with answer `a`" has probability at least `1 - δ - ε` at `θ`.
* `stopped_info`: for every alternative `λ` of `L`,
  `(1-δ) log(1/δ) - log 2 ≤ Σ_q N_q KL_q(θ,λ)`, where `N_q` are the expected counts of the whole
  run (the supremum over horizons). Finiteness is asked of the informative queries only: after
  the stop the dummy is queried forever, so its count is infinite, and its divergence is zero. The truncations' counts are at most `N_q`, and the unstopped
  mass tends to zero.
* `stopped_budget_law`: hence, if the whole run's expected design meets the budget, then
  `(1-δ) log(1/δ) - log 2 ≤ E|N(τ)| · R` for every `R` bounding the true game within the budget
  on the simplex; with `R = R(b)` this is the repair law at the stop, at level `δ` itself.
* The hypotheses are satisfiable: `LeanPaperARepairGaussV1.stopped_law_satisfiable` embeds the
  stopped fixed-design learner, at a Markov horizon, as a stopping policy that meets all of them.
-/

namespace CIGAMF.P13.PaperARepairStop

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperALowerKL CIGAMF.P13.PaperALowerGame
open CIGAMF.P13.PaperASacrificeDuality CIGAMF.P13.PaperARepairLaw CIGAMF.P13.PaperAFamilyLower
open CIGAMF.P13.PaperARepairBridge CIGAMF.P13.PaperBStoppedLaw

variable {W Q A : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q] [Fintype Q] [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The event "stopped within `n` rounds with answer `a`". -/
def stopAns (S : SPolicy Q A) (a0 a : A) (n : ℕ) : Set (Hist Q n) :=
  {x | fired S n x ∧ outT S S.out a0 n x = a}

theorem measurableSet_stopAns (S : SPolicy Q A) (a0 a : A) (n : ℕ) :
    MeasurableSet (stopAns S a0 a n) :=
  (measurableSet_fired S n).inter
    (measurable_outT S S.out S.out_meas a0 n (measurableSet_singleton a))

/-- The whole run's expected count of a query: the supremum over horizons. -/
noncomputable def cntSt (C : Channel W Q) (S : SPolicy Q A) (θ : W) (q : Q) : ℝ≥0∞ :=
  ⨆ n, ∫⁻ x, cntQ q n x ∂hist C (stoppedPol S C.dummy) θ n

theorem ecnt_le_St (C : Channel W Q) (S : SPolicy Q A) (θ : W) (n : ℕ) (q : Q)
    (hfin : cntSt C S θ q ≠ ⊤) :
    ecnt C (stoppedPol S C.dummy) θ n q ≤ (cntSt C S θ q).toReal := by
  unfold ecnt
  exact ENNReal.toReal_mono hfin (le_iSup (fun k => ∫⁻ x, cntQ q k x
    ∂hist C (stoppedPol S C.dummy) θ k) n)

/-- **The answer event of a truncation.** -/
theorem trunc_event (C : Channel W Q) (S : SPolicy Q A) (θ : W) (a0 a : A) (δ ε : ℝ) (n : ℕ)
    (hunst : (hist C (stoppedPol S C.dummy) θ n).real {x | ¬ fired S n x} ≤ ε)
    (herr : (hist C (stoppedPol S C.dummy) θ n).real {x | fired S n x ∧ outT S S.out a0 n x ≠ a}
      ≤ δ) :
    1 - δ - ε ≤ (hist C (stoppedPol S C.dummy) θ n).real (stopAns S a0 a n) := by
  haveI := hist_prob C (stoppedPol S C.dummy) θ n
  set μ := hist C (stoppedPol S C.dummy) θ n
  have hm := measurableSet_stopAns S a0 a n
  have hsub : (stopAns S a0 a n)ᶜ
      ⊆ {x | fired S n x ∧ outT S S.out a0 n x ≠ a} ∪ {x | ¬ fired S n x} := by
    intro x hx
    simp only [stopAns, Set.mem_compl_iff, Set.mem_setOf_eq, not_and] at hx
    by_cases hf : fired S n x
    · exact Or.inl ⟨hf, hx hf⟩
    · exact Or.inr hf
  have h1 : μ.real (stopAns S a0 a n)ᶜ ≤ δ + ε :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (by linarith))
  rw [measureReal_compl hm, probReal_univ] at h1
  linarith

/-- **The change of measure for the whole run.** -/
theorem stopped_info (C : Channel W Q) (S : SPolicy Q A) (θ l : W) (a0 a : A) (δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstop : ∀ ε : ℝ, 0 < ε → ∃ n,
      (hist C (stoppedPol S C.dummy) θ n).real {x | ¬ fired S n x} ≤ ε)
    (herr : ∀ n, (hist C (stoppedPol S C.dummy) θ n).real
      {x | fired S n x ∧ outT S S.out a0 n x ≠ a} ≤ δ)
    (halt : ∀ n, (hist C (stoppedPol S C.dummy) l n).real (stopAns S a0 a n) ≤ δ)
    (hfinKL : ∀ q, klq C θ l q ≠ ⊤) (hfin : ∀ q, q ≠ C.dummy → cntSt C S θ q ≠ ⊤) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2
      ≤ ∑ q, (cntSt C S θ q).toReal * (klq C θ l q).toReal := by
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- a horizon with small unstopped mass
  obtain ⟨n, hn⟩ := hstop (ε / (Real.log (1 / δ) + 1)) (by positivity)
  have hp := trunc_event C S θ a0 a δ _ n hn (herr n)
  have hinfo := event_info C (stoppedPol S C.dummy) n θ l (stopAns S a0 a n)
    (measurableSet_stopAns S a0 a n) δ hδ (halt n) hfinKL
  have hmono : ∑ q, ecnt C (stoppedPol S C.dummy) θ n q * (klq C θ l q).toReal
      ≤ ∑ q, (cntSt C S θ q).toReal * (klq C θ l q).toReal :=
    Finset.sum_le_sum fun q _ => by
      by_cases hq : q = C.dummy
      · subst hq; rw [klq_dummy]; simp
      · exact mul_le_mul_of_nonneg_right (ecnt_le_St C S θ n q (hfin q hq)) ENNReal.toReal_nonneg
  have hL1 : 0 < Real.log (1 / δ) + 1 := by linarith
  have hkey : (1 - δ) * Real.log (1 / δ)
      ≤ (1 - δ - ε / (Real.log (1 / δ) + 1)) * Real.log (1 / δ) + ε := by
    have : ε / (Real.log (1 / δ) + 1) * Real.log (1 / δ) ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hL1]; nlinarith
    nlinarith
  have hp' := mul_le_mul_of_nonneg_right hp hlog
  linarith

/-- The whole run's informative total and expected design. -/
noncomputable def etotSt (C : Channel W Q) (S : SPolicy Q A) (θ : W) : ℝ :=
  ∑ q, (cntSt C S θ q).toReal * (if q = C.dummy then 0 else 1)

noncomputable def ebarSt (C : Channel W Q) (S : SPolicy Q A) (θ : W) (q : Q) : ℝ :=
  (cntSt C S θ q).toReal * (if q = C.dummy then 0 else 1) / etotSt C S θ

theorem ebarSt_alloc (C : Channel W Q) (S : SPolicy Q A) (θ : W) (hpos : 0 < etotSt C S θ) :
    IsAllocG (ebarSt C S θ) := by
  refine ⟨fun q => div_nonneg (mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num))
    hpos.le, ?_⟩
  have e : ∑ q, (cntSt C S θ q).toReal * (if q = C.dummy then 0 else 1) = etotSt C S θ := rfl
  unfold ebarSt
  rw [← Finset.sum_div, e, div_self hpos.ne']

theorem etotSt_mul_infoAt (C : Channel W Q) (S : SPolicy Q A) (θ l : W)
    (hpos : 0 < etotSt C S θ) :
    etotSt C S θ * infoAt C θ l (ebarSt C S θ)
      = ∑ q, (cntSt C S θ q).toReal * (klq C θ l q).toReal := by
  unfold infoAt ebarSt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q = C.dummy
  · subst hq; rw [klq_dummy C θ l]; simp
  · simp only [hq, if_false, mul_one]; field_simp

/-- **The repair law at the stopping time.**  A policy that stops almost surely at `θ`, answers
`a` wrongly at `θ` with probability at most `δ` and answers `a` at every alternative of `L` with
probability at most `δ` on its stopped runs, and whose whole-run expected design meets the budget,
pays `(1-δ) log(1/δ) - log 2 ≤ E|N(τ)| · R`. -/
theorem stopped_budget_law (C : Channel W Q) (S : SPolicy Q A) (θ : W) (L : Set W) [Nonempty L]
    (a0 a : A) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hstop : ∀ ε : ℝ, 0 < ε → ∃ n,
      (hist C (stoppedPol S C.dummy) θ n).real {x | ¬ fired S n x} ≤ ε)
    (herr : ∀ n, (hist C (stoppedPol S C.dummy) θ n).real
      {x | fired S n x ∧ outT S S.out a0 n x ≠ a} ≤ δ)
    (halt : ∀ l ∈ L, ∀ n, (hist C (stoppedPol S C.dummy) l n).real (stopAns S a0 a n) ≤ δ)
    (hfinKL : ∀ l ∈ L, ∀ q, klq C θ l q ≠ ⊤) (hfin : ∀ q, q ≠ C.dummy → cntSt C S θ q ≠ ⊤)
    (hpos : 0 < etotSt C S θ)
    (s : (Q → ℝ) → ℝ) (b R : ℝ) (hR : ∀ w : Q → ℝ, IsAllocG w → s w ≤ b → Jt C θ L w ≤ R)
    (hbud : s (ebarSt C S θ) ≤ b) :
    (1 - δ) * Real.log (1 / δ) - Real.log 2 ≤ etotSt C S θ * R := by
  have hper : ∀ l : L, ((1 - δ) * Real.log (1 / δ) - Real.log 2) / etotSt C S θ
      ≤ infoAt C θ l (ebarSt C S θ) := by
    intro l
    rw [div_le_iff₀ hpos]
    have h1 := etotSt_mul_infoAt C S θ l hpos
    have h2 := stopped_info C S θ l a0 a δ hδ hδ1 hstop herr (halt l l.2) (hfinKL l l.2) hfin
    linarith [mul_comm (etotSt C S θ) (infoAt C θ l (ebarSt C S θ))]
  have hJ : ((1 - δ) * Real.log (1 / δ) - Real.log 2) / etotSt C S θ
      ≤ Jt C θ L (ebarSt C S θ) := le_ciInf hper
  rw [div_le_iff₀ hpos] at hJ
  have hRb := hR _ (ebarSt_alloc C S θ hpos) hbud
  nlinarith [mul_le_mul_of_nonneg_left hRb hpos.le]


/-! ## A finite-horizon policy is a stopping policy that meets the hypotheses -/

section Finite

variable (C : Channel W Q) (pol0 : Policy Q) (N : ℕ)

open Classical in
/-- The indicator of an event, as a Boolean answer. -/
noncomputable def indAns (E0 : Set (Hist Q N)) : Hist Q N → Bool :=
  fun x => if x ∈ E0 then true else false

theorem measurable_indAns (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0) :
    Measurable (indAns N E0) := by
  classical
  unfold indAns
  exact Measurable.ite hE0 measurable_const measurable_const

theorem indAns_true (E0 : Set (Hist Q N)) (x : Hist Q N) : indAns N E0 x = true ↔ x ∈ E0 := by
  classical
  unfold indAns; split_ifs with h <;> simp [h]

/-- The embedded stopping policy: run `pol0` for `N` rounds, stop, answer the indicator. -/
noncomputable def finStop (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0) : SPolicy Q Bool :=
  ofFinite pol0 N (indAns N E0) (measurable_indAns N E0 hE0)

theorem hist_finStop_N (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0) (w : W) :
    hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) w N = hist C pol0 w N :=
  hist_congr C _ _ w N fun k hk => step_ofFinite_lt pol0 N _ _ C.dummy k hk

/-- After the horizon, an event of the first `N` rounds keeps its probability. -/
theorem finStop_restr (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0) (w : W) (k : ℕ)
    (B : Set (Hist Q N)) (hB : MeasurableSet B) :
    (hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) w (N + k)).real
      (hRestr N (Nat.le_add_right N k) ⁻¹' B) = (hist C pol0 w N).real B := by
  rw [← map_measureReal_apply (measurable_hRestr N (Nat.le_add_right N k)) hB,
    hist_map_restr, hist_finStop_N]

/-- The per-query expected count of the embedded policy is constant after the horizon. -/
theorem finStop_cnt_after (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0) (w : W) (q : Q)
    (hq : q ≠ C.dummy) :
    ∀ k, ∫⁻ x, cntQ q (N + k) x ∂hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) w (N + k)
      = ∫⁻ x, cntQ q N x ∂hist C pol0 w N
  | 0 => by rw [Nat.add_zero, hist_finStop_N]
  | k + 1 => by
      rw [← finStop_cnt_after E0 hE0 w q hq k]
      have hc : ∀ n (x : Hist Q n), cntQ q n x = qsum (fun q' => if q' = q then 1 else 0) n x :=
        fun n x => rfl
      simp_rw [hc]
      rw [show N + (k + 1) = (N + k) + 1 by ring, lintegral_qsum_succ]
      haveI := hist_prob C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) w (N + k)
      have hstep := step_ofFinite_ge pol0 N (indAns N E0) (measurable_indAns N E0 hE0) C.dummy
        (N + k) (Nat.le_add_right _ _)
      have hzero : ∫⁻ x, (fun q' : Q => if q' = q then (1 : ℝ≥0∞) else 0) x.2
          ∂((hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) w (N + k))
            ⊗ₘ (stoppedPol (finStop pol0 N E0 hE0) C.dummy).step (N + k)) = 0 := by
        rw [show (stoppedPol (finStop pol0 N E0 hE0) C.dummy).step (N + k)
            = Kernel.const _ (Measure.dirac C.dummy) from hstep, Measure.compProd_const]
        have hind : (fun x : Hist Q (N + k) × Q => (fun q' : Q => if q' = q then (1 : ℝ≥0∞) else 0) x.2)
            = Set.indicator (Set.univ ×ˢ {q}) 1 := by
          funext x
          by_cases h : x.2 = q <;> simp [Set.indicator, h]
        rw [hind, lintegral_indicator_one (MeasurableSet.univ.prod (MeasurableSet.of_discrete)),
          Measure.prod_prod, Measure.dirac_apply' _ MeasurableSet.of_discrete]
        simp [Ne.symm hq]
      rw [hzero, add_zero]

theorem cnt_mono (w : W) (q : Q) (n : ℕ) :
    ∀ j, ∫⁻ x, cntQ q n x ∂hist C pol0 w n ≤ ∫⁻ x, cntQ q (n + j) x ∂hist C pol0 w (n + j)
  | 0 => le_rfl
  | j + 1 => by
      refine (cnt_mono w q n j).trans ?_
      have hc : ∀ n (x : Hist Q n), cntQ q n x = qsum (fun q' => if q' = q then 1 else 0) n x :=
        fun n x => rfl
      simp_rw [hc]
      rw [show n + (j + 1) = (n + j) + 1 by ring, lintegral_qsum_succ]
      exact le_self_add

theorem finStop_cnt_before (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0) (w : W) (q : Q)
    (n : ℕ) (hn : n ≤ N) :
    ∫⁻ x, cntQ q n x ∂hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) w n
      ≤ ∫⁻ x, cntQ q N x ∂hist C pol0 w N := by
  rw [hist_congr C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) pol0 w n
    fun k hk => step_ofFinite_lt pol0 N _ _ C.dummy k (by omega)]
  have h := cnt_mono C pol0 w q n (N - n)
  rwa [show n + (N - n) = N by omega] at h

/-- **The whole-run counts of the embedded policy are its counts at the horizon.** -/
theorem finStop_cntSt (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0) (w : W) (q : Q)
    (hq : q ≠ C.dummy) :
    cntSt C (finStop pol0 N E0 hE0) w q = ∫⁻ x, cntQ q N x ∂hist C pol0 w N := by
  unfold cntSt
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rcases le_total n N with h | h
    · exact finStop_cnt_before C pol0 N E0 hE0 w q n h
    · obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
      exact le_of_eq (finStop_cnt_after C pol0 N E0 hE0 w q hq k)
  · refine le_trans (le_of_eq (finStop_cnt_after C pol0 N E0 hE0 w q hq 0).symm) ?_
    exact le_iSup (fun n => ∫⁻ x, cntQ q n x
      ∂hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) w n) (N + 0)

/-- **A correct finite-horizon policy meets every hypothesis of the stopped law**, with the
whole-run counts equal to its counts at the horizon. -/
theorem finStop_hyps (θ : W) (L : Set W) (E0 : Set (Hist Q N)) (hE0 : MeasurableSet E0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hθ : 1 - δ ≤ (hist C pol0 θ N).real E0)
    (hL : ∀ l ∈ L, (hist C pol0 l N).real E0 ≤ δ) :
    (∀ ε : ℝ, 0 < ε → ∃ n,
      (hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) θ n).real
        {x | ¬ fired (finStop pol0 N E0 hE0) n x} ≤ ε)
    ∧ (∀ n, (hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) θ n).real
        {x | fired (finStop pol0 N E0 hE0) n x
          ∧ outT (finStop pol0 N E0 hE0) (finStop pol0 N E0 hE0).out false n x ≠ true} ≤ δ)
    ∧ (∀ l ∈ L, ∀ n, (hist C (stoppedPol (finStop pol0 N E0 hE0) C.dummy) l n).real
        (stopAns (finStop pol0 N E0 hE0) false true n) ≤ δ)
    ∧ (∀ q, q ≠ C.dummy → cntSt C (finStop pol0 N E0 hE0) θ q ≠ ⊤) := by
  set S := finStop pol0 N E0 hE0 with hSdef
  have hfired : ∀ n (x : Hist Q n), fired S n x ↔ N ≤ n :=
    fun n x => fired_ofFinite pol0 N _ _ n x
  refine ⟨fun ε hε => ⟨N, ?_⟩, fun n => ?_, fun l hl n => ?_, fun q hq => ?_⟩
  · have : {x : Hist Q N | ¬ fired S N x} = ∅ := by
      ext x; simp [hfired N x]
    rw [this]; simp; exact hε.le
  · rcases lt_or_ge n N with hn | hn
    · have : {x : Hist Q n | fired S n x ∧ outT S S.out false n x ≠ true} = ∅ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hf; exact absurd ((hfired n x).mp hf) (by omega)
      rw [this]; simp; exact hδ
    · obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
      have hset : {x : Hist Q (N + k) | fired S (N + k) x ∧ outT S S.out false (N + k) x ≠ true}
          = hRestr N (Nat.le_add_right N k) ⁻¹' E0ᶜ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff]
        rw [show outT S S.out false (N + k) x = indAns N E0 (hRestr N (Nat.le_add_right N k) x)
          from outT_ofFinite pol0 N (indAns N E0) (measurable_indAns N E0 hE0) false (N + k)
            (Nat.le_add_right N k) x, Ne, indAns_true]
        exact ⟨fun h => h.2, fun h => ⟨(hfired _ x).mpr (Nat.le_add_right N k), h⟩⟩
      rw [hset, finStop_restr C pol0 N E0 hE0 θ k _ hE0.compl]
      haveI := hist_prob C pol0 θ N
      rw [measureReal_compl hE0, probReal_univ]
      linarith
  · rcases lt_or_ge n N with hn | hn
    · have : stopAns S false true n = ∅ := by
        ext x; simp only [stopAns, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hf; exact absurd ((hfired n x).mp hf) (by omega)
      rw [this]; simp; exact hδ
    · obtain ⟨k, rfl⟩ : ∃ k, n = N + k := ⟨n - N, by omega⟩
      have hset : stopAns S false true (N + k) = hRestr N (Nat.le_add_right N k) ⁻¹' E0 := by
        ext x
        simp only [stopAns, Set.mem_setOf_eq, Set.mem_preimage]
        rw [show outT S S.out false (N + k) x = indAns N E0 (hRestr N (Nat.le_add_right N k) x)
          from outT_ofFinite pol0 N (indAns N E0) (measurable_indAns N E0 hE0) false (N + k)
            (Nat.le_add_right N k) x, indAns_true]
        exact ⟨fun h => h.2, fun h => ⟨(hfired _ x).mpr (Nat.le_add_right N k), h⟩⟩
      rw [hset, finStop_restr C pol0 N E0 hE0 l k _ hE0]
      exact hL l hl
  · rw [finStop_cntSt C pol0 N E0 hE0 θ q hq]
    exact lintegral_cntQ_ne_top C pol0 θ q N

end Finite

#print axioms trunc_event
#print axioms stopped_info
#print axioms ebarSt_alloc
#print axioms stopped_budget_law
#print axioms finStop_cntSt
#print axioms finStop_hyps

end CIGAMF.P13.PaperARepairStop
