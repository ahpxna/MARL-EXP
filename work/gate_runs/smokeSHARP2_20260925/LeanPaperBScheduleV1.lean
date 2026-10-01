import «LeanPaperBProtocolV1»

/-!
# Paper B: policies that follow a fixed schedule

A decoder with a fixed budget asks a PREDETERMINED sequence of queries: round `n` issues
`sched n` whatever has been observed.  In the protocol of `LeanPaperBProtocolV1` such a policy is
the deterministic kernel `schedPolicy sched`.  Two facts are needed about it:

* `hist_sched_ae` -- almost surely the recorded query at every round IS the scheduled one.  This
  is proved along the recursion, not assumed, so the decoder may read its test statistics off the
  history's recorded queries and the counts are exactly the scheduled ones;
* `tauN_sched_ae` -- almost surely its cost is the number of non-dummy entries of the schedule,
  so `costN` is that number exactly (`costN_sched`).
-/

namespace CIGAMF.P13.PaperBSchedule

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol

variable {W Q : Type*} [MeasurableSpace Q] [DiscreteMeasurableSpace Q] [Countable Q]
  [DecidableEq Q]

/-- The policy that issues `sched n` at round `n`. -/
noncomputable def schedPolicy (sched : ℕ → Q) : Policy Q where
  step n := Kernel.deterministic (fun _ => sched n) measurable_const
  markov n := inferInstance

/-- The set of histories whose recorded queries follow the schedule. -/
def onSched (sched : ℕ → Q) (n : ℕ) : Set (Hist Q n) := {ω | ∀ i : Fin n, (ω i).1 = sched i}

theorem measurableSet_onSched (sched : ℕ → Q) (n : ℕ) :
    MeasurableSet (onSched sched n) := by
  have : onSched sched n = ⋂ i : Fin n, {ω : Hist Q n | (ω i).1 = sched i} := by
    ext ω; simp [onSched]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurable_fst.comp (measurable_pi_apply i)) (measurableSet_singleton _)

theorem snoc_onSched (sched : ℕ → Q) (n : ℕ) (p : (Hist Q n × Q) × ℝ) :
    snocMap n p ∈ onSched sched (n + 1) ↔ p.1.1 ∈ onSched sched n ∧ p.1.2 = sched n := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · have := h i.castSucc
      simpa [snocMap] using this
    · have := h (Fin.last n)
      simpa [snocMap] using this
  · rintro ⟨h1, h2⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [snocMap] using h2
    · simpa [snocMap] using h1 j

/-- A property of the first coordinate that holds almost surely under `mu` holds almost surely
under `mu ⊗ₘ kappa`. -/
theorem compProd_null_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] (S : Set α)
    (hS : MeasurableSet S) (h0 : μ S = 0) : (μ ⊗ₘ κ) (Prod.fst ⁻¹' S) = 0 := by
  rw [Measure.compProd_apply (measurable_fst hS)]
  refine (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left
    (measurable_fst hS))).mpr ?_
  refine (ae_iff.mpr ?_)
  refine measure_mono_null (fun x hx => ?_) h0
  by_contra hxS
  apply hx
  have : (Prod.mk x : β → α × β) ⁻¹' (Prod.fst ⁻¹' S) = (∅ : Set β) := by
    ext y; simp [hxS]
  simp [this]

/-- **Almost surely the recorded queries follow the schedule.** -/
theorem hist_sched_null (C : Channel W Q) (sched : ℕ → Q) (w : W) :
    ∀ n, hist C (schedPolicy sched) w n (onSched sched n)ᶜ = 0
  | 0 => by
      have : (onSched sched 0)ᶜ = (∅ : Set (Hist Q 0)) := by
        ext ω; simp [onSched]
      rw [this, measure_empty]
  | n + 1 => by
      haveI := hist_prob C (schedPolicy sched) w n
      haveI := (schedPolicy sched (Q := Q)).markov n
      haveI := obsKernel_markov C w n
      simp only [hist]
      rw [Measure.map_apply (measurable_snocMap n) (measurableSet_onSched sched (n + 1)).compl]
      have hpre : snocMap n ⁻¹' (onSched sched (n + 1))ᶜ
          = Prod.fst ⁻¹' ({x : Hist Q n × Q | x.1 ∈ onSched sched n ∧ x.2 = sched n}ᶜ) := by
        ext p
        simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq]
        rw [snoc_onSched]
      have hmeasX : MeasurableSet {x : Hist Q n × Q | x.1 ∈ onSched sched n ∧ x.2 = sched n} :=
        (measurable_fst (measurableSet_onSched sched n)).inter
          (measurable_snd (measurableSet_singleton _))
      rw [hpre]
      refine compProd_null_fst _ _ _ hmeasX.compl ?_
      -- the deterministic kernel puts the scheduled query at every history
      rw [Measure.compProd_apply hmeasX.compl]
      refine (lintegral_eq_zero_iff (Kernel.measurable_kernel_prodMk_left hmeasX.compl)).mpr ?_
      have hnull := hist_sched_null C sched w n
      refine (ae_iff.mpr ?_)
      refine measure_mono_null (fun h hh => ?_) hnull
      intro hon
      apply hh
      show (schedPolicy sched).step n h (Prod.mk h ⁻¹'
        {x : Hist Q n × Q | x.1 ∈ onSched sched n ∧ x.2 = sched n}ᶜ) = 0
      rw [show (schedPolicy sched).step n h = Measure.dirac (sched n) from
        Kernel.deterministic_apply (measurable_const (a := sched n)) h]
      rw [Measure.dirac_apply' _ (measurable_prodMk_left hmeasX.compl)]
      simp [hon]

theorem hist_sched_ae (C : Channel W Q) (sched : ℕ → Q) (w : W) (n : ℕ) :
    ∀ᵐ ω ∂hist C (schedPolicy sched) w n, ∀ i : Fin n, (ω i).1 = sched i := by
  refine ae_iff.mpr ?_
  have := hist_sched_null C sched w n
  refine measure_mono_null (fun ω hω => ?_) this
  simp only [Set.mem_setOf_eq, not_forall] at hω
  obtain ⟨i, hi⟩ := hω
  exact fun hon => hi (hon i)

/-- The number of non-dummy entries of the schedule. -/
noncomputable def schedCost (sched : ℕ → Q) (dummy : Q) (n : ℕ) : ℕ :=
  ∑ i : Fin n, if sched i = dummy then 0 else 1

/-- **The cost of a scheduled policy is its number of non-dummy entries.** -/
theorem costN_sched (C : Channel W Q) (sched : ℕ → Q) (w : W) (n : ℕ) :
    costN C (schedPolicy sched) w n = schedCost sched C.dummy n := by
  haveI := hist_prob C (schedPolicy sched) w n
  unfold costN
  have hae : ∀ᵐ ω ∂hist C (schedPolicy sched) w n,
      (tauN C.dummy n ω : ℝ≥0∞) = (schedCost sched C.dummy n : ℝ≥0∞) := by
    filter_upwards [hist_sched_ae C sched w n] with ω hω
    unfold tauN schedCost
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hω i]
  rw [lintegral_congr_ae hae, lintegral_const, measure_univ, mul_one]

#print axioms hist_sched_ae
#print axioms costN_sched

end CIGAMF.P13.PaperBSchedule
