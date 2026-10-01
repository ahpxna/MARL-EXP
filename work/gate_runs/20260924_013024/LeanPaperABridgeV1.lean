import «LeanPaperA7ProcessV1»
import «LeanPaperBConcentrationV1»

/-!
# Paper A: the stream model and the kernel protocol are the same law

The upper bound of Paper A is proved on the innovation stream (`LeanPaperA7ProcessV1`):
the learner is a deterministic function of the past observations, and observations are
`Y = m_q + s_q omega`.  The change-of-measure lower bound is proved on the kernel protocol of
`LeanPaperBProtocolV1` (`LeanPaperALowerKLV1`).  This module proves that for a deterministic
learner the two are the SAME law of the history, round by round (`stream_eq_hist`):

    law of histF(L, m, s, n)(omega_1..omega_n) under the stream  =  hist(gChan, detPol L, m, n).

`gChan d s` is the Gaussian channel with query `q` observed as `N(m_q, s_q^2)` and a dummy
query `d` whose mean is pinned to `0` in every world, as the protocol requires; `detPol L`
is the learner's rule as a deterministic kernel.

WARNING -- the pinned query.  `gChan d s` fixes the mean of `d` to `0` in every world.  The
theorem is exact for that transformed model, but `d` must be a FRESH query, never a cell of the
experiment: Paper A measures every cell and its alternatives may move any of them.  The
instantiation for Paper A is `LeanPaperABridgeDummyV1` (query type `E ⊕ Unit`, dummy
`Sum.inr ()`, worlds `lift m` on the real cells).  The induction step uses only: the fresh
innovation is independent of the past with law `N(0,1)` (`indep_Xp`, `obs_map`), the
Gaussian is the affine image of `N(0,1)`, and the deterministic kernel is a push-forward
(`Measure.compProd_deterministic`).
-/

namespace CIGAMF.P13.PaperABridge

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open CIGAMF.P13.PaperA7Stream CIGAMF.P13.PaperA7Process
open CIGAMF.P13.PaperBChiSq CIGAMF.P13.PaperBProtocol CIGAMF.P13.PaperBConcentration

variable {Q : Type*} [Fintype Q] [DecidableEq Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]

/-- The variance of query `q`. -/
def vq (s : Q → ℝ) (q : Q) : ℝ≥0 := ⟨s q ^ 2, sq_nonneg _⟩

theorem vq_ne_zero (s : Q → ℝ) (hs : ∀ q, 0 < s q) (q : Q) : vq s q ≠ 0 := by
  intro h
  have : (s q ^ 2 : ℝ) = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  have : 0 < s q ^ 2 := by have := hs q; positivity
  linarith

/-- The mean function with the dummy pinned at `0`. -/
def mz (d : Q) (m : Q → ℝ) (q : Q) : ℝ := if q = d then 0 else m q

/-- **The Gaussian channel.** -/
noncomputable def gChan (d : Q) (s : Q → ℝ) (hs : ∀ q, 0 < s q) : Channel (Q → ℝ) Q where
  dens m q y := gaussianPDFReal (mz d m q) (vq s q) y
  dummy := d
  meas m q := measurable_gaussianPDFReal _ _
  pos m q y := gaussianPDFReal_pos _ _ _ (vq_ne_zero s hs q)
  mass m q := lintegral_gaussianPDF_eq_one _ (vq_ne_zero s hs q)
  dummy_same m m' y := by simp [mz]

/-- The learner's rule as a deterministic policy. -/
noncomputable def detPol (L : Learner Q) : Policy Q where
  step n := Kernel.deterministic (L.rule n) (L.meas n)
  markov n := inferInstance

theorem obsKernel_gChan (d : Q) (s : Q → ℝ) (hs : ∀ q, 0 < s q) (m : Q → ℝ) (n : ℕ)
    (x : Hist Q n × Q) :
    obsKernel (gChan d s hs) m n x = gaussianReal (mz d m x.2) (vq s x.2) := by
  rw [obsKernel_apply, gaussianReal_of_var_ne_zero _ (vq_ne_zero s hs x.2)]
  rfl

/-- The Gaussian is the affine image of the standard one. -/
theorem gauss_affine (μ0 : ℝ) (s0 : ℝ) :
    (gaussianReal 0 1).map (fun z => μ0 + s0 * z) = gaussianReal μ0 ⟨s0 ^ 2, sq_nonneg _⟩ := by
  have h1 := gaussianReal_map_const_mul (μ := 0) (v := 1) s0
  have hfun : (fun z => μ0 + s0 * z) = (fun x => x + μ0) ∘ (fun z => s0 * z) := by
    funext z; simp [add_comm]
  rw [hfun, ← Measure.map_map (measurable_add_const μ0) (measurable_const_mul s0), h1,
    gaussianReal_map_add_const]
  congr 1
  · simp
  · apply NNReal.eq
    simp
    try rfl

/-- The history map of one more round, as a function of past and fresh innovation. -/
noncomputable def Gstep (L : Learner Q) (θ s : Q → ℝ) (n : ℕ) (p : (Fin n → ℝ) × ℝ) :
    Hist Q (n + 1) :=
  snocMap n ((histF L θ s n p.1, L.rule n (histF L θ s n p.1)),
    θ (L.rule n (histF L θ s n p.1)) + s (L.rule n (histF L θ s n p.1)) * p.2)

theorem Gstep_eq (L : Learner Q) (θ s : Q → ℝ) (n : ℕ) (x : Fin n → ℝ) (y : ℝ) :
    Gstep L θ s n (x, y) = histF L θ s (n + 1) (Fin.snoc (α := fun _ => ℝ) x y) := by
  rw [histF_snoc]
  rfl

theorem measurable_Gstep (L : Learner Q) (θ s : Q → ℝ) (n : ℕ) :
    Measurable (Gstep L θ s n) := by
  have hH : Measurable fun p : (Fin n → ℝ) × ℝ => histF L θ s n p.1 :=
    (measurable_histF L θ s n).comp measurable_fst
  have hq := (L.meas n).comp hH
  refine (measurable_snocMap n).comp ((hH.prodMk hq).prodMk ?_)
  exact ((Measurable.of_discrete (f := θ)).comp hq).add
    (((Measurable.of_discrete (f := s)).comp hq).mul measurable_snd)

/-- The stream side of one round. -/
theorem stream_step (L : Learner Q) (θ s : Q → ℝ) (n : ℕ) :
    streamMeasure.map (fun ω => histF L θ s (n + 1) (Xp (n + 1) ω))
      = ((streamMeasure.map (Xp n)).prod (gaussianReal 0 1)).map (Gstep L θ s n) := by
  have hfun : (fun ω => histF L θ s (n + 1) (Xp (n + 1) ω))
      = Gstep L θ s n ∘ (fun ω => (Xp n ω, obs (n + 1) ω)) := by
    funext ω
    simp only [Function.comp_apply]
    rw [Gstep_eq, Xp_succ]
    rfl
  have hpair : streamMeasure.map (fun ω => (Xp n ω, obs (n + 1) ω))
      = (streamMeasure.map (Xp n)).prod (gaussianReal 0 1) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map (measurable_Xp n).aemeasurable
      (obs_measurable _).aemeasurable).mp (indep_Xp n), obs_map]
  rw [hfun, ← Measure.map_map (measurable_Gstep L θ s n)
    ((measurable_Xp n).prodMk (obs_measurable _)), hpair]

/-- The kernel side of one round, from a push-forward past. -/
theorem kernel_step (L : Learner Q) (d : Q) (s : Q → ℝ) (hs : ∀ q, 0 < s q) (m : Q → ℝ)
    (n : ℕ) (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] :
    ((((ν.map (histF L (mz d m) s n)) ⊗ₘ (detPol L).step n) ⊗ₘ obsKernel (gChan d s hs) m n)).map
        (snocMap n)
      = (ν.prod (gaussianReal 0 1)).map (Gstep L (mz d m) s n) := by
  set H := histF L (mz d m) s n with hH
  have hHm : Measurable H := measurable_histF L (mz d m) s n
  haveI : IsProbabilityMeasure (ν.map H) :=
    (Measure.isProbabilityMeasure_map_iff hHm.aemeasurable).mpr inferInstance
  haveI := obsKernel_markov (gChan d s hs) m n
  have hdet : (ν.map H) ⊗ₘ (detPol L).step n
      = ν.map (fun x => (H x, L.rule n (H x))) := by
    show (ν.map H) ⊗ₘ Kernel.deterministic (L.rule n) (L.meas n) = _
    rw [Measure.compProd_deterministic, Measure.map_map
      (show Measurable (fun a : Hist Q n => (a, L.rule n a)) from measurable_id.prodMk (L.meas n))
      hHm]
    rfl
  ext S hS
  have hS' : MeasurableSet (snocMap n ⁻¹' S) := measurable_snocMap n hS
  rw [Measure.map_apply (measurable_snocMap n) hS, Measure.map_apply (measurable_Gstep _ _ _ n) hS,
    Measure.compProd_apply hS', hdet,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hS')
      (show Measurable (fun x => (H x, L.rule n (H x))) from hHm.prodMk ((L.meas n).comp hHm)),
    Measure.prod_apply (measurable_Gstep _ _ _ n hS)]
  refine lintegral_congr fun x => ?_
  rw [obsKernel_gChan]
  set q := L.rule n (H x) with hq
  have haff := gauss_affine (mz d m q) (s q)
  have hvq : (⟨s q ^ 2, sq_nonneg _⟩ : ℝ≥0) = vq s q := rfl
  rw [hvq] at haff
  rw [← haff, Measure.map_apply (by fun_prop) (measurable_prodMk_left hS')]
  rfl

/-- **The two models give the same law of the history.** -/
theorem stream_eq_hist (L : Learner Q) (d : Q) (s : Q → ℝ) (hs : ∀ q, 0 < s q) (m : Q → ℝ) :
    ∀ n, streamMeasure.map (fun ω => histF L (mz d m) s n (Xp n ω))
      = hist (gChan d s hs) (detPol L) m n
  | 0 => by
      have : (fun ω : ℕ → ℝ => histF L (mz d m) s 0 (Xp 0 ω)) = fun _ => (fun i => i.elim0) := by
        funext ω i
        exact i.elim0
      rw [this, Measure.map_const, measure_univ, one_smul]
      rfl
  | n + 1 => by
      haveI : IsProbabilityMeasure (streamMeasure.map (Xp n)) :=
        (Measure.isProbabilityMeasure_map_iff (measurable_Xp n).aemeasurable).mpr inferInstance
      rw [stream_step, ← kernel_step L d s hs m n (streamMeasure.map (Xp n))]
      simp only [hist]
      rw [← stream_eq_hist L d s hs m n,
        Measure.map_map (measurable_histF L (mz d m) s n) (measurable_Xp n)]
      rfl

#print axioms gauss_affine
#print axioms stream_step
#print axioms kernel_step
#print axioms stream_eq_hist

end CIGAMF.P13.PaperABridge
