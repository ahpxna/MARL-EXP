import «LeanAdaptiveResourceMapV1»
import «LeanD6GaussianQueryDominanceV1»
import Mathlib.Probability.Kernel.Composition.CompMap

/-! Actual D6 finite-horizon state/transcript simulation. H can include the
entire query/response history and a parameter-independent policy seed. Fresh
standard noise is included in the resource law explicitly; removing that
ancillary randomness and reducing to the sample mean are separate results. -/
namespace CIGAMF.P13.D6AdaptiveTranscript
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
variable {n : ℕ} {H : Type*} [MeasurableSpace H]

lemma feed_deterministic_apply {X : Type} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (f : H × X → H)
    (hf : Measurable f) (h : H) :
    feed P (Kernel.deterministic f hf) h = P.map (fun x => f (h,x)) := by
  rw [feed,Kernel.deterministic_comp_eq_map,Kernel.map_apply _ hf,
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map hf (by fun_prop)]
  rfl

def gaussianKernel (m : H → ℝ) (hm : Measurable m) : Kernel H ℝ where
  toFun h := gaussianReal (m h) 1
  measurable' := measurable_gaussianReal.comp (hm.prodMk measurable_const)

instance gaussianKernelMarkov (m : H → ℝ) (hm : Measurable m) :
    IsMarkovKernel (gaussianKernel m hm) := by
  constructor
  intro h
  change IsProbabilityMeasure (gaussianReal (m h) 1)
  infer_instance

def actualStep (m : H → ℝ) (hm : Measurable m)
    (update : H × ℝ → H) (hu : Measurable update) : Kernel H H :=
  (Kernel.id ×ₖ gaussianKernel m hm).map update

lemma actualStep_apply (m : H → ℝ) (hm : Measurable m)
    (update : H × ℝ → H) (hu : Measurable update) (h : H) :
    actualStep m hm update hu h =
      (gaussianReal (m h) 1).map (fun y => update (h,y)) := by
  rw [actualStep,Kernel.map_apply _ hu,Kernel.prod_apply,Kernel.id_apply,
    Measure.dirac_prod,Measure.map_map hu (by fun_prop)]
  rfl

/-- Resource consists of one B-off observation and free independent randomization. -/
def resourceLaw (q mu : ℝ) : Measure (ℝ × ℝ) :=
  (gaussianReal (1+q-q*mu) 1).prod (gaussianReal 0 1)

instance resourceLawProbability (q mu : ℝ) : IsProbabilityMeasure (resourceLaw q mu) := by
  unfold resourceLaw
  infer_instance

/-- For any state-dependent legal query, the same measurable simulator yields
its exact Gaussian response law at every true margin. -/
theorem actual_step_from_resource
    (A : Finset (I n)) (j : I n) (q : ℝ) (hq : 2 ≤ q) (hj : j ∉ A)
    (hB : ((others A j).card : ℝ)=q)
    (policy : H → Measurement n) (legal : ∀ h, Legal j q (policy h))
    (ha : Measurable (fun h => meanOffset A j (policy h)))
    (hb : Measurable (fun h => meanSlope A j (policy h)))
    (update : H × ℝ → H) (hu : Measurable update) (mu : ℝ) :
    ∃ hm : Measurable (fun h => actualMean A j mu (policy h)),
      ∃ hf : Measurable (fun hx : H × (ℝ × ℝ) =>
        update (hx.1,simulate A j q (policy hx.1) hx.2.1 hx.2.2)),
      actualStep (fun h => actualMean A j mu (policy h)) hm update hu =
        feed (resourceLaw q mu) (Kernel.deterministic _ hf) := by
  have hm : Measurable (fun h => actualMean A j mu (policy h)) := by
    simp_rw [actual_mean_affine A j hj q mu _ (legal _)]
    exact ha.add (hb.mul_const mu)
  have hf : Measurable (fun hx : H × (ℝ × ℝ) =>
      update (hx.1,simulate A j q (policy hx.1) hx.2.1 hx.2.2)) := by
    apply hu.comp
    apply measurable_fst.prodMk
    unfold simulate
    have hax := ha.comp (measurable_fst : Measurable (Prod.fst : H × (ℝ × ℝ) → H))
    have hbx := hb.comp (measurable_fst : Measurable (Prod.fst : H × (ℝ × ℝ) → H))
    fun_prop
  refine ⟨hm,hf,?_⟩
  ext1 h
  rw [actualStep_apply,feed_deterministic_apply]
  have hX : HasLaw Prod.fst
      (gaussianReal (actualMean A j mu (.inr (others A j,false))) 1) (resourceLaw q mu) := by
    rw [B_off_mean A j q hq hj hB mu]
    refine ⟨by fun_prop,?_⟩
    simp [resourceLaw]
  have hZ : HasLaw Prod.snd (gaussianReal 0 1) (resourceLaw q mu) := by
    refine ⟨by fun_prop,?_⟩
    simp [resourceLaw]
  have hi : IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd (resourceLaw q mu) := by
    exact indepFun_prod measurable_id measurable_id
  have hd := actual_query_gaussian_dominance A j q hq hj hB (policy h) (legal h) mu hX hZ hi
  have hg : Measurable (fun y : ℝ => update (h,y)) := hu.comp (measurable_const.prodMk measurable_id)
  have ht := congrArg (fun P : Measure ℝ => P.map (fun y => update (h,y))) hd.map_eq
  rw [Measure.map_map hg (by unfold simulate; fun_prop)] at ht
  exact ht.symm

/-- A single parameter-free simulator generates the complete actual D6 state
law for every margin and every finite horizon. An independent policy seed can
be included in H and its initial law; update can retain all queries and answers. -/
theorem actual_full_transcript
    (A : Finset (I n)) (j : I n) (q : ℝ) (hq : 2 ≤ q) (hj : j ∉ A)
    (hB : ((others A j).card : ℝ)=q)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (policy : ℕ → H → Measurement n) (legal : ∀ t h, Legal j q (policy t h))
    (ha : ∀ t, Measurable (fun h => meanOffset A j (policy t h)))
    (hb : ∀ t, Measurable (fun h => meanSlope A j (policy t h)))
    (update : ℕ → H × ℝ → H) (hu : ∀ t, Measurable (update t))
    (N : ℕ) :
    ∃ hm : ∀ mu t, Measurable (fun h => actualMean A j mu (policy t h)),
      ∃ K : Kernel (Samples (ℝ × ℝ) N) H, IsMarkovKernel K ∧ ∀ mu,
        K ∘ₖ resource (resourceLaw q mu) N =
          trajectory initial (fun t => actualStep (fun h => actualMean A j mu (policy t h))
            (hm mu t) (update t) (hu t)) N := by
  have hm : ∀ mu t, Measurable (fun h => actualMean A j mu (policy t h)) := by
    intro mu t
    simp_rw [actual_mean_affine A j hj q mu _ (legal t _)]
    exact (ha t).add ((hb t).mul_const mu)
  have hf : ∀ t, Measurable (fun hx : H × (ℝ × ℝ) =>
      update t (hx.1,simulate A j q (policy t hx.1) hx.2.1 hx.2.2)) := by
    intro t
    apply (hu t).comp
    apply measurable_fst.prodMk
    unfold simulate
    have hax := (ha t).comp (measurable_fst : Measurable (Prod.fst : H × (ℝ × ℝ) → H))
    have hbx := (hb t).comp (measurable_fst : Measurable (Prod.fst : H × (ℝ × ℝ) → H))
    fun_prop
  let sim : ℕ → Kernel (H × (ℝ × ℝ)) H := fun t => Kernel.deterministic _ (hf t)
  haveI : ∀ t, IsMarkovKernel (sim t) := fun t => inferInstanceAs
    (IsMarkovKernel (Kernel.deterministic _ (hf t)))
  refine ⟨hm,?_⟩
  apply uniform_transcript_simulation initial sim (resourceLaw q)
    (fun mu t => actualStep (fun h => actualMean A j mu (policy t h))
      (hm mu t) (update t) (hu t)) ?_ N
  intro mu t
  obtain ⟨hm',hf',heq⟩ := actual_step_from_resource A j q hq hj hB
    (policy t) (legal t) (ha t) (hb t) (update t) (hu t) mu
  exact heq

def augmentGaussian : Kernel ℝ (ℝ × ℝ) := Kernel.id ×ₖ Kernel.const ℝ (gaussianReal 0 1)

instance augmentGaussianMarkov : IsMarkovKernel augmentGaussian := by
  unfold augmentGaussian
  infer_instance

lemma augmented_law (q mu : ℝ) : resourceLaw q mu =
    augmentGaussian ∘ₘ gaussianReal (1+q-q*mu) 1 := by
  unfold resourceLaw augmentGaussian
  rw [← Measure.compProd_eq_comp_prod,Measure.compProd_const]

/-- Full adaptive state/transcript domination by N actual B-off measurements.
All auxiliary randomization has been moved into a single margin-independent
Markov kernel; it is no longer supplied as an observed resource. -/
theorem actual_Boff_transcript
    (A : Finset (I n)) (j : I n) (q : ℝ) (hq : 2 ≤ q) (hj : j ∉ A)
    (hB : ((others A j).card : ℝ)=q)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (policy : ℕ → H → Measurement n) (legal : ∀ t h, Legal j q (policy t h))
    (ha : ∀ t, Measurable (fun h => meanOffset A j (policy t h)))
    (hb : ∀ t, Measurable (fun h => meanSlope A j (policy t h)))
    (update : ℕ → H × ℝ → H) (hu : ∀ t, Measurable (update t)) (N : ℕ) :
    ∃ hm : ∀ mu t, Measurable (fun h => actualMean A j mu (policy t h)),
      ∃ K : Kernel (Samples ℝ N) H, IsMarkovKernel K ∧ ∀ mu,
        K ∘ₖ resource (gaussianReal (1+q-q*mu) 1) N =
          trajectory initial (fun t => actualStep (fun h => actualMean A j mu (policy t h))
            (hm mu t) (update t) (hu t)) N := by
  obtain ⟨hm,K,hK,h⟩ := actual_full_transcript A j q hq hj hB initial policy legal ha hb update hu N
  letI := hK
  refine ⟨hm,?_⟩
  apply CIGAMF.P13.AdaptiveResourceMap.remove_ancillary augmentGaussian
    (fun mu => gaussianReal (1+q-q*mu) 1) N K _
  intro mu
  rw [← augmented_law]
  exact h mu

#print axioms feed_deterministic_apply
#print axioms actualStep_apply
#print axioms actual_step_from_resource
#print axioms actual_full_transcript
#print axioms actual_Boff_transcript
end
end CIGAMF.P13.D6AdaptiveTranscript
