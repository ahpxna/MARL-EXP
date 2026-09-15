import «LeanD6AdaptiveLikelihoodV1»
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod

/-! Mixtures over nuisance parameters preserve adaptive likelihood normalization.
The event bound is on the actual terminal state law. An anytime application
must freeze the likelihood at the stopping decision, or spend error over time;
a fixed-horizon bound alone is not called an anytime theorem here. -/
namespace CIGAMF.P13.D6AdaptiveMixtureRisk
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6AdaptiveLikelihood CIGAMF.P13.D6AdaptiveTranscript
open CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
variable {H Θ B : Type*} [MeasurableSpace H] [MeasurableSpace Θ]

def mixture (prior : Measure Θ) (L : Θ → H → ℝ) (h : H) : ENNReal :=
  ∫⁻ θ,ENNReal.ofReal (L θ h) ∂prior

theorem mixture_normalization (P : Measure H) [SFinite P]
    (prior : Measure Θ) [IsProbabilityMeasure prior] (L : Θ → H → ℝ)
    (hm : Measurable (fun x : H × Θ => L x.2 x.1))
    (hn : ∀ θ,(∫⁻ h,ENNReal.ofReal (L θ h) ∂P)=1) :
    (∫⁻ h,mixture prior L h ∂P)=1 := by
  unfold mixture
  rw [lintegral_lintegral_swap ((Measurable.ennreal_ofReal hm).aemeasurable)]
  simp_rw [hn]
  simp

theorem measurable_mixture (prior : Measure Θ) [SFinite prior] (L : Θ → H → ℝ)
    (hm : Measurable (fun x : H × Θ => L x.2 x.1)) : Measurable (mixture prior L) := by
  unfold mixture
  exact (Measurable.ennreal_ofReal hm).lintegral_prod_right

theorem finite_family_tail (P : Measure H) [SFinite P]
    (prior : Measure Θ) [IsProbabilityMeasure prior]
    (W : Finset B) (L : B → Θ → H → ℝ)
    (hm : ∀ b ∈ W,Measurable (fun x : H × Θ => L b x.2 x.1))
    (hn : ∀ b ∈ W,∀ θ,(∫⁻ h,ENNReal.ofReal (L b θ h) ∂P)=1)
    (c : ENNReal) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    P {h | ∃ b ∈ W,c ≤ mixture prior (L b) h} ≤ (W.card : ENNReal)/c := by
  have hs : {h | ∃ b ∈ W,c ≤ mixture prior (L b) h} =
      ⋃ b ∈ W,{h | c ≤ mixture prior (L b) h} := by ext h; simp
  rw [hs]
  calc
    _ ≤ ∑ b ∈ W,P {h | c ≤ mixture prior (L b) h} := measure_biUnion_finset_le W _
    _ ≤ ∑ _b ∈ W,(1:ENNReal)/c := by
      apply Finset.sum_le_sum; intro b hb
      have hh := meas_ge_le_lintegral_div (μ := P)
        (measurable_mixture prior (L b) (hm b hb)).aemeasurable hc hc'
      rw [mixture_normalization P prior (L b) (hm b hb) (hn b hb)] at hh
      exact hh
    _ = _ := by simp [div_eq_mul_inv]

/-- The normalization premise of the tail bound is discharged from the actual
Gaussian adaptive transitions, for every candidate label and nuisance. -/
theorem adaptive_family_tail
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (m : ℕ → H → ℝ) (hm : ∀ t,Measurable (m t))
    (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (prior : Measure Θ) [IsProbabilityMeasure prior] (W : Finset B)
    (v : B → Θ → ℕ → H → ℝ) (L : B → Θ → ℕ → H → ℝ)
    (hLm : ∀ b ∈ W,∀ θ t,Measurable (L b θ t))
    (hL : ∀ b ∈ W,∀ θ t h,0 ≤ L b θ t h)
    (hinit : ∀ b ∈ W,∀ θ,(∫⁻ h,ENNReal.ofReal (L b θ 0 h) ∂initial ())=1)
    (transition : ∀ b ∈ W,∀ θ t h y,L b θ (t+1) (update t (h,y))=
      L b θ t h*likelihood (m t h) (v b θ t h) y)
    (N : ℕ) (hjoint : ∀ b ∈ W,Measurable (fun x : H × Θ => L b x.2 N x.1))
    (c : ENNReal) (hc : c ≠ 0) (hc' : c ≠ ⊤) :
    trajectory initial (fun t => actualStep (m t) (hm t) (update t) (hu t)) N ()
      {h | ∃ b ∈ W,c ≤ mixture prior (fun θ => L b θ N) h} ≤ (W.card : ENNReal)/c := by
  have hstep : ∀ t,IsMarkovKernel (actualStep (m t) (hm t) (update t) (hu t)) := by
    intro t
    unfold actualStep
    exact Kernel.IsMarkovKernel.map _ (hu t)
  have htraj : ∀ t,IsMarkovKernel
      (trajectory initial (fun t => actualStep (m t) (hm t) (update t) (hu t)) t) := by
    intro t
    induction t with
    | zero => exact inferInstanceAs (IsMarkovKernel initial)
    | succ t ih =>
      letI := ih
      letI := hstep t
      change IsMarkovKernel (actualStep (m t) (hm t) (update t) (hu t) ∘ₖ _)
      infer_instance
  letI := htraj N
  apply finite_family_tail _ prior W (fun b θ => L b θ N) hjoint ?_ c hc hc'
  intro b hb θ
  exact adaptive_likelihood_normalization initial m (v b θ) hm update hu (L b θ)
    (hLm b hb θ) (hL b hb θ) (hinit b hb θ) (transition b hb θ) N

#print axioms mixture_normalization
#print axioms finite_family_tail
#print axioms adaptive_family_tail
end
end CIGAMF.P13.D6AdaptiveMixtureRisk
