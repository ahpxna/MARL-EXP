import «LeanGaussianThresholdDecisionV1»

/-! Exact risk of a two-allocation recommendation with nonzero correct-side
loss; needed when the phase-III allocation is frozen at the boundary. -/
namespace CIGAMF.P13.GaussianThresholdRisk
open MeasureTheory ProbabilityTheory Set
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.GaussianSampleProduct
open CIGAMF.P13.D6GaussianOverlap CIGAMF.P13.GaussianThresholdDecision
noncomputable section
attribute [local instance] Classical.propDecidable

lemma integrable_threshold (m good bad : ℝ) (N : ℕ) :
    Integrable (fun x : Samples ℝ N => if choosePlus N x then bad else good)
      (resource (gaussianReal m 1) N ()) := by
  have hs : MeasurableSet {x : Samples ℝ N | choosePlus N x} :=
    measurableSet_le measurable_const (measurable_sumSamples N)
  have hm : Measurable (fun x : Samples ℝ N => if choosePlus N x then bad else good) :=
    Measurable.ite hs measurable_const measurable_const
  refine ⟨hm.aestronglyMeasurable,HasFiniteIntegral.of_bounded (C := max |good| |bad|) ?_⟩
  apply Filter.Eventually.of_forall
  intro x
  by_cases h : choosePlus N x <;> simp only [h,ite_true,ite_false,Real.norm_eq_abs]
  · exact le_max_right _ _
  · exact le_max_left _ _

theorem minus_risk (a good bad : ℝ) (N : ℕ) (hN : 0 < N) :
    (∫ x, if choosePlus N x then bad else good ∂resource (gaussianReal (-a) 1) N ())=
      good+(bad-good)*standardTail (a*Real.sqrt N) := by
  have hf : (fun x : Samples ℝ N => if choosePlus N x then bad else good)=
      (fun _ => good)+(fun x => if choosePlus N x then bad-good else 0) := by
    funext x
    by_cases h : choosePlus N x <;> simp [h]
  rw [hf,integral_add' (integrable_const good) (integrable_threshold (-a) 0 (bad-good) N)]
  rw [minus_threshold_risk a (bad-good) N hN]
  simp

theorem plus_risk (a good bad : ℝ) (N : ℕ) (hN : 0 < N) :
    (∫ x, if choosePlus N x then good else bad ∂resource (gaussianReal a 1) N ())=
      good+(bad-good)*standardTail (a*Real.sqrt N) := by
  have hf : (fun x : Samples ℝ N => if choosePlus N x then good else bad)=
      (fun _ => good)+(fun x => if choosePlus N x then 0 else bad-good) := by
    funext x
    by_cases h : choosePlus N x <;> simp [h]
  rw [hf,integral_add' (integrable_const good) (integrable_threshold a (bad-good) 0 N)]
  rw [plus_threshold_risk a (bad-good) N hN]
  simp

#print axioms minus_risk
#print axioms plus_risk
end
end CIGAMF.P13.GaussianThresholdRisk
