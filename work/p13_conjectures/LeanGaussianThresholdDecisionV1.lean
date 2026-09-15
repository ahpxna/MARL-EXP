import «LeanGaussianProductOverlapV1»

/-! Exact risks of the sign-of-sum recommendation rule. No Monte Carlo or
asymptotic approximation enters these identities. -/
namespace CIGAMF.P13.GaussianThresholdDecision
open MeasureTheory ProbabilityTheory Set
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.GaussianSampleProduct
open CIGAMF.P13.GaussianProductOverlap CIGAMF.P13.D6GaussianOverlap
noncomputable section
attribute [local instance] Classical.propDecidable

def choosePlus (N : ℕ) (x : Samples ℝ N) : Prop := 0 ≤ sumSamples N x

/-- Exact minus-environment risk when recommending plus incurs loss c. -/
theorem minus_threshold_risk (a c : ℝ) (N : ℕ) (hN : 0 < N) :
    (∫ x, if choosePlus N x then c else 0 ∂resource (gaussianReal (-a) 1) N ())=
      c*standardTail (a*Real.sqrt N) := by
  classical
  have hs : MeasurableSet {x : Samples ℝ N | 0 ≤ sumSamples N x} :=
    measurableSet_le measurable_const (measurable_sumSamples N)
  change (∫ x, {x : Samples ℝ N | 0 ≤ sumSamples N x}.indicator (fun _ => c) x
    ∂resource (gaussianReal (-a) 1) N ())=_
  rw [integral_indicator hs,setIntegral_const]
  simp only [Measure.real,negative_sum_half_mass a N hN,smul_eq_mul,standardTail]
  ring

/-- Exact plus-environment risk; ties are assigned to plus. -/
theorem plus_threshold_risk (a c : ℝ) (N : ℕ) (hN : 0 < N) :
    (∫ x, if choosePlus N x then 0 else c ∂resource (gaussianReal a 1) N ())=
      c*standardTail (a*Real.sqrt N) := by
  classical
  have hs : MeasurableSet {x : Samples ℝ N | sumSamples N x < 0} :=
    measurableSet_lt (measurable_sumSamples N) measurable_const
  have hf : (fun x : Samples ℝ N => if choosePlus N x then 0 else c)=
      {x : Samples ℝ N | sumSamples N x < 0}.indicator (fun _ => c) := by
    funext x
    by_cases hx : 0 ≤ sumSamples N x <;> simp [choosePlus,Set.indicator,hx,not_lt.mpr] at *
  rw [hf,integral_indicator hs,setIntegral_const]
  simp only [Measure.real,positive_sum_half_mass a N hN,smul_eq_mul,standardTail]
  ring

/-- For equal cross-losses the exact Gaussian product lower bound is attained. -/
theorem equal_loss_attainment (a c : ℝ) (N : ℕ) (hN : 0 < N) :
    max (∫ x, if choosePlus N x then c else 0 ∂resource (gaussianReal (-a) 1) N ())
      (∫ x, if choosePlus N x then 0 else c ∂resource (gaussianReal a 1) N ())=
      c*standardTail (a*Real.sqrt N) := by
  rw [minus_threshold_risk a c N hN,plus_threshold_risk a c N hN,max_self]

#print axioms minus_threshold_risk
#print axioms plus_threshold_risk
#print axioms equal_loss_attainment
end
end CIGAMF.P13.GaussianThresholdDecision
