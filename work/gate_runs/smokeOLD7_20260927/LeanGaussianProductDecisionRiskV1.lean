import «LeanGaussianProductOverlapV1»
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Transfer of the exact N-sample Gaussian risk bound through any Markov
simulator, including randomized decisions based on the complete transcript. -/
namespace CIGAMF.P13.GaussianProductDecisionRisk
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.GaussianSampleProduct
open CIGAMF.P13.D6GaussianOverlap CIGAMF.P13.GaussianProductOverlap
noncomputable section

lemma product_expectation (m : ℝ) (N : ℕ) (f : Samples ℝ N → ℝ) :
    (∫ x, f x ∂resource (gaussianReal m 1) N ())=
      ∫ x, density m N x*f x ∂base N := by
  rw [gaussian_product_density,integral_withDensity_eq_integral_toReal_smul
    (measurable_density m N).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (density_nonnegative m N _),smul_eq_mul]

lemma integrable_product_loss (m : ℝ) (N : ℕ) (f : Samples ℝ N → ℝ)
    (hf : Integrable f (resource (gaussianReal m 1) N ())) :
    Integrable (fun x => density m N x*f x) (base N) := by
  rw [gaussian_product_density] at hf
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_density m N).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hf
  simpa only [ENNReal.toReal_ofReal (density_nonnegative m N _),smul_eq_mul] using h

lemma bounded_integrable {H : Type*} [MeasurableSpace H] (P : Measure H) [IsFiniteMeasure P]
    (f : H → ℝ) (hf : Measurable f) (B : ℝ) (h0 : ∀ h,0 ≤ f h) (hB : ∀ h,f h ≤ B) :
    Integrable f P := by
  refine ⟨hf.aestronglyMeasurable,HasFiniteIntegral.of_bounded (C := B) ?_⟩
  exact Filter.Eventually.of_forall (fun h => by simpa only [Real.norm_of_nonneg (h0 h)] using hB h)

/-- The bound applies to the actual output law of an arbitrary simulator.
Only measurable bounded losses and their pointwise separation are required. -/
theorem markov_product_risk_lower {H : Type*} [MeasurableSpace H]
    (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 0 < N)
    (K : Kernel (Samples ℝ N) H) [IsMarkovKernel K]
    (lm lp : H → ℝ) (hm : Measurable lm) (hp : Measurable lp)
    (Bm Bp separation : ℝ) (hm0 : ∀ h,0 ≤ lm h) (hp0 : ∀ h,0 ≤ lp h)
    (hmb : ∀ h,lm h ≤ Bm) (hpb : ∀ h,lp h ≤ Bp)
    (sep : ∀ h,separation ≤ lm h+lp h) :
    separation*standardTail (a*Real.sqrt N) ≤
      max (∫ h, lm h ∂(K ∘ₖ resource (gaussianReal (-a) 1) N) ())
        (∫ h, lp h ∂(K ∘ₖ resource (gaussianReal a 1) N) ()) := by
  have him := bounded_integrable ((K ∘ₖ resource (gaussianReal (-a) 1) N) ()) lm hm Bm hm0 hmb
  have hip := bounded_integrable ((K ∘ₖ resource (gaussianReal a 1) N) ()) lp hp Bp hp0 hpb
  have hsep : ∀ x : Samples ℝ N,separation ≤ (∫ h,lm h ∂K x)+(∫ h,lp h ∂K x) := by
    intro x
    have im := bounded_integrable (K x) lm hm Bm hm0 hmb
    have ip := bounded_integrable (K x) lp hp Bp hp0 hpb
    have h := integral_mono (integrable_const separation) (im.add ip) sep
    simpa only [Pi.add_apply,integral_const,probReal_univ,one_smul,integral_add im ip] using h
  have h := product_max_risk_lower a ha N hN (fun x => ∫ h,lm h ∂K x)
    (fun x => ∫ h,lp h ∂K x) separation
    (integrable_product_loss (-a) N _ him.integral_comp)
    (integrable_product_loss a N _ hip.integral_comp)
    (fun _ => integral_nonneg hm0) (fun _ => integral_nonneg hp0) hsep
  rw [← product_expectation,← product_expectation,← Kernel.integral_comp him,
    ← Kernel.integral_comp hip] at h
  exact h

#print axioms product_expectation
#print axioms markov_product_risk_lower
end
end CIGAMF.P13.GaussianProductDecisionRisk
