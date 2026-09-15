import «LeanGaussianSampleProductV1»
import «LeanD6GaussianOverlapV1»
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Exact common mass of N actual independent Gaussian observations. The loss
may depend on every observation, not just on their sum. -/
namespace CIGAMF.P13.GaussianProductOverlap
open MeasureTheory ProbabilityTheory Set
open CIGAMF.P13.AdaptiveTranscriptKernel CIGAMF.P13.GaussianSampleProduct
open CIGAMF.P13.D6GaussianOverlap
noncomputable section

lemma normalized_sum_law (m : ℝ) (N : ℕ) (hN : 0 < N) :
    HasLaw (fun x => sumSamples N x / Real.sqrt N)
      (gaussianReal (m*Real.sqrt N) 1) (resource (gaussianReal m 1) N ()) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt (N:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
  have hv0 : (NNReal.mk ((Real.sqrt (N:ℝ))^2) (sq_nonneg _))=(N:NNReal) := by
    apply NNReal.coe_injective
    exact Real.sq_sqrt hn.le
  have hv : (N:NNReal) / (NNReal.mk ((Real.sqrt (N:ℝ))^2) (sq_nonneg _)) = 1 := by
    rw [hv0,div_self (by exact_mod_cast (Nat.ne_of_gt hN) : (N:NNReal) ≠ 0)]
  have hm : (N:ℝ)*m/Real.sqrt N=m*Real.sqrt N := by
    apply (div_eq_iff hs).mpr
    calc
      (N:ℝ)*m = m*(Real.sqrt (N:ℝ))^2 := by rw [Real.sq_sqrt hn.le]; ring
      _ = m*Real.sqrt N*Real.sqrt N := by ring
  simpa only [hm,hv] using gaussianReal_div_const (gaussian_sum_law m N) (Real.sqrt N)

lemma gaussian_left_mass (a : ℝ) :
    gaussianReal a 1 (Iio 0)=gaussianReal 0 1 (Ioi a) := by
  have hm := congrArg (fun P : Measure ℝ => P (Ioi (0:ℝ)))
    (gaussianReal_map_neg (μ := a) (v := 1))
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at hm
  have hp : (fun x : ℝ => -x) ⁻¹' Ioi 0=Iio 0 := by
    ext x
    simp
  rw [hp,shifted_half_mass] at hm
  exact hm

lemma negative_sum_half_mass (a : ℝ) (N : ℕ) (hN : 0 < N) :
    resource (gaussianReal (-a) 1) N () {x | 0 ≤ sumSamples N x}=
      gaussianReal 0 1 (Ioi (a*Real.sqrt N)) := by
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hm := (normalized_sum_law (-a) N hN).measure_eq (p := fun x : ℝ => 0 ≤ x) measurableSet_Ici
  have hp : {x : Samples ℝ N | 0 ≤ sumSamples N x / Real.sqrt N}=
      {x | 0 ≤ sumSamples N x} := by
    ext x
    simp only [Set.mem_setOf_eq,le_div_iff₀ hs,zero_mul]
  change resource (gaussianReal (-a) 1) N () {x | 0 ≤ sumSamples N x / Real.sqrt N}=
    gaussianReal ((-a)*Real.sqrt N) 1 (Ici 0) at hm
  rw [hp,neg_mul] at hm
  letI : NullSingletonClass (gaussianReal (-(a*Real.sqrt N)) 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  rw [← measure_congr Ioi_ae_eq_Ici,shifted_half_mass] at hm
  exact hm

lemma positive_sum_half_mass (a : ℝ) (N : ℕ) (hN : 0 < N) :
    resource (gaussianReal a 1) N () {x | sumSamples N x < 0}=
      gaussianReal 0 1 (Ioi (a*Real.sqrt N)) := by
  have hs : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hm := (normalized_sum_law a N hN).measure_eq (p := fun x : ℝ => x < 0) measurableSet_Iio
  have hp : {x : Samples ℝ N | sumSamples N x / Real.sqrt N < 0}=
      {x | sumSamples N x < 0} := by
    ext x
    simp only [Set.mem_setOf_eq,div_lt_iff₀ hs,zero_mul]
  change resource (gaussianReal a 1) N () {x | sumSamples N x / Real.sqrt N < 0}=
    gaussianReal (a*Real.sqrt N) 1 (Iio 0) at hm
  rw [hp,gaussian_left_mass] at hm
  exact hm

lemma min_density_piecewise (a : ℝ) (ha : 0 ≤ a) (N : ℕ) :
    (fun x => ENNReal.ofReal (min (density (-a) N x) (density a N x)))=
      {x | 0 ≤ sumSamples N x}.piecewise (fun x => ENNReal.ofReal (density (-a) N x))
        (fun x => ENNReal.ofReal (density a N x)) := by
  classical
  funext x
  by_cases hx : 0 ≤ sumSamples N x
  · have hr : density (-a) N x ≤ density a N x := by
      rw [product_density_ratio a N x]
      apply le_mul_of_one_le_right (density_nonnegative (-a) N x)
      exact Real.one_le_exp_iff.mpr (by positivity)
    simp [Set.piecewise,hx,min_eq_left hr]
  · have hr : density a N x ≤ density (-a) N x := by
      rw [product_density_ratio a N x]
      apply mul_le_of_le_one_right (density_nonnegative (-a) N x)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_ge hx))
    simp [Set.piecewise,hx,min_eq_right hr]

/-- Common mass on the complete N-observation sample space, with no loss
restriction to the sufficient statistic. -/
theorem product_overlap_lintegral (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 0 < N) :
    (∫⁻ x, ENNReal.ofReal (min (density (-a) N x) (density a N x)) ∂base N)=
      2*gaussianReal 0 1 (Ioi (a*Real.sqrt N)) := by
  classical
  have hs : MeasurableSet {x : Samples ℝ N | 0 ≤ sumSamples N x} :=
    measurableSet_le measurable_const (measurable_sumSamples N)
  rw [min_density_piecewise a ha N,lintegral_piecewise hs]
  rw [← withDensity_apply _ hs,← withDensity_apply _ hs.compl,
    ← gaussian_product_density,← gaussian_product_density]
  have hc : {x : Samples ℝ N | 0 ≤ sumSamples N x}ᶜ={x | sumSamples N x < 0} := by
    ext x
    simp
  rw [hc,negative_sum_half_mass a N hN,positive_sum_half_mass a N hN,two_mul]

/-- Real-valued exact overlap 2 Phi(-a sqrt N). -/
theorem product_overlap (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 0 < N) :
    (∫ x, min (density (-a) N x) (density a N x) ∂base N)=
      2*standardTail (a*Real.sqrt N) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => le_min (density_nonnegative (-a) N x) (density_nonnegative a N x))
    (((measurable_density (-a) N).min (measurable_density a N)).aestronglyMeasurable),
    product_overlap_lintegral a ha N hN,ENNReal.toReal_mul]
  simp [standardTail]

lemma integrable_density (m : ℝ) (N : ℕ) : Integrable (density m N) (base N) := by
  refine ⟨(measurable_density m N).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (density_nonnegative m N))]
  have h := congrArg (fun P : Measure (Samples ℝ N) => P Set.univ) (gaussian_product_density m N)
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,measure_univ] at h
  rw [← h]
  exact ENNReal.one_lt_top

/-- Exact lower bound for any full-sample decision losses. -/
theorem product_max_risk_lower (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 0 < N)
    (lossminus lossplus : Samples ℝ N → ℝ) (separation : ℝ)
    (hrm : Integrable (fun x => density (-a) N x*lossminus x) (base N))
    (hrp : Integrable (fun x => density a N x*lossplus x) (base N))
    (lm : ∀ x, 0 ≤ lossminus x) (lp : ∀ x, 0 ≤ lossplus x)
    (sep : ∀ x, separation ≤ lossminus x+lossplus x) :
    separation*standardTail (a*Real.sqrt N) ≤
      max (∫ x, density (-a) N x*lossminus x ∂base N)
        (∫ x, density a N x*lossplus x ∂base N) := by
  have h := common_density_risk_lower (base N) (density (-a) N) (density a N)
    lossminus lossplus separation (integrable_density (-a) N) (integrable_density a N)
    hrm hrp (density_nonnegative (-a) N) (density_nonnegative a N) lm lp sep
  rw [product_overlap a ha N hN] at h
  have hm := le_max_left (∫ x, density (-a) N x*lossminus x ∂base N)
    (∫ x, density a N x*lossplus x ∂base N)
  have hp := le_max_right (∫ x, density (-a) N x*lossminus x ∂base N)
    (∫ x, density a N x*lossplus x ∂base N)
  linarith

#print axioms normalized_sum_law
#print axioms product_overlap_lintegral
#print axioms product_overlap
#print axioms product_max_risk_lower
end
end CIGAMF.P13.GaussianProductOverlap
