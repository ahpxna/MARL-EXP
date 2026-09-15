import «LeanAdaptiveTranscriptKernelV1»
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual Gaussian product law on the same nested samples used by the
adaptive transcript simulator. Sum law and product density are established
before a common-part comparison can be invoked. -/
namespace CIGAMF.P13.GaussianSampleProduct
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section

def sumSamples : (N : ℕ) → Samples ℝ N → ℝ
  | 0 => fun _ => 0
  | N+1 => fun x => sumSamples N x.1+x.2

theorem measurable_sumSamples (N : ℕ) : Measurable (sumSamples N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih => exact (ih.comp measurable_fst).add measurable_snd

theorem resource_succ (P : Measure ℝ) [IsProbabilityMeasure P] (N : ℕ) :
    resource P (N+1) ()=(resource P N ()).prod P := by
  rw [resource,Kernel.prod_apply,Kernel.const_apply]

/-- Exact sum distribution for the resource used by the adaptive simulator. -/
theorem gaussian_sum_law (m : ℝ) (N : ℕ) :
    HasLaw (sumSamples N) (gaussianReal ((N:ℝ)*m) (N:NNReal))
      (resource (gaussianReal m 1) N ()) := by
  induction N with
  | zero =>
    refine ⟨by exact measurable_const.aemeasurable,?_⟩
    simp [resource,sumSamples,Kernel.id_apply,gaussianReal_zero_var]
  | succ N ih =>
    rw [resource_succ]
    have hx : HasLaw (Prod.fst : Samples ℝ N × ℝ → Samples ℝ N)
        (resource (gaussianReal m 1) N ())
        ((resource (gaussianReal m 1) N ()).prod (gaussianReal m 1)) := by
      refine ⟨by fun_prop,?_⟩
      simp
    have hy : HasLaw (Prod.snd : Samples ℝ N × ℝ → ℝ) (gaussianReal m 1)
        ((resource (gaussianReal m 1) N ()).prod (gaussianReal m 1)) := by
      refine ⟨by fun_prop,?_⟩
      simp
    have hi : IndepFun (fun x : Samples ℝ N × ℝ => sumSamples N x.1) Prod.snd
        ((resource (gaussianReal m 1) N ()).prod (gaussianReal m 1)) :=
      (indepFun_prod measurable_id measurable_id).comp (measurable_sumSamples N) measurable_id
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hi (ih.fun_comp hx) hy
    have hfun : ((fun x : Samples ℝ N × ℝ => sumSamples N x.1)+Prod.snd)=sumSamples (N+1) := rfl
    rw [hfun] at hsum
    refine ⟨(measurable_sumSamples (N+1)).aemeasurable,?_⟩
    convert hsum using 1 <;> push_cast <;> ring

def base : (N : ℕ) → Measure (Samples ℝ N)
  | 0 => Measure.dirac ()
  | N+1 => (base N).prod volume

instance baseSigmaFinite : (N : ℕ) → SigmaFinite (base N)
  | 0 => inferInstanceAs (SigmaFinite (Measure.dirac ()))
  | N+1 => by
    letI := baseSigmaFinite N
    change SigmaFinite ((base N).prod volume)
    infer_instance

def density (m : ℝ) : (N : ℕ) → Samples ℝ N → ℝ
  | 0 => fun _ => 1
  | N+1 => fun x => density m N x.1*gaussianPDFReal m 1 x.2

theorem density_nonnegative (m : ℝ) (N : ℕ) (x : Samples ℝ N) : 0 ≤ density m N x := by
  induction N with
  | zero => exact zero_le_one
  | succ N ih => exact mul_nonneg (ih x.1) (gaussianPDFReal_nonneg m 1 x.2)

theorem measurable_density (m : ℝ) (N : ℕ) : Measurable (density m N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    change Measurable (fun x : Samples ℝ N × ℝ => density m N x.1*gaussianPDFReal m 1 x.2)
    exact (ih.comp measurable_fst).mul (by fun_prop)

theorem gaussian_product_density (m : ℝ) (N : ℕ) :
    resource (gaussianReal m 1) N ()=(base N).withDensity (fun x => ENNReal.ofReal (density m N x)) := by
  induction N with
  | zero => simp [resource,base,density,Kernel.id_apply]
  | succ N ih =>
    rw [resource_succ,ih,gaussianReal_of_var_ne_zero m (by norm_num : (1:NNReal) ≠ 0),
      prod_withDensity (by exact (measurable_density m N).ennreal_ofReal)
        (measurable_gaussianPDF m 1)]
    congr 1
    funext x
    change ENNReal.ofReal (density m N x.1)*ENNReal.ofReal (gaussianPDFReal m 1 x.2)=
      ENNReal.ofReal (density m N x.1*gaussianPDFReal m 1 x.2)
    exact (ENNReal.ofReal_mul (density_nonnegative m N x.1)).symm

lemma unit_density_ratio (a x : ℝ) :
    gaussianPDFReal a 1 x=gaussianPDFReal (-a) 1 x*Real.exp (2*a*x) := by
  simp only [gaussianPDFReal,NNReal.coe_one,mul_one]
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

/-- The likelihood ratio for the entire product depends only on its sum. -/
theorem product_density_ratio (a : ℝ) (N : ℕ) (x : Samples ℝ N) :
    density a N x=density (-a) N x*Real.exp (2*a*sumSamples N x) := by
  induction N with
  | zero => simp [density,sumSamples]
  | succ N ih =>
    simp only [density,sumSamples]
    rw [ih x.1,unit_density_ratio a x.2]
    have he : 2*a*(sumSamples N x.1+x.2)=2*a*sumSamples N x.1+2*a*x.2 := by ring
    rw [he,Real.exp_add]
    ring

#print axioms gaussian_sum_law
#print axioms gaussian_product_density
#print axioms product_density_ratio
end
end CIGAMF.P13.GaussianSampleProduct
