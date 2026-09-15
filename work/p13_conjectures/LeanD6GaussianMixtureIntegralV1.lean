import «LeanD6ProfileStoppingGeometryV1»
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-! The expression used in the stopping boundary is the actual integral
against a standard Gaussian nuisance prior, including its normalizing factor. -/
namespace CIGAMF.P13.D6GaussianMixtureIntegral
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6ProfileStoppingGeometry
noncomputable section

theorem square_completion (c z v u : ℝ) (hv : 0 ≤ v) :
    -u^2/2+quadraticScore c z v u =
      -c/2+z^2/(2*(1+v))-(1+v)*(u-z/(1+v))^2/2 := by
  have hn : 1+v ≠ 0 := by linarith
  unfold quadraticScore
  field_simp [hn]
  <;> ring

lemma prefactor (v : ℝ) (hv : 0 ≤ v) :
    (Real.sqrt (2*Real.pi))⁻¹ =
      (Real.sqrt (1+v))⁻¹*(Real.sqrt (2*Real.pi*(1/(1+v))))⁻¹ := by
  have hvp : 0 < 1+v := by linarith
  have he : 2*Real.pi*(1/(1+v))=(2*Real.pi)/(1+v) := by ring
  rw [he,Real.sqrt_div (by positivity),inv_div]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hvp)]

lemma mixture_density_identity (c z v u : ℝ) (hv : 0 ≤ v) :
    gaussianPDFReal 0 1 u*Real.exp (quadraticScore c z v u) =
      ((Real.sqrt (1+v))⁻¹*Real.exp (-c/2+z^2/(2*(1+v))))*
        gaussianPDFReal (z/(1+v)) (NNReal.mk (1/(1+v)) (by positivity)) u := by
  have hn : 1+v ≠ 0 := by linarith
  have hexp : -(u-z/(1+v))^2/(2*(1/(1+v))) =
      -(1+v)*(u-z/(1+v))^2/2 := by
    field_simp [hn]
    <;> ring
  simp only [gaussianPDFReal,NNReal.coe_one,NNReal.coe_mk,mul_one,sub_zero]
  rw [mul_assoc,← Real.exp_add,square_completion c z v u hv,hexp,prefactor v hv]
  rw [sub_eq_add_neg,Real.exp_add]
  ring

theorem gaussian_quadratic_integral (c z v : ℝ) (hv : 0 ≤ v) :
    (∫ u,Real.exp (quadraticScore c z v u) ∂gaussianReal 0 1) =
      Real.exp (mixtureExpression c z v) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  simp_rw [mixture_density_identity c z v _ hv]
  rw [integral_const_mul,integral_gaussianPDFReal_eq_one]
  · rw [mul_one]
    have hh : Real.exp (-(Real.log (1+v)/2))=(Real.sqrt (1+v))⁻¹ := by
      rw [Real.exp_neg,Real.exp_half,Real.exp_log (by linarith)]
    have he : mixtureExpression c z v=-(Real.log (1+v)/2)+(-c/2+z^2/(2*(1+v))) := by
      unfold mixtureExpression; ring
    rw [he,Real.exp_add (-(Real.log (1+v)/2)) (-c/2+z^2/(2*(1+v))),hh]
  · apply ne_of_gt
    change 0 < 1/(1+v)
    positivity

#print axioms square_completion
#print axioms mixture_density_identity
#print axioms gaussian_quadratic_integral
end
end CIGAMF.P13.D6GaussianMixtureIntegral
