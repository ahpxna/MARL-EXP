import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic

/-! Continuous common-density risk and exact overlap of the actual unit-variance
Gaussian laws. No adaptive-transcript comparison or D6 oracle optimality is
assumed proved by this module. -/
namespace CIGAMF.P13.D6GaussianOverlap
open ProbabilityTheory MeasureTheory Set
noncomputable section

/-- The right tail of the actual standard Gaussian probability measure. -/
def standardTail (a : ℝ) : ℝ := (gaussianReal 0 1 (Ioi a)).toReal

lemma pdf_reflection (a x : ℝ) :
    gaussianPDFReal a 1 x = gaussianPDFReal (-a) 1 (-x) := by
  have h : -(x-a)^2/(2*(↑(1 : NNReal) : ℝ)) =
      -((-x)-(-a))^2/(2*(↑(1 : NNReal) : ℝ)) := by ring
  simp only [gaussianPDFReal,h]

lemma pdf_left_le_right {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    gaussianPDFReal (-a) 1 x ≤ gaussianPDFReal a 1 x := by
  unfold gaussianPDFReal
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [mul_nonneg ha hx]
  · positivity

/-- The smaller Gaussian density is the density with mean -a at |x|. -/
theorem gaussian_min_density (a : ℝ) (ha : 0 ≤ a) (x : ℝ) :
    min (gaussianPDFReal (-a) 1 x) (gaussianPDFReal a 1 x) =
      gaussianPDFReal (-a) 1 |x| := by
  by_cases hx : 0 ≤ x
  · rw [min_eq_left (pdf_left_le_right ha hx),abs_of_nonneg hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    have hle : gaussianPDFReal a 1 x ≤ gaussianPDFReal (-a) 1 x := by
      calc
        _ = gaussianPDFReal (-a) 1 (-x) := pdf_reflection a x
        _ ≤ gaussianPDFReal a 1 (-x) := pdf_left_le_right ha (by linarith)
        _ = gaussianPDFReal (-a) 1 x := by simpa using pdf_reflection a (-x)
    rw [min_eq_right hle,abs_of_neg hx',pdf_reflection a x]

lemma shifted_half_mass (a : ℝ) :
    gaussianReal (-a) 1 (Ioi 0) = gaussianReal 0 1 (Ioi a) := by
  have hm := congrArg (fun μ : Measure ℝ => μ (Ioi (0 : ℝ)))
    (gaussianReal_map_sub_const (μ := 0) (v := 1) a)
  rw [Measure.map_apply (by fun_prop) measurableSet_Ioi] at hm
  have hp : (fun x : ℝ => x-a) ⁻¹' Ioi 0 = Ioi a := by
    ext x
    simp only [mem_preimage,mem_Ioi]
    constructor <;> intro h <;> linarith
  simpa only [hp,zero_sub] using hm.symm

/-- Exact overlap, expressed using a probability tail rather than a formal symbol. -/
theorem gaussian_overlap (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, min (gaussianPDFReal (-a) 1 x) (gaussianPDFReal a 1 x)) =
      2 * standardTail a := by
  simp_rw [gaussian_min_density a ha]
  rw [integral_comp_abs]
  have hm := gaussianReal_apply_eq_integral (-a) (v := 1) (by norm_num) (Ioi 0)
  rw [shifted_half_mass] at hm
  have hi : 0 ≤ ∫ x in Ioi (0 : ℝ), gaussianPDFReal (-a) 1 x :=
    integral_nonneg (gaussianPDFReal_nonneg (-a) 1)
  have ht := congrArg ENNReal.toReal hm
  rw [ENNReal.toReal_ofReal hi] at ht
  exact congrArg (fun t : ℝ => 2*t) ht.symm

/-- Continuous analogue of the finite common-part risk inequality. -/
theorem common_density_risk_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (pminus pplus lossminus lossplus : Ω → ℝ) (separation : ℝ)
    (hpm : Integrable pminus μ) (hpp : Integrable pplus μ)
    (hrm : Integrable (fun x => pminus x*lossminus x) μ)
    (hrp : Integrable (fun x => pplus x*lossplus x) μ)
    (pm : ∀ x, 0 ≤ pminus x) (pp : ∀ x, 0 ≤ pplus x)
    (lm : ∀ x, 0 ≤ lossminus x) (lp : ∀ x, 0 ≤ lossplus x)
    (sep : ∀ x, separation ≤ lossminus x+lossplus x) :
    separation*(∫ x, min (pminus x) (pplus x) ∂μ) ≤
      (∫ x, pminus x*lossminus x ∂μ)+(∫ x, pplus x*lossplus x ∂μ) := by
  rw [← integral_const_mul,← integral_add hrm hrp]
  apply integral_mono ((hpm.inf hpp).const_mul separation) (hrm.add hrp)
  intro x
  change separation*min (pminus x) (pplus x) ≤
    pminus x*lossminus x+pplus x*lossplus x
  have hmin : 0 ≤ min (pminus x) (pplus x) := le_min (pm x) (pp x)
  have hs := mul_le_mul_of_nonneg_right (sep x) hmin
  have hm := mul_le_mul_of_nonneg_right (min_le_left (pminus x) (pplus x)) (lm x)
  have hp := mul_le_mul_of_nonneg_right (min_le_right (pminus x) (pplus x)) (lp x)
  nlinarith

/-- A separated pair of nonnegative losses has Gaussian max-risk at least
separation times the exact standard Gaussian tail. -/
theorem gaussian_max_risk_lower (a : ℝ) (ha : 0 ≤ a)
    (lossminus lossplus : ℝ → ℝ) (separation : ℝ)
    (hrm : Integrable (fun x => gaussianPDFReal (-a) 1 x*lossminus x))
    (hrp : Integrable (fun x => gaussianPDFReal a 1 x*lossplus x))
    (lm : ∀ x, 0 ≤ lossminus x) (lp : ∀ x, 0 ≤ lossplus x)
    (sep : ∀ x, separation ≤ lossminus x+lossplus x) :
    separation*standardTail a ≤
      max (∫ x, gaussianPDFReal (-a) 1 x*lossminus x)
        (∫ x, gaussianPDFReal a 1 x*lossplus x) := by
  have hb := common_density_risk_lower volume (gaussianPDFReal (-a) 1)
    (gaussianPDFReal a 1) lossminus lossplus separation
    (integrable_gaussianPDFReal (-a) 1) (integrable_gaussianPDFReal a 1)
    hrm hrp (gaussianPDFReal_nonneg (-a) 1) (gaussianPDFReal_nonneg a 1) lm lp sep
  rw [gaussian_overlap a ha] at hb
  have hm := le_max_left (∫ x, gaussianPDFReal (-a) 1 x*lossminus x)
    (∫ x, gaussianPDFReal a 1 x*lossplus x)
  have hp := le_max_right (∫ x, gaussianPDFReal (-a) 1 x*lossminus x)
    (∫ x, gaussianPDFReal a 1 x*lossplus x)
  linarith

#print axioms gaussian_min_density
#print axioms gaussian_overlap
#print axioms common_density_risk_lower
#print axioms gaussian_max_risk_lower
end
end CIGAMF.P13.D6GaussianOverlap
