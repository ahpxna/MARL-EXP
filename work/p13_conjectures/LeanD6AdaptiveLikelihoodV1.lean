import «LeanD6AdaptiveTranscriptV1»
import «LeanD6MovingNuisanceRegretV1»
import Mathlib.Probability.Distributions.Gaussian.Basic

/-! Actual Gaussian likelihood increments and finite adaptive normalization.
The update identity is explicit: a likelihood state multiplies by the ratio
for the query chosen from its current history. This is the probability-side
foundation for a later mixture stopping theorem, not that theorem itself. -/
namespace CIGAMF.P13.D6AdaptiveLikelihood
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6MovingNuisanceRegret
open CIGAMF.P13.D6AdaptiveTranscript CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section

/-- Candidate-to-true Gaussian likelihood ratio. -/
def likelihood (m v y : ℝ) := Real.exp ((v-m)*y+(m^2-v^2)/2)

lemma likelihood_factor (m v y : ℝ) :
    likelihood m v y=Real.exp ((m^2-v^2)/2)*Real.exp ((v-m)*y) := by
  rw [likelihood,Real.exp_add]
  ring

lemma likelihood_integrable (m v : ℝ) :
    Integrable (likelihood m v) (gaussianReal m 1) := by
  change Integrable (fun y => likelihood m v y) (gaussianReal m 1)
  simp_rw [likelihood_factor]
  exact (integrable_exp_mul_gaussianReal (v-m)).const_mul _

theorem gaussian_likelihood_mean_one (m v : ℝ) :
    (∫ y,likelihood m v y ∂gaussianReal m 1)=1 := by
  simp_rw [likelihood_factor]
  rw [integral_const_mul]
  have hg : (∫ y : ℝ,Real.exp ((v-m)*y) ∂gaussianReal m 1) =
      Real.exp (m*(v-m)+(v-m)^2/2) := by
    simpa only [mgf,NNReal.coe_one,one_mul] using
      congrFun (mgf_fun_id_gaussianReal (μ := m) (v := 1)) (v-m)
  rw [hg,← Real.exp_add]
  have he : (m^2-v^2)/2+(m*(v-m)+(v-m)^2/2)=0 := by ring
  rw [he,Real.exp_zero]

theorem gaussian_likelihood_lintegral (m v : ℝ) :
    (∫⁻ y,ENNReal.ofReal (likelihood m v y) ∂gaussianReal m 1)=1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (likelihood_integrable m v)
    (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le)),
    gaussian_likelihood_mean_one]
  norm_num

theorem gaussian_log_likelihood_mean (m v : ℝ) :
    (∫ y,Real.log (likelihood m v y) ∂gaussianReal m 1)=-(m-v)^2/2 := by
  have hi : Integrable (fun y : ℝ => y) (gaussianReal m 1) := IsGaussian.integrable_id
  simp only [likelihood,Real.log_exp]
  rw [integral_add (hi.const_mul _) (integrable_const _),integral_const_mul,
    integral_id_gaussianReal,integral_const]
  simp only [probReal_univ,one_smul]
  ring

/-- The squared-world-mean information already used by the allocation game is
exactly expected negative log likelihood for the actual Gaussian response. -/
theorem actual_information_log_likelihood {n : ℕ} (A A' : Finset (I n))
    (j : I n) (mu nu : ℝ) (e : Measurement n) :
    -(∫ y,Real.log (likelihood (actualMean A j mu e) (actualMean A' j nu e) y)
      ∂gaussianReal (actualMean A j mu e) 1)=information A A' j mu nu e := by
  rw [gaussian_log_likelihood_mean,information_eq_mean]
  ring

variable {H : Type*} [MeasurableSpace H]

theorem actual_step_preserves_likelihood (m v : H → ℝ) (hm : Measurable m)
    (update : H × ℝ → H) (hu : Measurable update)
    (L L' : H → ℝ) (hL' : Measurable L') (hL : ∀ h,0 ≤ L h)
    (transition : ∀ h y,L' (update (h,y))=L h*likelihood (m h) (v h) y) (h : H) :
    (∫⁻ h',ENNReal.ofReal (L' h') ∂actualStep m hm update hu h)=ENNReal.ofReal (L h) := by
  rw [actualStep_apply,lintegral_map (by fun_prop) (by fun_prop)]
  simp_rw [transition,ENNReal.ofReal_mul (hL h)]
  rw [lintegral_const_mul _ (by unfold likelihood; fun_prop),gaussian_likelihood_lintegral,mul_one]

/-- Exact normalization across the full adaptive state law, allowing different
true/candidate means at each state and retaining the entire likelihood record. -/
theorem adaptive_likelihood_normalization
    (initial : Kernel Unit H) (m v : ℕ → H → ℝ) (hm : ∀ t,Measurable (m t))
    (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (L : ℕ → H → ℝ) (hLm : ∀ t,Measurable (L t)) (hL : ∀ t h,0 ≤ L t h)
    (hinit : (∫⁻ h,ENNReal.ofReal (L 0 h) ∂initial ())=1)
    (transition : ∀ t h y,L (t+1) (update t (h,y))=
      L t h*likelihood (m t h) (v t h) y) (N : ℕ) :
    (∫⁻ h,ENNReal.ofReal (L N h)
      ∂trajectory initial (fun t => actualStep (m t) (hm t) (update t) (hu t)) N ())=1 := by
  induction N with
  | zero => exact hinit
  | succ N ih =>
    rw [trajectory,Kernel.lintegral_comp _ _ _ (by fun_prop)]
    simp_rw [actual_step_preserves_likelihood (m N) (v N) (hm N) (update N) (hu N)
      (L N) (L (N+1)) (hLm (N+1)) (hL N) (transition N)]
    exact ih

#print axioms gaussian_likelihood_mean_one
#print axioms gaussian_likelihood_lintegral
#print axioms gaussian_log_likelihood_mean
#print axioms actual_information_log_likelihood
#print axioms actual_step_preserves_likelihood
#print axioms adaptive_likelihood_normalization
end
end CIGAMF.P13.D6AdaptiveLikelihood
