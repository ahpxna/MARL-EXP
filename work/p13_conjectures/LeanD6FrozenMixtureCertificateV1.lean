import «LeanD6ActualRecordLikelihoodV1»
import «LeanD6GaussianMixtureIntegralV1»
import Mathlib.Data.List.OfFn

/-! A likelihood-mixture certificate has an unconditional finite-horizon
error bound on the actual absorbing record process. It uses no known A in
its stopping rule. Nontermination is not counted as successful output. -/
namespace CIGAMF.P13.D6FrozenMixtureCertificate
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6AdaptiveTranscript
open CIGAMF.P13.D6AdaptiveMixtureRisk CIGAMF.P13.D6StoppingGeometryBridge
open CIGAMF.P13.D6ActualRecordLikelihood CIGAMF.P13.AdaptiveTranscriptKernel
open CIGAMF.P13.D6UniqueOptimum CIGAMF.P13.D6Geometry
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {H : Type*} [MeasurableSpace H]

def absoluteMixture (prior : Measure ℝ) (B : Finset (I n)) (j : I n)
    (record : List (Measurement n × ℝ)) : ENNReal :=
  ∫⁻ nu,ENNReal.ofReal (Real.exp (logLikelihood B j nu record)) ∂prior

def Certificate (prior : Measure ℝ) (W : Finset (Finset (I n))) (j : I n)
    (record : List (Measurement n × ℝ)) (answer : Finset (I n)) (c : ENNReal) : Prop :=
  answer ∈ W ∧ ∀ B ∈ W,B ≠ answer → ∀ nu : ℝ,0 ≤ nu → nu ≤ 1 →
    c*ENNReal.ofReal (Real.exp (logLikelihood B j nu record)) ≤
      absoluteMixture prior answer j record

theorem relative_mixture_factor (prior : Measure ℝ) (A B : Finset (I n)) (j : I n)
    (mu : ℝ) (record : List (Measurement n × ℝ)) :
    (∫⁻ nu,ENNReal.ofReal (recordRatio A B j mu nu record) ∂prior)=
      absoluteMixture prior B j record*ENNReal.ofReal (Real.exp (-logLikelihood A j mu record)) := by
  have he : ∀ nu,ENNReal.ofReal (recordRatio A B j mu nu record)=
      ENNReal.ofReal (Real.exp (logLikelihood B j nu record))*
        ENNReal.ofReal (Real.exp (-logLikelihood A j mu record)) := by
    intro nu
    rw [recordRatio,sub_eq_add_neg,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
  simp_rw [he]
  exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top

lemma exp_cancel (s : ℝ) : ENNReal.ofReal (Real.exp s)*ENNReal.ofReal (Real.exp (-s))=1 := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  simp

/-- A wrong certified label forces an actual relative-mixture threshold
crossing, including all admissible nuisance alternatives. -/
theorem wrong_certificate_crosses (prior : Measure ℝ) (W : Finset (Finset (I n)))
    (A answer : Finset (I n)) (j : I n) (mu : ℝ) (hA : A ∈ W)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (record : List (Measurement n × ℝ))
    (c : ENNReal) (hcert : Certificate prior W j record answer c) (hne : answer ≠ A) :
    c ≤ ∫⁻ nu,ENNReal.ofReal (recordRatio A answer j mu nu record) ∂prior := by
  have h := hcert.2 A hA (Ne.symm hne) mu hmu hmu1
  have hh := mul_le_mul_of_nonneg_right h (show 0 ≤ ENNReal.ofReal (Real.exp (-logLikelihood A j mu record)) from zero_le)
  rw [mul_assoc,exp_cancel,mul_one] at hh
  rwa [relative_mixture_factor]

/-- No external probability event is assumed: the bound follows from actual
Gaussian transitions, the retained record, and the displayed stopping rule. -/
theorem actual_frozen_label_error (A : Finset (I n)) (j : I n) (mu : ℝ)
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (record : H → List (Measurement n × ℝ)) (policy : ℕ → H → Measurement n)
    (hm : ∀ t,Measurable (fun h => actualMean A j mu (policy t h)))
    (stopped : H → Prop) (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (hrecord : ∀ t h y,record (update t (h,y))=
      if stopped h then record h else (policy t h,y)::record h)
    (hempty : ∀ᵐ h ∂initial (),record h=[])
    (htrue : Measurable (fun h => logLikelihood A j mu (record h)))
    (prior : Measure ℝ) [IsProbabilityMeasure prior] (W : Finset (Finset (I n)))
    (hcandidate : ∀ B ∈ W,Measurable (fun x : H × ℝ => logLikelihood B j x.2 (record x.1)))
    (answer : H → Finset (I n)) (hA : A ∈ W) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (c : ENNReal) (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (hcert : ∀ h,stopped h → Certificate prior W j (record h) (answer h) c) (N : ℕ) :
    trajectory initial (fun t => actualStep (fun h => actualMean A j mu (policy t h))
      (hm t) (update t) (hu t)) N () {h | stopped h ∧ answer h ≠ A} ≤ (W.card:ENNReal)/c := by
  apply le_trans (measure_mono ?_) (actual_frozen_family_tail A j mu initial record policy hm
    stopped update hu hrecord hempty htrue prior W hcandidate c hc hc' N)
  rintro h ⟨hs,hne⟩
  exact ⟨answer h,(hcert h hs).1,wrong_certificate_crosses prior W A (answer h) j mu
    hA hmu hmu1 (record h) c (hcert h hs) hne⟩

/-- Exact threshold calibration, including nonempty candidate families. -/
theorem delta_calibration (W : Finset (Finset (I n))) (hW : W.Nonempty)
    (delta : ENNReal) (hd : delta ≠ 0) (hdt : delta ≠ ⊤) :
    (W.card:ENNReal)/delta ≠ 0 ∧ (W.card:ENNReal)/delta ≠ ⊤ ∧
      (W.card:ENNReal)/((W.card:ENNReal)/delta)=delta := by
  have hk : (W.card:ENNReal) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hW)
  exact ⟨ENNReal.div_ne_zero.mpr ⟨hk,hdt⟩,
    ENNReal.div_ne_top (by simp) hd,ENNReal.div_div_cancel hk (by simp)⟩

/-- The probability of a wrong literal support-geometric answer is bounded
by the label-error probability; never-stopped runs stay outside both events. -/
theorem geometric_error_le_label_error (P : Measure H) (r : ℕ) (j : I (2*r+1))
    (hr : 2 ≤ r) (A : Finset (I (2*r+1))) (hA : A ∈ worlds r j)
    (mu : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (stopped : H → Prop) (answer : H → Finset (I (2*r+1))) :
    P {h | stopped h ∧ ¬GeometricOptimal A (answer h)ᶜ j mu} ≤
      P {h | stopped h ∧ answer h ≠ A} := by
  apply measure_mono
  rintro h ⟨hs,hbad⟩
  refine ⟨hs,?_⟩
  intro he
  apply hbad
  rw [he]
  have hp := world_parameters r j hr hA
  exact (geometric_optimal_iff A Aᶜ j hp.1 mu hmu hmu1 hp.2.2.1 hp.2.2.1 hp.2.2.2).mpr rfl

#print axioms relative_mixture_factor
#print axioms wrong_certificate_crosses
#print axioms actual_frozen_label_error
#print axioms delta_calibration
#print axioms geometric_error_le_label_error
end
end CIGAMF.P13.D6FrozenMixtureCertificate

/-! The quadratic profile-gap rule in the experiment implies the actual
record-mixture certificate. The Gaussian nuisance integral is evaluated,
rather than assumed equal to its computational expression. -/
namespace CIGAMF.P13.D6ProfileMixtureCertificate
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6StoppingGeometryBridge
open CIGAMF.P13.D6ProfileStoppingGeometry CIGAMF.P13.D6GaussianMixtureIntegral
open CIGAMF.P13.D6FrozenMixtureCertificate
noncomputable section
variable {n N : ℕ}

theorem finite_record_score (e : Fin N → Measurement n) (y : Fin N → ℝ)
    (B : Finset (I n)) (j : I n) (nu : ℝ) :
    logLikelihood B j nu (List.ofFn (fun t => (e t,y t)))=score Finset.univ e y B j nu := by
  simp [logLikelihood,score,List.sum_ofFn,Function.comp_def]

theorem finite_record_mixture (e : Fin N → Measurement n) (y : Fin N → ℝ)
    (B : Finset (I n)) (j : I n) (q : ℝ) (hj : j ∉ B) (hl : ∀ t,Legal j q (e t)) :
    absoluteMixture (gaussianReal 0 1) B j (List.ofFn (fun t => (e t,y t)))=
      ENNReal.ofReal (Real.exp (mixtureExpression (C Finset.univ e y B j)
        (Z Finset.univ e y B j) (V Finset.univ e B j))) := by
  have he : ∀ nu,logLikelihood B j nu (List.ofFn (fun t => (e t,y t)))=
      quadraticScore (C Finset.univ e y B j) (Z Finset.univ e y B j) (V Finset.univ e B j) nu := by
    intro nu
    rw [finite_record_score]
    exact actual_score_quadratic Finset.univ e y B j nu q hj (fun t _ => hl t)
  have hv : 0 ≤ V Finset.univ e B j := by unfold V; positivity
  have hmeas : Measurable (fun nu => Real.exp (quadraticScore (C Finset.univ e y B j)
      (Z Finset.univ e y B j) (V Finset.univ e B j) nu)) := by unfold quadraticScore; fun_prop
  have hi : Integrable (fun nu => Real.exp (quadraticScore (C Finset.univ e y B j)
      (Z Finset.univ e y B j) (V Finset.univ e B j) nu)) (gaussianReal 0 1) := by
    apply (integrable_const (1:ℝ)).mono' hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro nu
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
    rw [← he nu]
    exact likelihood_nonpositive B j nu _
  unfold absoluteMixture
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
    gaussian_quadratic_integral _ _ _ hv]

/-- The implemented profile penalty gives a concrete, truth-independent
certificate at threshold exp(threshold), for every candidate alternative. -/
theorem profile_stop_certificate (e : Fin N → Measurement n) (y : Fin N → ℝ)
    (W : Finset (Finset (I n))) (answer : Finset (I n)) (j : I n)
    (q muhat threshold : ℝ) (hanswer : answer ∈ W) (hj : j ∉ answer)
    (hl : ∀ t,Legal j q (e t)) (hv : 0 < V Finset.univ e answer j)
    (hstop : ∀ B ∈ W,B ≠ answer → ∀ nu : ℝ,0 ≤ nu → nu ≤ 1 →
      threshold+profilePenalty (Z Finset.univ e y answer j) (V Finset.univ e answer j) ≤
        score Finset.univ e y answer j muhat-score Finset.univ e y B j nu) :
    Certificate (gaussianReal 0 1) W j (List.ofFn (fun t => (e t,y t))) answer
      (ENNReal.ofReal (Real.exp threshold)) := by
  refine ⟨hanswer,?_⟩
  intro B hB hne nu hn hn1
  have hs := hstop B hB hne nu hn hn1
  have hp := actual_profile_majorant Finset.univ e y answer j muhat q hj (fun t _ => hl t) hv
  rw [finite_record_mixture e y answer j q hj hl,finite_record_score]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  linarith only [hs,hp]

#print axioms finite_record_score
#print axioms finite_record_mixture
#print axioms profile_stop_certificate
end
end CIGAMF.P13.D6ProfileMixtureCertificate
