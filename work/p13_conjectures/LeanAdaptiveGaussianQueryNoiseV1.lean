import «LeanD6AdaptiveLikelihoodV1»

/-! Concentration for the noise accumulated by one predictably selected query.
Normalization is proved from actual adaptive Gaussian transitions, including
random counts. No independence of the selected observations is assumed. -/
namespace CIGAMF.P13.AdaptiveGaussianQueryNoise
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6AdaptiveLikelihood CIGAMF.P13.D6AdaptiveTranscript
open CIGAMF.P13.AdaptiveTranscriptKernel
noncomputable section
variable {H : Type*} [MeasurableSpace H]

def exponential (theta count noise : ℝ) := Real.exp (theta*noise-theta^2*count/2)

lemma selected_increment (theta count noise m y : ℝ) (pick : Bool) :
    exponential theta (count+if pick then 1 else 0) (noise+if pick then y-m else 0)=
      exponential theta count noise*likelihood m (m+if pick then theta else 0) y := by
  unfold exponential likelihood
  rw [← Real.exp_add]
  congr 1
  cases pick <;> simp <;> ring

/-- Exact exponential normalization for a query selected from the adaptive
history. The count and residual accumulator are updated only when selected. -/
theorem query_noise_normalization
    (initial : Kernel Unit H) [IsMarkovKernel initial]
    (m : ℕ → H → ℝ) (hm : ∀ t,Measurable (m t))
    (update : ℕ → H × ℝ → H) (hu : ∀ t,Measurable (update t))
    (pick : ℕ → H → Bool) (count noise : ℕ → H → ℝ)
    (hc : ∀ t,Measurable (count t)) (hs : ∀ t,Measurable (noise t))
    (hzero : ∀ᵐ h ∂initial (),count 0 h=0 ∧ noise 0 h=0)
    (hcount : ∀ t h y,count (t+1) (update t (h,y))=count t h+if pick t h then 1 else 0)
    (hnoise : ∀ t h y,noise (t+1) (update t (h,y))=noise t h+if pick t h then y-m t h else 0)
    (theta : ℝ) (N : ℕ) :
    (∫⁻ h,ENNReal.ofReal (exponential theta (count N h) (noise N h))
      ∂trajectory initial (fun t => actualStep (m t) (hm t) (update t) (hu t)) N ())=1 := by
  apply adaptive_likelihood_normalization initial m
    (fun t h => m t h+if pick t h then theta else 0) hm update hu
    (fun t h => exponential theta (count t h) (noise t h))
  · intro t
    unfold exponential
    exact ((measurable_const.mul (hs t)).sub (measurable_const.mul (hc t) |>.div_const 2)).exp
  · intro t h; exact (Real.exp_pos _).le
  · calc
      _ = ∫⁻ _h, (1:ENNReal) ∂initial () := by
        apply lintegral_congr_ae
        filter_upwards [hzero] with h hh
        simp [exponential,hh.1,hh.2]
      _ = 1 := by simp
  · intro t h y
    rw [hcount,hnoise]
    exact selected_increment theta (count t h) (noise t h) (m t h) y (pick t h)

/-- Markov's bound for the normalized exponential, retaining the random count. -/
theorem normalized_exponential_tail (P : Measure H) (count noise : H → ℝ)
    (hc : Measurable count) (hs : Measurable noise) (theta b : ℝ)
    (hn : (∫⁻ h,ENNReal.ofReal (exponential theta (count h) (noise h)) ∂P)=1) :
    P {h | b ≤ theta*noise h-theta^2*count h/2} ≤ 1/ENNReal.ofReal (Real.exp b) := by
  have hm : Measurable (fun h => ENNReal.ofReal (exponential theta (count h) (noise h))) := by
    unfold exponential
    fun_prop
  have hh := meas_ge_le_lintegral_div (μ := P) hm.aemeasurable
    (show ENNReal.ofReal (Real.exp b) ≠ 0 by simp [Real.exp_pos]) ENNReal.ofReal_ne_top
  rw [hn] at hh
  apply le_trans (measure_mono ?_) hh
  intro h he
  change ENNReal.ofReal (Real.exp b) ≤ ENNReal.ofReal (exponential theta (count h) (noise h))
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he)

/-- A count slice has the Gaussian Chernoff exponent despite adaptive selection.
The premise is the exponential identity proved by query_noise_normalization. -/
theorem count_slice_tail (P : Measure H) (count noise : H → ℝ)
    (hc : Measurable count) (hs : Measurable noise) (k x : ℝ) (hk : 0 < k) (hx : 0 ≤ x)
    (hn : ∀ theta,(∫⁻ h,ENNReal.ofReal (exponential theta (count h) (noise h)) ∂P)=1) :
    P {h | count h=k ∧ x ≤ noise h} ≤ 1/ENNReal.ofReal (Real.exp (x^2/(2*k))) := by
  apply le_trans (measure_mono ?_) (normalized_exponential_tail P count noise hc hs (x/k) _ (hn _))
  intro h he
  change x^2/(2*k) ≤ (x/k)*noise h-(x/k)^2*count h/2
  rw [he.1]
  have hm := mul_le_mul_of_nonneg_left he.2 (div_nonneg hx hk.le)
  have hid : (x/k)*x-(x/k)^2*k/2=x^2/(2*k) := by field_simp; ring
  linarith only [hm,hid]

#print axioms selected_increment
#print axioms query_noise_normalization
#print axioms normalized_exponential_tail
#print axioms count_slice_tail
end
end CIGAMF.P13.AdaptiveGaussianQueryNoise
