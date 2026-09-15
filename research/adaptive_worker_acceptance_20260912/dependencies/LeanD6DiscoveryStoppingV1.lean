import «LeanD6DiscoveryVectorCertificateV1»
import «LeanDyadicCertifiedStoppingV1»

/-! Certified discovery: termination, finite expected raw-query cost, and an
unconditional bound on ever certifying a wrong label. No conditioning on earlier
correct estimates and no assumed path law or tail envelope. -/
namespace CIGAMF.P13.D6DiscoveryStopping
open scoped BigOperators ENNReal
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6DiscoveryVectorCertificate
open CIGAMF.P13.D6NuisanceFreeDiscoveryLaw
open CIGAMF.P13.DyadicCertifiedStopping
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

def repetitions (r0 s : ℕ) := r0*2^s

def eta (d r0 : ℕ) : ℝ≥0∞ := ENNReal.ofReal (2*(d:ℝ)*Real.exp (-(r0:ℝ)/128))

def stageAccept (q r0 : ℕ) (s : ℕ) (x : Sample I) : Prop := accepts (repetitions r0 s) q x

def queryCost (q r0 : ℕ) (x : Sample I) : ℝ≥0∞ :=
  (4*Fintype.card I*r0:ℕ)*work (stageAccept q r0) x

lemma dyadic_exp_bound (r0 s : ℕ) (hr0 : 512 ≤ r0) :
    Real.exp (-(repetitions r0 s:ℝ)/128) ≤
      Real.exp (-(r0:ℝ)/128)*(1/4:ℝ)^s := by
  have hr : (512:ℝ) ≤ r0 := by exact_mod_cast hr0
  have hex : Real.exp (-(r0:ℝ)/128) ≤ (1:ℝ)/4 := by
    rw [show -(r0:ℝ)/128 = -((r0:ℝ)/128) by ring,Real.exp_neg]
    have hh : (4:ℝ) ≤ Real.exp ((r0:ℝ)/128) := by
      have ht := Real.add_one_le_exp ((r0:ℝ)/128)
      linarith
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<4) hh
  have hs : (s:ℝ)+1 ≤ (2:ℝ)^s := by exact_mod_cast s.lt_two_pow_self
  calc
    _ ≤ Real.exp (((s:ℝ)+1)*(-(r0:ℝ)/128)) := by
      apply Real.exp_le_exp.mpr
      simp only [repetitions,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      nlinarith
    _ = Real.exp (-(r0:ℝ)/128)^(s+1) := by
      rw [← Real.exp_nat_mul]
      push_cast
      rfl
    _ ≤ Real.exp (-(r0:ℝ)/128)*(1/4:ℝ)^s := by
      rw [pow_succ,mul_comm]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_nonneg _) hex s) (Real.exp_nonneg _)

lemma actual_stage_tail (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i, (∑ t,signs t*means i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) (s : ℕ) :
    vectorPath means (bad B a (repetitions r0 s)) ≤
      eta (Fintype.card I) r0*(4⁻¹:ℝ≥0∞)^s := by
  have hr : 0 < repetitions r0 s := Nat.mul_pos (by omega) (by positivity)
  have hh := vector_tail means B a hm (repetitions r0 s) hr
  have hd := mul_le_mul_of_nonneg_left (dyadic_exp_bound r0 s hr0)
    (by positivity : 0 ≤ 2*(Fintype.card I:ℝ))
  have hreal := hh.trans hd
  have hen := ENNReal.ofReal_le_ofReal hreal
  rw [ofReal_measureReal] at hen
  have he : ENNReal.ofReal (2*(Fintype.card I:ℝ)*(Real.exp (-(r0:ℝ)/128)*(1/4:ℝ)^s)) =
      eta (Fintype.card I) r0*(4⁻¹:ℝ≥0∞)^s := by
    rw [← mul_assoc,ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by norm_num)]
    simp [eta,ENNReal.ofReal_div_of_pos]
  rwa [he] at hen

/-- The stopping event occurs almost surely, including paths with earlier
estimation errors. This theorem is for discovery, not full allocation tracking. -/
theorem discovery_terminates (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i, (∑ t,signs t*means i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    ∀ᵐ x ∂vectorPath means, ∃ s, stageAccept B.card r0 s x := by
  exact almost_sure_termination (vectorPath means) (stageAccept B.card r0)
    (fun s => accepts_measurable _ _) (fun s => bad B a (repetitions r0 s))
    (fun s x hx => good_accepts B a _ x hx) (eta (Fintype.card I) r0)
    ENNReal.ofReal_ne_top (actual_stage_tail means B a hm r0 hr0)

theorem discovery_expected_cost (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i, (∑ t,signs t*means i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,queryCost B.card r0 x ∂vectorPath means) ≤
      (4*Fintype.card I*r0:ℕ)*(1+2*eta (Fintype.card I) r0) := by
  have hh := expected_work_bound (vectorPath means) (stageAccept B.card r0)
    (fun s => accepts_measurable _ _) (fun s => bad B a (repetitions r0 s))
    (fun s x hx => good_accepts B a _ x hx) (eta (Fintype.card I) r0)
    (actual_stage_tail means B a hm r0 hr0)
  unfold queryCost
  have hw : Measurable (work (stageAccept B.card r0) : Sample I → ℝ≥0∞) :=
    work_measurable (stageAccept B.card r0) (fun s => accepts_measurable _ _)
  rw [lintegral_const_mul _ hw]
  exact mul_le_mul le_rfl hh (by positivity) (by positivity)

theorem discovery_expected_cost_finite (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i, (∑ t,signs t*means i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    (∫⁻ x,queryCost B.card r0 x ∂vectorPath means) < ∞ := by
  apply lt_of_le_of_lt (discovery_expected_cost means B a hm r0 hr0)
  dsimp [eta]
  finiteness

/-- This bounds every wrong certificate at every stage, hence also one chosen
at the first acceptance. It does not discard the error on a bad commitment. -/
theorem discovery_ever_wrong (means : I → Fin 4 → ℝ) (B : Finset I) (a : I)
    (hm : ∀ i, (∑ t,signs t*means i t)=target B a i)
    (r0 : ℕ) (hr0 : 512 ≤ r0) :
    vectorPath means (⋃ s, {x | ∃ S, Certified (repetitions r0 s) B.card x S ∧ S ≠ B}) ≤
      eta (Fintype.card I) r0*(1-(4⁻¹:ℝ≥0∞))⁻¹ := by
  apply ever_error_bound (vectorPath means) _ (fun s => bad B a (repetitions r0 s)) _ _
    (actual_stage_tail means B a hm r0 hr0)
  intro s x hx
  obtain ⟨S,hS,hn⟩ := hx
  by_contra hgood
  exact hn (good_certificate_correct B S a _ x hgood hS)

#print axioms actual_stage_tail
#print axioms discovery_terminates
#print axioms discovery_expected_cost
#print axioms discovery_expected_cost_finite
#print axioms discovery_ever_wrong
end
end CIGAMF.P13.D6DiscoveryStopping
