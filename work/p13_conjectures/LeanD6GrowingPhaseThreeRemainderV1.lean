import «LeanD6UniformPhaseThreeRemainderV1»

/-! A quantitative version of the compactness bound: for q>=8 the existing
explicit phase-III remainder is at most 64/q^2. This is an upper bound, not a
claim that 64 is sharp. It permits growing-q use without an unspecified C(q). -/
namespace CIGAMF.P13.D6GrowingPhaseThreeRemainder
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6FrozenAllocationFeasible
open CIGAMF.P13.D6PhaseShiftLipschitz CIGAMF.P13.D6FrozenQuadraticBound
open CIGAMF.P13.D6UniformPhaseThreeRemainder
noncomputable section

lemma K_bounds (q : ℝ) (hq : 8 ≤ q) : q^3/2 ≤ K q ∧ 4*q^2 ≤ K q ∧ K q ≤ q^3 := by
  have h := mul_nonneg (show 0 ≤ q-8 by linarith) (sq_nonneg q)
  unfold K
  constructor
  · nlinarith
  constructor <;> nlinarith [sq_nonneg (q-1)]

lemma radical_ge_q (q mu : ℝ) (hq : 8 ≤ q) (hm : mu ∈ phaseInterval q) : q ≤ D q mu := by
  have hb := phase_shift_bounds q mu (by linarith) hm.1 hm.2
  have hk := K_bounds q hq
  have hd := radical_positive q mu (by linarith) (by linarith [hb.1])
  have hs := radical_square q mu (by linarith)
  have hp : 0 ≤ q*(q-1)*(1-mu)^2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hx : 0 ≤ K q*(mu^2-1/4) := mul_nonneg (by linarith [hk.2.1]) (by nlinarith [hb.1])
  unfold radicand at hs
  nlinarith

lemma shift_modulus_scaled (q mu : ℝ) (hq : 8 ≤ q) (hm : mu ∈ phaseInterval q) :
    q*shiftModulus q mu ≤ 6 := by
  have hk := K_bounds q hq
  have hkp := K_pos q (by linarith)
  have hd := radical_ge_q q mu hq hm
  have hrad : radicalModulus q mu ≤ 2*q^2+2*q := by
    unfold radicalModulus
    apply (div_le_iff₀ (by linarith : 0 < D q mu)).mpr
    have hp := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2*q^2+2*q by positivity)
    nlinarith [hk.2.2]
  unfold shiftModulus
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hkp).mpr
  have hh := mul_le_mul_of_nonneg_left hrad (show 0 ≤ q by linarith)
  nlinarith [hk.1]

lemma mass_scaled (q mu : ℝ) (hq : 8 ≤ q) (hm : mu ∈ phaseInterval q) :
    mass q mu*(q-2)^2 ≤ 1 := by
  have hb := phase_shift_bounds q mu (by linarith) hm.1 hm.2
  have hk := K_bounds q hq
  have he := rationalized_shift q mu (by linarith) (by linarith [hb.1]) hb.2.1
  have hd := radical_positive q mu (by linarith) (by linarith [hb.1])
  have ht := mul_le_mul_of_nonneg_left hb.2.2.2 (show 0 ≤ q*(q-2) from mul_nonneg (by linarith) (by linarith))
  have hp : (q-1)*(q-2)^2+K q ≤ 4*q^2*(q-2) := by
    have h := mul_nonneg (show 0 ≤ q-8 by linarith) (sq_nonneg q)
    nlinarith [hk.2.2,sq_nonneg (q-2)]
  have hh := mul_le_mul_of_nonneg_right hp hb.2.2.1
  unfold mass
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  nlinarith [he,ht,hh]

lemma coefficient_le_two (q mu : ℝ) (hq : 8 ≤ q) (hm : mu ∈ phaseInterval q) :
    coefficient q (mass q mu) ≤ 2 := by
  have hw := phase_mass_bounds q mu (by linarith) hm.1 hm.2
  have hh := mass_scaled q mu hq hm
  have hs : (1-mass q mu)*(q-1)/q ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < q)).mpr
    have hn := mul_nonneg hw.1 (show 0 ≤ q-1 by linarith)
    nlinarith
  unfold coefficient
  linarith

lemma combined_modulus_scaled (q mu : ℝ) (hq : 8 ≤ q) (hm : mu ∈ phaseInterval q) :
    q*combinedModulus q mu ≤ 8 := by
  have hw := phase_mass_bounds q mu (by linarith) hm.1 hm.2
  have hc := frozen_coefficients q (mass q mu) (by linarith) hw.1 hw.2
  have hs := shift_modulus_scaled q mu hq hm
  have hp : mass q mu*(q-2)^2 ≤ coefficient q (mass q mu) := by
    unfold coefficient
    have hh : 0 ≤ (1-mass q mu)*(q-1)/q := by
      exact div_nonneg (mul_nonneg (by linarith [hw.2]) (by linarith)) (by linarith)
    linarith
  have he : q*(mass q mu*(q-2)/coefficient q (mass q mu)) ≤ 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hc.1).mpr
    have hn := mul_nonneg (mul_nonneg hw.1 (show 0 ≤ q-2 by linarith)) (show 0 ≤ q-4 by linarith)
    nlinarith
  have hn : 0 ≤ mass q mu*(q-2)/coefficient q (mass q mu) :=
    div_nonneg (mul_nonneg hw.1 (by linarith)) hc.1.le
  unfold combinedModulus
  rw [abs_of_nonneg hn]
  linarith

/-- Uniform in both q>=8 and the entire phase-III design interval. -/
theorem remainder_scaled (q mu : ℝ) (hq : 8 ≤ q) (hm : mu ∈ phaseInterval q) :
    remainderConstant q mu ≤ 64/q^2 := by
  have hb := phase_shift_bounds q mu (by linarith) hm.1 hm.2
  have hmod := modulus_nonnegative q mu (by linarith) (by linarith [hb.1])
  have hscaled := combined_modulus_scaled q mu hq hm
  have hcoeff := coefficient_le_two q mu hq hm
  have hw := phase_mass_bounds q mu (by linarith) hm.1 hm.2
  have hc := (frozen_coefficients q (mass q mu) (by linarith) hw.1 hw.2).1
  have hs : (q*combinedModulus q mu)^2 ≤ 64 := by
    have hp : 0 ≤ q*combinedModulus q mu := by positivity
    nlinarith
  have ht := mul_le_mul_of_nonneg_left hs hc.le
  unfold remainderConstant
  apply (le_div_iff₀ (by positivity : 0 < q^2)).mpr
  rw [mul_pow] at ht
  nlinarith

#print axioms K_bounds
#print axioms radical_ge_q
#print axioms shift_modulus_scaled
#print axioms mass_scaled
#print axioms coefficient_le_two
#print axioms combined_modulus_scaled
#print axioms remainder_scaled
end
end CIGAMF.P13.D6GrowingPhaseThreeRemainder
