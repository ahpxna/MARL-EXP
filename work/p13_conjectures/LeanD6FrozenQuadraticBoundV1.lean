import «LeanD6FrozenOracleGapV1»
import «LeanD6PhaseShiftLipschitzV1»
import «LeanD6FrozenAllocationFeasibleV1»

/-! Explicit quadratic oracle regret of the boundary-frozen phase-III design.
All-alternative feasibility is discharged, and the remainder constant is an
explicit function of the design margin and q, independent of sample size. -/
namespace CIGAMF.P13.D6FrozenQuadraticBound
open MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6FrozenScalarAllocation CIGAMF.P13.D6FrozenOracleGap
open CIGAMF.P13.D6PhaseShiftLipschitz CIGAMF.P13.D6FrozenAllocationFeasible
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6PhaseThreePrimal
noncomputable section
variable {n : ℕ}

def combinedModulus (q mu0 : ℝ) := shiftModulus q mu0+
    |mass q mu0*(q-2)/coefficient q (mass q mu0)|
def remainderConstant (q mu0 : ℝ) := coefficient q (mass q mu0)*(combinedModulus q mu0)^2/2

lemma modulus_nonnegative (q mu0 : ℝ) (hq : 3 ≤ q) (hm0 : 0 < mu0) :
    0 ≤ combinedModulus q mu0 := by
  have hk := K_pos q hq
  have hd := radical_positive q mu0 hq hm0
  have ha : 0 ≤ q*(q-1) := mul_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ q*(q-2) := mul_nonneg (by linarith) (by linarith)
  unfold combinedModulus shiftModulus radicalModulus
  positivity

lemma nuisance_displacement_bound (q mu mu0 eps : ℝ) (hq : 3 ≤ q)
    (hm : 0 < mu) (hm1 : mu ≤ 1) (hm0 : 0 < mu0) (hm01 : mu0 ≤ 1)
    (hc : coefficient q (mass q mu0) ≠ 0) (heps : 0 ≤ eps) (he : |mu-mu0| ≤ eps) :
    |shift q mu-delta q (mass q mu0) mu| ≤ combinedModulus q mu0*eps := by
  have hshift := shift_lipschitz q mu mu0 eps hq hm hm1 hm0 hm01 heps he
  have hanchor := frozen_shift_at_design q mu0 hq hm0 hm01 hc
  have hdiff : delta q (mass q mu0) mu0-delta q (mass q mu0) mu=
      (mass q mu0*(q-2)/coefficient q (mass q mu0))*(mu-mu0) := by unfold delta; ring
  have htriangle := abs_add_le (shift q mu-shift q mu0)
    (delta q (mass q mu0) mu0-delta q (mass q mu0) mu)
  rw [hanchor] at htriangle
  have heq : shift q mu-shift q mu0+(shift q mu0-delta q (mass q mu0) mu)=
      shift q mu-delta q (mass q mu0) mu := by ring
  rw [heq] at htriangle
  have hsmall : |shift q mu0-delta q (mass q mu0) mu| ≤
      |mass q mu0*(q-2)/coefficient q (mass q mu0)| *eps := by
    rw [← hanchor,hdiff,abs_mul]
    exact mul_le_mul_of_nonneg_left he (abs_nonneg _)
  unfold combinedModulus
  nlinarith only [htriangle,hshift,hsmall]

/-- All premises describe the actual phase interval, label cardinalities and
margin distance. No oracle-gap, alternative guard or statistical conclusion
appears among them. -/
theorem actual_frozen_quadratic_regret (A : Finset (I n)) (j : I n)
    (q mu mu0 eps : ℝ) (hq : 3 ≤ q)
    (hmlo : marginMax q ≤ mu) (hmhi : mu ≤ marginHigh q)
    (h0lo : marginMax q ≤ mu0) (h0hi : mu0 ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (heps : 0 ≤ eps) (he : |mu-mu0| ≤ eps) :
    oracleRegret A j q mu (queries A j) (weights A j q (mass q mu0)) ≤
      remainderConstant q mu0*eps^2 := by
  have hm := phase_shift_bounds q mu hq hmlo hmhi
  have h0 := phase_shift_bounds q mu0 hq h0lo h0hi
  have hw := phase_mass_bounds q mu0 hq h0lo h0hi
  have hc := frozen_coefficients q (mass q mu0) hq hw.1 hw.2
  have hf := frozen_half_interval_conditions q (mass q mu0) mu hq hw.1 hw.2 hm.1 hm.2.1
  rw [actual_frozen_oracle_gap A j q (mass q mu0) mu hq hmlo hmhi hw.1
    (by linarith [hw.2]) hc.1 hj hA hB hf.1 hf.2.1 hf.2.2]
  have hd := nuisance_displacement_bound q mu mu0 eps hq (by linarith [hm.1]) hm.2.1
    (by linarith [h0.1]) h0.2.1 (ne_of_gt hc.1) heps he
  have hmod := modulus_nonnegative q mu0 hq (by linarith [h0.1])
  have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hmod heps)).mpr hd
  rw [sq_abs,mul_pow] at hs
  have ht := mul_le_mul_of_nonneg_left hs hc.1.le
  unfold remainderConstant
  nlinarith only [ht]

#print axioms nuisance_displacement_bound
#print axioms actual_frozen_quadratic_regret
end
end CIGAMF.P13.D6FrozenQuadraticBound
