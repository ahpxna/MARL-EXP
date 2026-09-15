import «LeanD6FrozenScalarAllocationV1»
import «LeanD6LocalOracleRegretV1»

/-! Exact oracle penalty for freezing a phase-III allocation. This is the
quadratic remainder needed by a matching local-risk upper bound. -/
namespace CIGAMF.P13.D6FrozenOracleGap
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6FrozenScalarAllocation
open CIGAMF.P13.D6AllocationPhaseThreeParameters CIGAMF.P13.D6PhaseThreePrimal
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6AllocationRiskBridge
noncomputable section
variable {n : ℕ}

lemma balanced_loss (q w mu s : ℝ) (hq : q ≠ 0)
    (balance : q*((1-mu)-(q-2)*s)^2=mu^2+(q-1)*s^2) :
    mixedLoss q mu w 1 ((1-mu)+s)=gammaTwice q mu s := by
  have he := congrArg (fun x : ℝ => w*x) balance
  unfold mixedLoss gammaTwice
  apply (eq_div_iff hq).mpr
  field_simp [hq]
  nlinarith only [he]

/-- Exact regret identity at any balanced oracle nuisance, for an arbitrary
frozen mixture weight. -/
theorem balanced_gap_identity (q w mu s : ℝ) (hq : q ≠ 0)
    (hc : coefficient q w ≠ 0)
    (balance : q*((1-mu)-(q-2)*s)^2=mu^2+(q-1)*s^2) :
    gammaTwice q mu s/2-D6FrozenScalarAllocation.value q w mu=
      coefficient q w*(s-delta q w mu)^2/2 := by
  have h := frozen_completed_square q w mu ((1-mu)+s) hq hc
  rw [balanced_loss q w mu s hq balance] at h
  have he : (1-mu)+s-((1-mu)+delta q w mu)=s-delta q w mu := by ring
  rw [he] at h
  linarith only [h]

/-- Actual oracle regret, after all-alternative infimum and all-query
supremum have both been evaluated. -/
theorem actual_frozen_oracle_gap (A : Finset (I n)) (j : I n) (q w mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (hc : 0 < coefficient q w)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (guard : beta q w*(1-mu)^2 ≤ p q w*mu^2)
    (hnu0 : 0 ≤ mu-delta q w mu) (hnu1 : mu-delta q w mu ≤ 1) :
    oracleRegret A j q mu (queries A j) (weights A j q w)=
      coefficient q w*(shift q mu-delta q w mu)^2/2 := by
  have hm := phase_shift_bounds q mu hq hlo hup
  have hmu : 0 < mu := by linarith [hm.1]
  have hmu1 : mu ≤ 1 := hm.2.1
  have he := balanced_gap_identity q w mu (shift q mu) (by linarith) (ne_of_gt hc)
    (D6AllocationPhaseThreeParameters.balance q mu hq hmu hmu1)
  unfold oracleRegret
  rw [phase_three_oracle A j q mu hq hlo hup hj hA hB,
    frozen_actual_value A j q w mu hq hw hw1 hc hj hA hB guard hnu0 hnu1]
  change max 0 (gammaTwice q mu (shift q mu)/2-D6FrozenScalarAllocation.value q w mu)=_
  rw [he,max_eq_right (by positivity)]

/-- At the design margin, stationarity makes the frozen nuisance equal to
the oracle nuisance. This cancels the zeroth-order term in the gap. -/
theorem frozen_shift_at_design (q mu : ℝ) (hq : 3 ≤ q) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hc : coefficient q (mass q mu) ≠ 0) :
    delta q (mass q mu) mu=shift q mu := by
  have h := stationarity q mu hq hmu hmu1
  unfold delta
  apply (div_eq_iff hc).mpr
  unfold coefficient
  field_simp [show q ≠ 0 by linarith]
  nlinarith only [h]

/-- Equal boundary values identify the kink coefficient without differentiating
an infimum: J = p mu/(1-mu), hence J>0 for a nondegenerate frozen design. -/
theorem boundary_slope_jump (p b c mu : ℝ) (hmu : mu ≠ 1)
    (equal_values : (p*mu^2+b*(1-mu)^2)/2=c*(1-mu)^2/2) :
    p*mu-b*(1-mu)+c*(1-mu)=p*mu/(1-mu) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm hmu))).mpr
  nlinarith only [equal_values]

#print axioms balanced_gap_identity
#print axioms actual_frozen_oracle_gap
#print axioms frozen_shift_at_design
#print axioms boundary_slope_jump
end
end CIGAMF.P13.D6FrozenOracleGap
