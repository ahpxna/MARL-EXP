import «LeanD6FrozenQuadraticBoundV1»
import «LeanD6LocalMatchingAlgebraV1»
import «LeanD6AdaptiveOracleRegretV1»

/-! Boundary equality and loss bounds for two concrete legal D6 allocations.
These connect the local risk algebra to the actual supremum/infimum game. -/
namespace CIGAMF.P13.D6LocalMatchingDesign
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationDistribution CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6AllocationMarginSharp CIGAMF.P13.D6AllocationRiskBridge
open CIGAMF.P13.D6LocalOracleRegret CIGAMF.P13.D6AdaptiveOracleRegret
open CIGAMF.P13.D6AllocationPhaseThreeParameters CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6FrozenAllocationFeasible
open CIGAMF.P13.D6FrozenScalarAllocation CIGAMF.P13.D6FrozenQuadraticBound
open CIGAMF.P13.D6LocalMatchingAlgebra
noncomputable section
variable {n : ℕ}

def leftCoefficient (q : ℝ) := D6ExpandedAllocation.value q (D6ExpandedAllocation.scale q)
def localJump (q mu0 : ℝ) := jump (p q (mass q mu0)) (beta q (mass q mu0)) (leftCoefficient q) mu0
def localCurvature (q mu0 : ℝ) := curvatureDifference (p q (mass q mu0)) (beta q (mass q mu0)) (leftCoefficient q)

def leftRegret (A : Finset (I n)) (j : I n) (q mu : ℝ) :=
  oracleRegret A j q mu (primalQueries A j) (primalWeight A j q)
def rightRegret (A : Finset (I n)) (j : I n) (q mu0 mu : ℝ) :=
  oracleRegret A j q mu (D6PhaseThreePrimal.queries A j)
    (D6PhaseThreePrimal.weights A j q (mass q mu0))

lemma left_rate (q mu : ℝ) : rate q (1-mu)=leftValue (leftCoefficient q) mu := by
  unfold rate leftValue leftCoefficient
  ring

lemma frozen_rate (q w mu : ℝ) : D6FrozenScalarAllocation.value q w mu=frozenValue (p q w) (beta q w) mu := rfl

/-- Equality at the boundary follows from two proved oracle values, rather
than being assumed as an identity between guessed radical formulas. -/
theorem boundary_equality (A : Finset (I n)) (j : I n) (q mu0 : ℝ)
    (hq : 3 ≤ q) (hI : Interior q (1-mu0))
    (hlo : marginMax q ≤ mu0) (hup : mu0 ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    frozenValue (p q (mass q mu0)) (beta q (mass q mu0)) mu0=leftValue (leftCoefficient q) mu0 := by
  have hm := phase_shift_bounds q mu0 hq hlo hup
  have hw := phase_mass_bounds q mu0 hq hlo hup
  have hf := frozen_half_interval_value A j q (mass q mu0) mu0 hq hw.1 hw.2 hm.1 hm.2.1 hj hA hB
  have ho := D6PhaseThreeSharp.optimal_allocation_value A j q mu0 hq hlo hup hj hA hB
  have hl := phase_two_oracle A j q (1-mu0) hq hI hj hA hB
  simp only [sub_sub_cancel] at hl
  rw [phase_three_oracle A j q mu0 hq hlo hup hj hA hB,left_rate] at hl
  rw [frozen_rate] at hf
  exact hf.symm.trans (ho.trans hl)

lemma left_regret_zero (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hI : Interior q (1-mu))
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    leftRegret A j q mu=0 := by
  have ho := phase_two_oracle A j q (1-mu) hq hI hj hA hB
  have hv := phase_two_allocation_value A j q (1-mu) hq hI hj hA hB
  simp only [sub_sub_cancel] at ho hv
  simp [leftRegret,oracleRegret,ho,hv]

lemma left_value_lower_on_phase_three (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hmu : mu < 1) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    leftValue (leftCoefficient q) mu ≤ allocationValue A j mu (primalQueries A j) (primalWeight A j q) := by
  have hp := primal_distribution A j q hq hj hA hB
  obtain ⟨A',nu,had,he⟩ := D6PhaseThreeSharp.actual_adversary A j q mu hq hlo hup hj hA hB
    (primalQueries A j) (primalWeight A j q) hp.1 (fun e _ => hp.2.1 e) hp.2.2
  apply le_csInf (s := valueSet A j mu (primalQueries A j) (primalWeight A j q)) ⟨_,A',nu,had,rfl⟩
  rintro v ⟨B,u,h,rfl⟩
  have hg := margin_distribution_lower A B j q (1-mu) u hq (by linarith) hj h.2.2.1
    h.2.1 h.1 hA hB
  simpa only [sub_sub_cancel,left_rate] using hg

/-- Exact wrong-phase loss on the minus side, evaluated over every alternative. -/
theorem minus_right_loss (A : Finset (I n)) (j : I n) (q mu0 mu : ℝ)
    (hq : 3 ≤ q) (hI : Interior q (1-mu))
    (h0lo : marginMax q ≤ mu0) (h0hi : mu0 ≤ marginHigh q)
    (hm : 1/2 ≤ mu) (hm1 : mu ≤ 1)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    rightRegret A j q mu0 mu=max 0 (leftValue (leftCoefficient q) mu-
      frozenValue (p q (mass q mu0)) (beta q (mass q mu0)) mu) := by
  have ho := phase_two_oracle A j q (1-mu) hq hI hj hA hB
  simp only [sub_sub_cancel,left_rate] at ho
  have hw := phase_mass_bounds q mu0 hq h0lo h0hi
  have hv := frozen_half_interval_value A j q (mass q mu0) mu hq hw.1 hw.2 hm hm1 hj hA hB
  rw [frozen_rate] at hv
  simp only [rightRegret,oracleRegret,ho,hv]

/-- The exact plus oracle equals the frozen value plus its actual regret. -/
theorem plus_oracle_decomposition (A : Finset (I n)) (j : I n) (q mu0 mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (h0lo : marginMax q ≤ mu0) (h0hi : mu0 ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    D6PhaseThreeSharp.rate q mu=
      frozenValue (p q (mass q mu0)) (beta q (mass q mu0)) mu+rightRegret A j q mu0 mu := by
  have hm := phase_shift_bounds q mu hq hlo hup
  have hw := phase_mass_bounds q mu0 hq h0lo h0hi
  have hv := frozen_half_interval_value A j q (mass q mu0) mu hq hw.1 hw.2 hm.1 hm.2.1 hj hA hB
  rw [frozen_rate] at hv
  have hp := D6PhaseThreePrimal.distribution A j q (mass q mu0) (by linarith) hw.1 (by linarith [hw.2]) hB
  have hu := D6PhaseThreeSharp.every_allocation_value_le A j q mu hq hlo hup hj hA hB _ _
    hp.1 (fun e _ => hp.2.1 e) hp.2.2
  rw [hv] at hu
  unfold rightRegret oracleRegret
  rw [phase_three_oracle A j q mu hq hlo hup hj hA hB,hv,max_eq_right (by linarith)]
  ring

lemma plus_left_loss (A : Finset (I n)) (j : I n) (q mu0 mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (h0lo : marginMax q ≤ mu0) (h0hi : mu0 ≤ marginHigh q)
    (hmu : mu < 1) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    leftRegret A j q mu ≤ max 0
      (frozenValue (p q (mass q mu0)) (beta q (mass q mu0)) mu+rightRegret A j q mu0 mu-
        leftValue (leftCoefficient q) mu) := by
  have hl := left_value_lower_on_phase_three A j q mu hq hlo hup hmu hj hA hB
  unfold leftRegret oracleRegret
  rw [phase_three_oracle A j q mu hq hlo hup hj hA hB,
    plus_oracle_decomposition A j q mu0 mu hq hlo hup h0lo h0hi hj hA hB]
  exact max_le_max le_rfl (sub_le_sub_left hl _)

#print axioms boundary_equality
#print axioms minus_right_loss
#print axioms plus_oracle_decomposition
#print axioms plus_left_loss
end
end CIGAMF.P13.D6LocalMatchingDesign
