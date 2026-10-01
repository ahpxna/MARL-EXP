import «LeanD6PhaseThreePrimalV1»
import «LeanD6PhaseThreeDualV1»
import «LeanD6AllocationRiskBridgeV1»

/-! Exact phase-III saddle value for the actual finite D6 query game.
The primal covers every different hidden set and every nuisance margin; the
dual covers every legal allocation. This is not a sequential rate theorem. -/
namespace CIGAMF.P13.D6PhaseThreeSharp
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationPhaseThreeCore
open CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.P13.D6AllocationRiskBridge
open CIGAMF.P13.D6PhaseThreePrimal
noncomputable section
variable {n : ℕ}

def rate (q mu : ℝ) := gammaTwice q mu (shift q mu)/2

theorem actual_adversary (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hn : ∑ e ∈ E,w e=1) :
    ∃ A' nu,Admissible A A' j nu ∧
      (∑ e ∈ E,w e*information A A' j mu nu e) ≤ rate q mu := by
  obtain ⟨a,ha,b,hb,h⟩ := D6PhaseThreeDual.allocation_upper A j q mu hq hlo hup hj hA hB E w hl hw hn
  have hv := D6PhaseThreeDual.phase_nuisance q mu hq hlo hup
  exact ⟨swapped A a b,mu-shift q mu,
    ⟨swapped_ne A j a b hb,swapped_card A j a b ha hb,
      swapped_j_not A j a b hj hb,hv.2.1,hv.2.2.1⟩,h⟩

theorem sharp_game (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    (∃ (E : Finset (Measurement n)) (w : Measurement n → ℝ),
      (∀ e ∈ E,Legal j q e) ∧ (∀ e ∈ E,0 ≤ w e) ∧ (∑ e ∈ E,w e)=1 ∧
      (∀ A' nu,Admissible A A' j nu → rate q mu ≤
        ∑ e ∈ E,w e*information A A' j mu nu e)) ∧
    (∀ (E : Finset (Measurement n)) (w : Measurement n → ℝ),
      (∀ e ∈ E,Legal j q e) → (∀ e ∈ E,0 ≤ w e) → (∑ e ∈ E,w e)=1 →
      ∃ A' nu,Admissible A A' j nu ∧
        (∑ e ∈ E,w e*information A A' j mu nu e) ≤ rate q mu) := by
  have hm := phase_mass_bounds q mu hq hlo hup
  have hp := distribution A j q (mass q mu) (by linarith) hm.1 (by linarith [hm.2]) hB
  constructor
  · refine ⟨queries A j,weights A j q (mass q mu),hp.1,(fun e _ => hp.2.1 e),hp.2.2,?_⟩
    intro A' nu h
    exact actual_phase_lower A A' j q mu nu hq hlo hup hj h.2.2.1 h.2.1 h.1 hB
  · intro E w hl hw hn
    exact actual_adversary A j q mu hq hlo hup hj hA hB E w hl hw hn

theorem every_allocation_value_le (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hn : ∑ e ∈ E,w e=1) :
    allocationValue A j mu E w ≤ rate q mu := by
  obtain ⟨A',nu,h,he⟩ := actual_adversary A j q mu hq hlo hup hj hA hB E w hl hw hn
  exact le_trans (allocationValue_le_actual A A' j mu nu E w hw h) he

theorem optimal_allocation_value (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    allocationValue A j mu (queries A j) (weights A j q (mass q mu))=rate q mu := by
  have hm := phase_mass_bounds q mu hq hlo hup
  have hp := distribution A j q (mass q mu) (by linarith) hm.1 (by linarith [hm.2]) hB
  apply le_antisymm
  · exact every_allocation_value_le A j q mu hq hlo hup hj hA hB _ _ hp.1
      (fun e _ => hp.2.1 e) hp.2.2
  · obtain ⟨A',nu,h,he⟩ := actual_adversary A j q mu hq hlo hup hj hA hB _ _ hp.1
      (fun e _ => hp.2.1 e) hp.2.2
    apply le_csInf (s := valueSet A j mu (queries A j) (weights A j q (mass q mu)))
      ⟨_,A',nu,h,rfl⟩
    rintro v ⟨A'',nu',hh,rfl⟩
    exact actual_phase_lower A A'' j q mu nu' hq hlo hup hj hh.2.2.1 hh.2.1 hh.1 hB

#print axioms actual_adversary
#print axioms sharp_game
#print axioms every_allocation_value_le
#print axioms optimal_allocation_value
end
end CIGAMF.P13.D6PhaseThreeSharp
