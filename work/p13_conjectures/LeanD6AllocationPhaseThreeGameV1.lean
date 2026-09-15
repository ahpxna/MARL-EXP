import «LeanD6AllocationPhaseThreePrimalV1»
import «LeanD6AllocationPhaseThreeDualV1»

/-! Both sides of the actual D6 allocation game throughout phase III. The
nuisance adversary is chosen after the whole allocation, not after its query. -/
namespace CIGAMF.P13.D6AllocationPhaseThreeGame
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationPhaseThreeCore
open CIGAMF.P13.D6AllocationPhaseThreeParameters CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion CIGAMF.P13.D6AllocationPhaseThreePrimal
open CIGAMF.P13.D6AllocationPhaseThreeDual
noncomputable section
variable {n : ℕ}

def rate (q mu : ℝ) := gammaTwice q mu (shift q mu)/2

/-- One adjacent alternative defeats the entire legal allocation. -/
theorem allocation_upper (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hn : ∑ e ∈ E,w e=1) :
    ∃ a ∈ A,∃ b ∈ others A j,
      (∑ e ∈ E,w e*information A (swapped A a b) j mu (mu-shift q mu) e) ≤ rate q mu := by
  let L := fun a b => ∑ e ∈ E,w e*information A (swapped A a b) j mu (mu-shift q mu) e
  have hsum : (∑ a ∈ A,∑ b ∈ others A j,L a b)=
      ∑ e ∈ E,w e*(∑ a ∈ A,∑ b ∈ others A j,
        information A (swapped A a b) j mu (mu-shift q mu) e) := by
    dsimp [L]
    simp_rw [mul_sum]
    calc
      _ = ∑ a ∈ A,∑ e ∈ E,∑ b ∈ others A j,
          w e*information A (swapped A a b) j mu (mu-shift q mu) e := by
        apply sum_congr rfl; intro a ha; exact sum_comm
      _ = _ := sum_comm
  have hb : 2*(∑ a ∈ A,∑ b ∈ others A j,L a b) ≤
      (q+1)*(mu^2+(q-1)*(shift q mu)^2) := by
    rw [hsum,mul_sum]
    calc
      _ ≤ ∑ e ∈ E,w e*((q+1)*(mu^2+(q-1)*(shift q mu)^2)) := by
        apply sum_le_sum; intro e he
        have hh := mul_le_mul_of_nonneg_left
          (measurement_bound A j q mu hq hlo hup hj hA hB e (hl e he)) (hw e he)
        nlinarith only [hh]
      _ = _ := by rw [← sum_mul,hn,one_mul]
  have hp : 0 < q := by linarith
  have hrate : 2*q*rate q mu=mu^2+(q-1)*(shift q mu)^2 := by
    unfold rate gammaTwice
    field_simp [ne_of_gt hp]
  have hlower : (∑ a ∈ A,∑ b ∈ others A j,L a b) ≤
      ∑ _a ∈ A,∑ _b ∈ others A j,rate q mu := by
    simp only [sum_const,nsmul_eq_mul,hA,hB]
    nlinarith only [hb,congrArg (fun x : ℝ => (q+1)*x) hrate]
  have hAnon : A.Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ) < A.card by linarith))
  have hBnon : (others A j).Nonempty := card_pos.mp
    (by exact_mod_cast (show (0:ℝ) < (others A j).card by linarith))
  obtain ⟨a,ha,hal⟩ := exists_le_of_sum_le hAnon hlower
  obtain ⟨b,hb,hbl⟩ := exists_le_of_sum_le hBnon hal
  exact ⟨a,ha,b,hb,hbl⟩

/-- A legal probability allocation attains Gamma, and every legal allocation
has one admissible world with information at most Gamma. -/
theorem sharp_actual_game (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    (∃ E : Finset (Measurement n),∃ w : Measurement n → ℝ,
      (∀ e ∈ E,Legal j q e) ∧ (∀ e ∈ E,0 ≤ w e) ∧ (∑ e ∈ E,w e)=1 ∧
      (∀ A' : Finset (I n),j ∉ A' → A'.card=A.card → A' ≠ A →
        ∀ nu : ℝ,0 ≤ nu → nu ≤ 1 → rate q mu ≤ ∑ e ∈ E,w e*information A A' j mu nu e)) ∧
    (∀ E : Finset (Measurement n),∀ w : Measurement n → ℝ,
      (∀ e ∈ E,Legal j q e) → (∀ e ∈ E,0 ≤ w e) → (∑ e ∈ E,w e)=1 →
      ∃ A' : Finset (I n),∃ nu : ℝ,A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧
        0 ≤ nu ∧ nu ≤ 1 ∧ (∑ e ∈ E,w e*information A A' j mu nu e) ≤ rate q mu) := by
  have hw := phase_mass_bounds q mu hq hlo hup
  have hp := distribution A j q (mass q mu) (by linarith) hB hw.1 (by linarith [hw.2])
  constructor
  · refine ⟨queries A j,weights A j q (mass q mu),hp.1,(fun e _ => hp.2.1 e),hp.2.2,?_⟩
    intro A' hj' hcard hne nu _ _
    exact all_actual_alternatives_lower A A' j q mu nu hq hlo hup hj hj' hcard hne hB
  · intro E w hl hw hn
    obtain ⟨a,ha,b,hb,hu⟩ := allocation_upper A j q mu hq hlo hup hj hA hB E w hl hw hn
    have hnuis := phase_nuisance_bounds q mu hq hlo hup
    exact ⟨swapped A a b,mu-shift q mu,swapped_ne A j a b hb,
      swapped_card A j a b ha hb,swapped_j_not A j a b hj hb,hnuis.2.1,hnuis.2.2.1,hu⟩

/-- The explicit allocation has an admissible worst world attaining Gamma. -/
theorem value_attained (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    ∃ A' : Finset (I n),∃ nu : ℝ,A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧
      0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ queries A j,weights A j q (mass q mu) e*information A A' j mu nu e)=rate q mu := by
  have hw := phase_mass_bounds q mu hq hlo hup
  have hp := distribution A j q (mass q mu) (by linarith) hB hw.1 (by linarith [hw.2])
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hu⟩ :=
    (sharp_actual_game A j q mu hq hlo hup hj hA hB).2
      (queries A j) (weights A j q (mass q mu)) hp.1 (fun e _ => hp.2.1 e) hp.2.2
  exact ⟨A',nu,hne,hcard,hj',hnu,hnu1,le_antisymm hu
    (all_actual_alternatives_lower A A' j q mu nu hq hlo hup hj hj' hcard hne hB)⟩

#print axioms allocation_upper
#print axioms sharp_actual_game
#print axioms value_attained
end
end CIGAMF.P13.D6AllocationPhaseThreeGame
