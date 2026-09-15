import «LeanD6AllocationPhaseThreeFeasibleV1»
import «LeanD6AllocationMarginV1»

/-! The phase-III design, represented on the actual finite measurement library.
The lower bound is uniform over every same-size hidden alternative and every
real nuisance margin. No formula for the actual information is assumed. -/
namespace CIGAMF.P13.D6PhaseThreePrimal
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationSharp
open CIGAMF.P13.D6AllocationPhaseThreeCore
open CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible
open CIGAMF.P13.D6AllocationMarginRegion
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

theorem actual_scalar_B_point (A A' : Finset (I n)) (j i : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (hi : i ∈ others A j) (mu nu : ℝ) :
    2*scalarKL A A' j i mu nu =
      (nu-mu)^2+(mu^2-(nu-mu)^2)*hit A' i := by
  have hh := others_not_mem A j i hi
  unfold scalarKL
  rw [world_response A j hj,world_response A' j hj']
  by_cases hi' : i ∈ A' <;>
    simp [CIGAMF.P13.D6Threshold.slope,hh.1,hh.2,hi',hit,bit_true] <;> ring

theorem actual_scalar_B_sum (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (mu nu : ℝ) :
    2*(∑ i ∈ others A j,scalarKL A A' j i mu nu) =
      (A \ A').card*mu^2+(((others A j).card : ℝ)-(A \ A').card)*(nu-mu)^2 := by
  rw [mul_sum]
  have he : (∑ i ∈ others A j,2*scalarKL A A' j i mu nu) =
      ∑ i ∈ others A j,((nu-mu)^2+(mu^2-(nu-mu)^2)*hit A' i) := by
    apply sum_congr rfl
    intro i hi
    exact actual_scalar_B_point A A' j i hj hj' hi mu nu
  rw [he]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,sum_hit]
  rw [intersection_others A' A j hj',card_sdiff_comm hcard]
  ring

theorem actual_Bon_KL (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (mu nu : ℝ) :
    2*queryKL A A' (others A j) j true mu nu =
      ((1-mu)*((others A j).card-1)-
        (1-nu)*((others A j).card-(A \ A').card-1))^2 := by
  have hjB : j ∉ others A j := by simp [others]
  unfold queryKL
  rw [actual_query_mean A (others A j) j true hj hjB (by simp),
    actual_query_mean A' (others A j) j true hj' hjB (by simp),
    inter_self,B_alternative_count A A' j hj' hcard]
  simp only [bit_true,↓reduceIte]
  ring

def queries (A : Finset (I n)) (j : I n) : Finset (Measurement n) :=
  insert (.inr (others A j,true)) ((others A j).image Sum.inl)

def weights (A : Finset (I n)) (j : I n) (q w : ℝ) (e : Measurement n) : ℝ :=
  (if e = .inr (others A j,true) then w else 0)+
    ∑ i ∈ others A j,if e = .inl i then (1-w)/q else 0

theorem weighted_sum (A : Finset (I n)) (j : I n) (q w : ℝ) (f : Measurement n → ℝ) :
    (∑ e ∈ queries A j,weights A j q w e*f e) =
      (1-w)/q*(∑ i ∈ others A j,f (.inl i))+w*f (.inr (others A j,true)) := by
  have hb : (.inr (others A j,true) : Measurement n) ∈ queries A j := by simp [queries]
  have hi : ∀ i ∈ others A j,(.inl i : Measurement n) ∈ queries A j := by
    intro i hi
    exact mem_insert_of_mem (mem_image_of_mem _ hi)
  unfold weights
  simp only [add_mul,sum_add_distrib,sum_mul]
  have hs : (∑ e ∈ queries A j,(if e = .inr (others A j,true) then w else 0)*f e) =
      w*f (.inr (others A j,true)) := by simp [ite_mul,hb]
  rw [hs,sum_comm]
  have ht : (∑ i ∈ others A j,∑ e ∈ queries A j,
      (if e = .inl i then (1-w)/q else 0)*f e) =
      (1-w)/q*(∑ i ∈ others A j,f (.inl i)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i him
    simp [ite_mul,hi i him]
  rw [ht]
  ring

theorem distribution (A : Finset (I n)) (j : I n) (q w : ℝ)
    (hq : 0 < q) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (hB : ((others A j).card : ℝ)=q) :
    (∀ e ∈ queries A j,Legal j q e) ∧ (∀ e,0 ≤ weights A j q w e) ∧
      (∑ e ∈ queries A j,weights A j q w e)=1 := by
  refine ⟨?_,?_,?_⟩
  · intro e he
    rcases mem_insert.mp he with he | he
    · subst e
      exact ⟨by simp [others],hB.le,by simp⟩
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp he
      trivial
  · intro e
    unfold weights
    apply add_nonneg
    · split <;> first | exact hw | exact le_refl 0
    · apply sum_nonneg
      intro i hi
      split <;> first | exact div_nonneg (by linarith) hq.le | exact le_refl 0
  · have he := weighted_sum A j q w (fun _ => 1)
    simp only [mul_one,sum_const,nsmul_eq_mul,hB] at he
    rw [he]
    field_simp [ne_of_gt hq]
    <;> ring

theorem actual_phase_information (A A' : Finset (I n)) (j : I n) (q w mu nu : ℝ)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card)
    (hB : ((others A j).card : ℝ)=q) :
    2*(∑ e ∈ queries A j,weights A j q w e*information A A' j mu nu e) =
      mixedLoss q mu w (A \ A').card (1-nu) := by
  rw [weighted_sum]
  change 2*((1-w)/q*(∑ i ∈ others A j,scalarKL A A' j i mu nu)+
    w*queryKL A A' (others A j) j true mu nu)=_
  have hs := actual_scalar_B_sum A A' j hj hj' hcard mu nu
  have hb := actual_Bon_KL A A' j hj hj' hcard mu nu
  rw [hB] at hs hb
  calc
    _ = (1-w)/q*(2*(∑ i ∈ others A j,scalarKL A A' j i mu nu))+
        w*(2*queryKL A A' (others A j) j true mu nu) := by ring
    _ = _ := by rw [hs,hb]; unfold mixedLoss; ring

theorem actual_phase_lower (A A' : Finset (I n)) (j : I n) (q mu nu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (hne : A' ≠ A)
    (hB : ((others A j).card : ℝ)=q) :
    gammaTwice q mu (shift q mu)/2 ≤
      ∑ e ∈ queries A j,weights A j q (mass q mu) e*information A A' j mu nu e := by
  have hd := alternative_distance_bounds A A' j q hj' hcard hne hB
  have hdn : 1 ≤ (A \ A').card := by exact_mod_cast hd.1
  have hcase : ((A \ A').card : ℝ)=1 ∨ 2 ≤ ((A \ A').card : ℝ) := by
    rcases Nat.eq_or_lt_of_le hdn with he | he
    · left; exact_mod_cast he.symm
    · right; exact_mod_cast he
  have hl := phase_all_distances_lower q mu (A \ A').card (1-nu) hq hlo hup hcase hd.2
  rw [← actual_phase_information A A' j q (mass q mu) mu nu hj hj' hcard hB] at hl
  linarith

#print axioms actual_scalar_B_sum
#print axioms actual_Bon_KL
#print axioms weighted_sum
#print axioms distribution
#print axioms actual_phase_information
#print axioms actual_phase_lower
end
end CIGAMF.P13.D6PhaseThreePrimal
