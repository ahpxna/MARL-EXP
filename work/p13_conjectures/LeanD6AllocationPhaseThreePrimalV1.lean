import «LeanD6AllocationPhaseThreeFeasibleV1»
import «LeanD6AllocationMarginV1»

/-! Phase III on actual D6 world evaluations and a normalized distribution
on legal measurements. This file proves the primal against every hidden
alternative; optimality additionally requires the all-query dual. -/
namespace CIGAMF.P13.D6AllocationPhaseThreePrimal
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationSharp
open CIGAMF.P13.D6AllocationPhaseThreeCore CIGAMF.P13.D6AllocationPhaseThreeParameters
open CIGAMF.P13.D6AllocationPhaseThreeFeasible CIGAMF.P13.D6AllocationMarginRegion
noncomputable section
variable {n : ℕ}

theorem scalar_B_point (A A' : Finset (I n)) (j i : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (hi : i ∈ others A j) (mu nu : ℝ) :
    2*scalarKL A A' j i mu nu =
      (mu-nu)^2+(mu^2-(mu-nu)^2)*hit A' i := by
  have hh := others_not_mem A j i hi
  unfold scalarKL
  rw [world_response A j hj, world_response A' j hj']
  by_cases hi' : i ∈ A' <;>
    simp [CIGAMF.P13.D6Threshold.slope,hh.1,hh.2,hi',hit,bit_true] <;> ring

/-- Exact sum of scalar information for every alternative distance. -/
theorem actual_scalar_B_sum (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (mu nu : ℝ) :
    2*(∑ i ∈ others A j, scalarKL A A' j i mu nu) =
      (A \ A').card*mu^2+
        (((others A j).card : ℝ)-(A \ A').card)*(mu-nu)^2 := by
  rw [mul_sum]
  have he : (∑ i ∈ others A j, 2*scalarKL A A' j i mu nu) =
      ∑ i ∈ others A j, ((mu-nu)^2+(mu^2-(mu-nu)^2)*hit A' i) := by
    apply sum_congr rfl
    intro i hi
    exact scalar_B_point A A' j i hj hj' hi mu nu
  rw [he]
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,sum_hit]
  rw [intersection_others A' A j hj',card_sdiff_comm hcard]
  ring

theorem actual_Bon_information (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (mu nu : ℝ) :
    2*queryKL A A' (others A j) j true mu nu =
      ((1-mu)*((others A j).card-1)-
        (1-nu)*(((others A j).card : ℝ)-(A \ A').card-1))^2 := by
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
  (if e=.inr (others A j,true) then w else 0)+
    ∑ i ∈ others A j, if e=.inl i then (1-w)/q else 0

theorem distribution_sum (A : Finset (I n)) (j : I n) (q w : ℝ)
    (f : Measurement n → ℝ) :
    (∑ e ∈ queries A j, weights A j q w e*f e) =
      (1-w)/q*(∑ i ∈ others A j, f (.inl i))+w*f (.inr (others A j,true)) := by
  have hb : (.inr (others A j,true) : Measurement n) ∈ queries A j := by simp [queries]
  have hi : ∀ i ∈ others A j, (.inl i : Measurement n) ∈ queries A j := by
    intro i hi
    exact mem_insert_of_mem (mem_image_of_mem _ hi)
  unfold weights
  simp only [add_mul,sum_add_distrib,sum_mul]
  have hbSum : (∑ e ∈ queries A j,
      (if e=.inr (others A j,true) then w else 0)*f e)=w*f (.inr (others A j,true)) := by
    simp [ite_mul,hb]
  rw [hbSum,sum_comm]
  have hiSum : (∑ i ∈ others A j, ∑ e ∈ queries A j,
      (if e=.inl i then (1-w)/q else 0)*f e)=(1-w)/q*(∑ i ∈ others A j, f (.inl i)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hmem
    simp [ite_mul,hi i hmem]
  rw [hiSum]
  ring

theorem distribution (A : Finset (I n)) (j : I n) (q w : ℝ)
    (hq : 0 < q) (hB : ((others A j).card : ℝ)=q) (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    (∀ e ∈ queries A j, Legal j q e) ∧
    (∀ e, 0 ≤ weights A j q w e) ∧ (∑ e ∈ queries A j, weights A j q w e)=1 := by
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
    · split <;> linarith
    · apply sum_nonneg
      intro i hi
      split
      · exact div_nonneg (by linarith) hq.le
      · exact le_refl 0
  · have he := distribution_sum A j q w (fun _ => 1)
    simp only [mul_one,sum_const,nsmul_eq_mul,hB] at he
    rw [he]
    field_simp [ne_of_gt hq]
    ring

/-- No abstract loss postulate: the finite actual-world sum is the quadratic. -/
theorem actual_information_eq (A A' : Finset (I n)) (j : I n) (q mu nu w : ℝ)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card)
    (hB : ((others A j).card : ℝ)=q) :
    2*(∑ e ∈ queries A j, weights A j q w e*information A A' j mu nu e) =
      mixedLoss q mu w (A \ A').card (1-nu) := by
  rw [distribution_sum]
  change 2*((1-w)/q*(∑ i ∈ others A j, scalarKL A A' j i mu nu)+
    w*queryKL A A' (others A j) j true mu nu)=_
  have hs := actual_scalar_B_sum A A' j hj hj' hcard mu nu
  have hb := actual_Bon_information A A' j hj hj' hcard mu nu
  rw [hB] at hs hb
  calc
    _ = (1-w)/q*(2*(∑ i ∈ others A j, scalarKL A A' j i mu nu))+
        w*(2*queryKL A A' (others A j) j true mu nu) := by ring
    _ = mixedLoss q mu w (A \ A').card (1-nu) := by rw [hs,hb]; unfold mixedLoss; ring

/-- Every legal alternative, including nonadjacent worlds and any nuisance
margin, is separated at the explicit phase-III rate. -/
theorem all_actual_alternatives_lower (A A' : Finset (I n)) (j : I n) (q mu nu : ℝ)
    (hq : 3 ≤ q) (hlo : marginMax q ≤ mu) (hup : mu ≤ marginHigh q)
    (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card) (hne : A' ≠ A)
    (hB : ((others A j).card : ℝ)=q) :
    gammaTwice q mu (shift q mu)/2 ≤
      ∑ e ∈ queries A j, weights A j q (mass q mu) e*information A A' j mu nu e := by
  have hd := alternative_distance_bounds A A' j q hj' hcard hne hB
  have hdn : 1 ≤ (A \ A').card := by exact_mod_cast hd.1
  have hcases : ((A \ A').card : ℝ)=1 ∨ 2 ≤ ((A \ A').card : ℝ) := by
    by_cases he : (A \ A').card=1
    · left; exact_mod_cast he
    · right; exact_mod_cast (show 2 ≤ (A \ A').card by omega)
  have hl := phase_all_distances_lower q mu (A \ A').card (1-nu) hq hlo hup hcases hd.2
  rw [← actual_information_eq A A' j q mu nu (mass q mu) hj hj' hcard hB] at hl
  linarith

#print axioms actual_scalar_B_sum
#print axioms actual_Bon_information
#print axioms distribution_sum
#print axioms distribution
#print axioms actual_information_eq
#print axioms all_actual_alternatives_lower
end
end CIGAMF.P13.D6AllocationPhaseThreePrimal
