import «LeanD6QueryWidthInformationV1»
import «LeanD6GaussianQueryDominanceV1»

namespace CIGAMF.P13.D6WidthCostInformation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6QueryWidthInformation CIGAMF.P13.D6GaussianQueryDominance
noncomputable section
variable {n : ℕ}

/-- Exact oracle envelope on a query contained in true B. Cost and variance are
separate positive primitives; scalar differencing does not satisfy them for free. -/
theorem actual_label_average_cost (A G : Finset (I n)) (j : I n)
    (q mu cost variance : ℝ) (hq : 0<q) (hc : 0<cost) (hv : 0<variance)
    (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q)
    (hjG : j ∉ G) (hG : 2 ≤ G.card) (hGA : Disjoint G A) (hGB : G ⊆ others A j) :
    (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j false mu mu)/
      (q*(q+1)*cost*variance) = (1-mu)^2*G.card/(2*q*cost*variance) := by
  rw [actual_fixed_margin_sum A G j false q mu hj hA hB hjG (fun _ => hG)]
  rw [disjoint_iff_inter_eq_empty.mp hGA,inter_eq_left.mpr hGB]
  simp only [card_empty,Nat.cast_zero,mul_zero,zero_mul,zero_add,sub_zero]
  field_simp
  <;> ring

theorem actual_known_label_margin_cost (A G : Finset (I n)) (j : I n)
    (q mu nu cost variance : ℝ) (hj : j ∉ A) (hl : Legal j q (.inr (G,false)))
    (hGB : G ⊆ others A j) :
    (actualMean A j mu (.inr (G,false))-actualMean A j nu (.inr (G,false)))^2/
      (2*cost*variance) = (mu-nu)^2*(G.card:ℝ)^2/(2*cost*variance) := by
  rw [actual_mean_affine A j hj q mu _ hl,actual_mean_affine A j hj q nu _ hl]
  simp only [meanOffset,meanSlope,inter_eq_left.mpr hGB,bit_false,sub_zero,Bool.false_eq_true,ite_false]
  ring

/-- Actual same-nuisance adjacent mixture, per cost, upper-bounds every joint
query by the B-scalar value when mu>=1/2 and cost*variance>=physical width. -/
theorem joint_mixture_scalar_bound (A G : Finset (I n)) (j : I n) (h : Bool)
    (q mu cost variance width : ℝ) (hq : 0<q) (hc : 0<cost) (hv : 0<variance)
    (hmu : 1/2 ≤ mu) (hj : j ∉ A) (hA : (A.card:ℝ)=q+1)
    (hB : ((others A j).card:ℝ)=q) (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card)
    (hwidth : (G.card:ℝ) ≤ width) (hcharge : width ≤ cost*variance) :
    (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu)/
      (q*(q+1)*cost*variance) ≤ mu^2/(2*q) := by
  have hb := actual_average_width_bound A G j h q mu width (cost*variance) hq
    (mul_pos hc hv) hj hA hB hjG hG hwidth
  have hden : (cost*variance)*q*(q+1)=q*(q+1)*cost*variance := by ring
  rw [hden] at hb
  apply hb.trans
  apply (div_le_div_iff₀ (by positivity : 0<2*(cost*variance)*q) (by positivity : 0<2*q)).mpr
  have hsq : (1-mu)^2 ≤ mu^2 := by nlinarith
  have hnon : 0 ≤ cost*variance := (mul_pos hc hv).le
  have hprod := mul_le_mul_of_nonneg_left hcharge (sq_nonneg (1-mu))
  have hprod2 := mul_le_mul_of_nonneg_right hsq hnon
  nlinarith [mul_nonneg (show 0 ≤ 2*q by positivity) (sub_nonneg.mpr (hprod.trans hprod2))]

#print axioms actual_label_average_cost
#print axioms actual_known_label_margin_cost
#print axioms joint_mixture_scalar_bound
end
end CIGAMF.P13.D6WidthCostInformation
