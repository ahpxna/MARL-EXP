import «LeanD6AllocationMarginV1»

/-! Width cap for the actual, uniformly averaged adjacent-swap KL at a fixed
nuisance. q=k-1. This is not a bound for each individual alternative, nor an
optimal composite-nuisance allocation theorem. Variance rescales KL by sigma2. -/
namespace CIGAMF.P13.D6QueryWidthInformation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationMargin
noncomputable section
variable {n : ℕ}

theorem actual_fixed_margin_sum (A G : Finset (I n)) (j : I n) (h : Bool) (q mu : ℝ)
    (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) :
    (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu)=
      ((1-mu)^2/2)*(q*(G ∩ A).card+(q+1)*(G ∩ others A j).card-
        2*((G ∩ A).card:ℝ)*(G ∩ others A j).card) := by
  have hp (a : I n) (ha : a ∈ A) (b : I n) (hb : b ∈ others A j) :
      queryKL A (swapped A a b) G j h mu mu=
        4*(1-mu)^2*queryKL A (swapped A a b) G j h (1/2) (1/2) := by
    have he := joint_homogeneity A (swapped A a b) G j h hj
      (swapped_j_not A j a b hj hb) hjG hG (1-mu) 1
    convert he using 1 <;> ring
  have hd := actual_dual_sum A G j h q 0 hj hA hB hjG hG
  simp only [CIGAMF.P13.D6ExpandedAllocation.dual,zero_pow (by decide : 2 ≠ 0),
    mul_zero,zero_mul,zero_add,add_zero,one_pow,one_mul] at hd
  calc
    _ = 4*(1-mu)^2*(∑ a ∈ A,∑ b ∈ others A j,
        queryKL A (swapped A a b) G j h (1/2) (1/2)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      rw [mul_sum]
      exact sum_congr rfl (fun b hb => hp a ha b hb)
    _ = ((1-mu)^2/2)*(8*(∑ a ∈ A,∑ b ∈ others A j,
        queryKL A (swapped A a b) G j h (1/2) (1/2))) := by ring
    _ = _ := by norm_num at hd; rw [hd]

lemma count_polynomial_bound (q s t r : ℝ) (hq : 0 ≤ q)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : s+t ≤ r) :
    q*s+(q+1)*t-2*s*t ≤ (q+1)*r := by
  nlinarith [mul_nonneg hs ht,mul_le_mul_of_nonneg_left hr (show 0 ≤ q+1 by linarith)]

/-- Uniform adjacent-world average of actual KL. At mu=0 this is precisely
r/(2*sigma2*(k-1)). The switch h does not affect same-margin differences. -/
theorem actual_average_width_bound (A G : Finset (I n)) (j : I n) (h : Bool)
    (q mu r sigma2 : ℝ) (hq : 0 < q) (hsigma : 0 < sigma2)
    (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (hsize : (G.card:ℝ) ≤ r) :
    (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu)/
      (sigma2*q*(q+1)) ≤ (1-mu)^2*r/(2*sigma2*q) := by
  rw [actual_fixed_margin_sum A G j h q mu hj hA hB hjG hG]
  have hc : ((G ∩ A).card:ℝ)+((G ∩ others A j).card:ℝ) ≤ r := by
    rw [← Nat.cast_add,query_count_partition A G j hjG]
    exact hsize
  have hp := count_polynomial_bound q (G ∩ A).card (G ∩ others A j).card r hq.le
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hc
  have hh := mul_le_mul_of_nonneg_left hp (div_nonneg (sq_nonneg (1-mu)) (by norm_num : (0:ℝ) ≤ 2))
  have hden : 0 < sigma2*q*(q+1) := by positivity
  calc _ ≤ (((1-mu)^2/2)*((q+1)*r))/(sigma2*q*(q+1)) :=
      div_le_div_of_nonneg_right hh hden.le
       _ = _ := by field_simp <;> ring

#print axioms actual_fixed_margin_sum
#print axioms actual_average_width_bound
end
end CIGAMF.P13.D6QueryWidthInformation
