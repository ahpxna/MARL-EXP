import «LeanD6AllocationMarginV1»

/-! Information for discovering the hidden set at a fixed true margin.
The adjacent average is bounded for every legal query. The final counting
corollary exposes its information-demand premise; it does not assume that
allocation learning must identify A exactly. -/
namespace CIGAMF.P13.D6LabelInformation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6ExpandedAllocation CIGAMF.P13.D6AllocationMargin
noncomputable section
variable {n : ℕ}

def capacityTwice (q mu : ℝ) := max (mu^2/q) ((1-mu)^2)

theorem fixed_margin_joint_sum (A G : Finset (I n)) (j : I n) (h : Bool) (q mu : ℝ)
    (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) :
    2*(∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu) =
      (1-mu)^2*(q*(G ∩ A).card+(q+1)*(G ∩ others A j).card-
        2*(G ∩ A).card*(G ∩ others A j).card) := by
  have hm : 1-(1-mu)*1=mu := by ring
  have hm' : 1-(1-mu)=mu := by ring
  have he : (∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu) =
      4*(1-mu)^2*(∑ a ∈ A,∑ b ∈ others A j,
        queryKL A (swapped A a b) G j h (1/2) (1/2)) := by
    rw [mul_sum]
    apply sum_congr rfl; intro a ha
    rw [mul_sum]
    apply sum_congr rfl; intro b hb
    have hh := joint_homogeneity A (swapped A a b) G j h hj
      (swapped_j_not A j a b hj hb) hjG hG (1-mu) 1
    norm_num only [hm,hm'] at hh
    exact hh
  have hd := actual_dual_sum A G j h q 0 hj hA hB hjG hG
  norm_num only at hd
  unfold dual at hd
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),mul_zero,zero_mul,zero_add,
    sub_zero,add_zero,one_pow,one_mul] at hd
  rw [he]
  nlinarith [congrArg (fun x : ℝ => (1-mu)^2*x) hd]

theorem measurement_average_bound (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 0 < q) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (e : Measurement n) (he : Legal j q e) :
    2*(∑ a ∈ A,∑ b ∈ others A j,information A (swapped A a b) j mu mu e) ≤
      q*(q+1)*capacityTwice q mu := by
  have hcapA := mul_le_mul_of_nonneg_left (le_max_left (mu^2/q) ((1-mu)^2))
    (show 0 ≤ q*(q+1) by positivity)
  have hcapB := mul_le_mul_of_nonneg_left (le_max_right (mu^2/q) ((1-mu)^2))
    (show 0 ≤ q*(q+1) by positivity)
  have hid : q*(q+1)*(mu^2/q)=(q+1)*mu^2 := by
    field_simp [ne_of_gt hq]
  rw [hid] at hcapA
  change (q+1)*mu^2 ≤ q*(q+1)*capacityTwice q mu at hcapA
  change q*(q+1)*(1-mu)^2 ≤ q*(q+1)*capacityTwice q mu at hcapB
  cases e with
  | inl i =>
    change 2*(∑ a ∈ A,∑ b ∈ others A j,scalarKL A (swapped A a b) j i mu mu) ≤ _
    have hs := actual_scalar_margin_sum A j i hj (1-mu) 0
    have hm : 1-(1-mu)=mu := by ring
    simp only [add_zero,mul_one,hm,hA,hB,zero_pow (by norm_num : (2:ℕ) ≠ 0),
      mul_zero,add_zero] at hs
    rw [hs]
    split_ifs
    · nlinarith [sq_nonneg mu]
    · have hc : 0 ≤ capacityTwice q mu := le_trans (sq_nonneg (1-mu)) (le_max_right _ _)
      positivity
    · exact hcapA
  | inr p =>
    change 2*(∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) p.1 j p.2 mu mu) ≤ _
    rw [fixed_margin_joint_sum A p.1 j p.2 q mu hj hA hB he.1 he.2.2]
    have hc : ((p.1 ∩ A).card : ℝ)+(p.1 ∩ others A j).card ≤ q := by
      have hh : ((p.1 ∩ A).card : ℝ)+(p.1 ∩ others A j).card=p.1.card := by
        exact_mod_cast query_count_partition A p.1 j he.1
      linarith [he.2.1]
    have hs : 0 ≤ ((p.1 ∩ A).card : ℝ) := by positivity
    have ht : 0 ≤ ((p.1 ∩ others A j).card : ℝ) := by positivity
    have hb : q*(p.1 ∩ A).card+(q+1)*(p.1 ∩ others A j).card-
        2*(p.1 ∩ A).card*(p.1 ∩ others A j).card ≤ q*(q+1) := by
      nlinarith [mul_nonneg hs ht]
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg (1-mu))
    nlinarith [hh,hcapB]

/-- Deterministic information accounting. To apply it to an adaptive stopped
experiment, a change-of-measure theorem must supply `demand` for the expected
counts. That probabilistic premise is intentionally explicit. -/
theorem cost_from_information_demand (A : Finset (I n)) (j : I n) (q mu k : ℝ)
    (hq : 0 < q) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (counts : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hc : ∀ e ∈ E,0 ≤ counts e)
    (demand : ∀ a ∈ A,∀ b ∈ others A j,
      k ≤ ∑ e ∈ E,counts e*information A (swapped A a b) j mu mu e) :
    2*k ≤ capacityTwice q mu*(∑ e ∈ E,counts e) := by
  have hlow : q*(q+1)*k ≤
      ∑ a ∈ A,∑ b ∈ others A j,∑ e ∈ E,
        counts e*information A (swapped A a b) j mu mu e := by
    have hh : (∑ _a ∈ A,∑ _b ∈ others A j,k) ≤
        ∑ a ∈ A,∑ b ∈ others A j,∑ e ∈ E,
          counts e*information A (swapped A a b) j mu mu e := by
      apply sum_le_sum; intro a ha
      apply sum_le_sum; intro b hb
      exact demand a ha b hb
    simp only [sum_const,nsmul_eq_mul,hA,hB] at hh
    nlinarith [hh]
  have he : (∑ a ∈ A,∑ b ∈ others A j,∑ e ∈ E,
      counts e*information A (swapped A a b) j mu mu e) =
      ∑ e ∈ E,counts e*(∑ a ∈ A,∑ b ∈ others A j,
        information A (swapped A a b) j mu mu e) := by
    simp_rw [mul_sum]
    calc
      _ = ∑ a ∈ A,∑ e ∈ E,∑ b ∈ others A j,
          counts e*information A (swapped A a b) j mu mu e := by
        apply sum_congr rfl; intro a ha; exact sum_comm
      _ = _ := sum_comm
  rw [he] at hlow
  have hhigh : 2*(∑ e ∈ E,counts e*(∑ a ∈ A,∑ b ∈ others A j,
      information A (swapped A a b) j mu mu e)) ≤
      q*(q+1)*capacityTwice q mu*(∑ e ∈ E,counts e) := by
    rw [mul_sum]
    calc
      _ ≤ ∑ e ∈ E,counts e*(q*(q+1)*capacityTwice q mu) := by
        apply sum_le_sum; intro e he
        have hh := mul_le_mul_of_nonneg_left
          (measurement_average_bound A j q mu hq hj hA hB e (hl e he)) (hc e he)
        nlinarith
      _ = _ := by rw [← sum_mul]; ring
  apply le_of_mul_le_mul_left (a := q*(q+1)) ?_ (by positivity)
  nlinarith [hlow,hhigh]

#print axioms fixed_margin_joint_sum
#print axioms measurement_average_bound
#print axioms cost_from_information_demand
end
end CIGAMF.P13.D6LabelInformation
