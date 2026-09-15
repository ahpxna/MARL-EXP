import «LeanD6AllocationDualBridgeV1»

/-! Actual D6 information for learning the side of a margin threshold.
The hidden set is held fixed. These theorems identify the largest per-query
Gaussian squared-mean information, not a stopping-time or probability theorem.
The attaining query is B-off (not the B-on query used in allocation phase II).
Consequently a two-point gap 2*epsilon has four times the information of the
limit experiment from a point epsilon away to the phase boundary. -/
namespace CIGAMF.P13.D6PhaseTestingInformation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

theorem same_set_joint_information (A G : Finset (I n)) (j : I n) (h : Bool)
    (hj : j ∉ A) (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (mu nu : ℝ) :
    queryKL A A G j h mu nu =
      (mu-nu)^2 * (((G ∩ others A j).card : ℝ)-bit h)^2 / 2 := by
  unfold queryKL
  rw [actual_query_mean A G j h hj hjG hG,
    actual_query_mean A G j h hj hjG hG]
  ring

theorem same_set_scalar_information (A : Finset (I n)) (j i : I n)
    (hj : j ∉ A) (mu nu : ℝ) :
    scalarKL A A j i mu nu = if i ∈ A then 0 else (mu-nu)^2/2 := by
  unfold scalarKL
  rw [world_response A j hj, world_response A j hj]
  by_cases hi : i ∈ A
  · simp [CIGAMF.P13.D6Threshold.slope, hi, bit_true]
  · by_cases hij : i=j
    · simp [CIGAMF.P13.D6Threshold.slope, hj, hij, bit_true]
    · simp [CIGAMF.P13.D6Threshold.slope, hi, hij, bit_true]
      ring

theorem joint_sensitivity_bound (A G : Finset (I n)) (j : I n) (h : Bool)
    (q : ℝ) (hq : 1 ≤ q) (hsize : (G.card : ℝ) ≤ q) :
    (((G ∩ others A j).card : ℝ)-bit h)^2 ≤ q^2 := by
  have hc0 : (0:ℝ) ≤ (G ∩ others A j).card := by positivity
  have hc : ((G ∩ others A j).card : ℝ) ≤ q := by
    exact le_trans (by exact_mod_cast card_le_card (inter_subset_left :
      G ∩ others A j ⊆ G)) hsize
  cases h <;> simp only [bit_false, bit_true] <;> nlinarith

/-- Every actual legal scalar or joint query has information at most q^2
 times the scalar Gaussian information when only the true margin changes. -/
theorem actual_information_upper (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 1 ≤ q) (hj : j ∉ A) (mu nu : ℝ)
    (e : Measurement n) (he : Legal j q e) :
    information A A j mu nu e ≤ q^2*(mu-nu)^2/2 := by
  cases e with
  | inl i =>
    change scalarKL A A j i mu nu ≤ _
    rw [same_set_scalar_information A j i hj mu nu]
    split_ifs
    · positivity
    · have hh := mul_le_mul_of_nonneg_right
        (show (1:ℝ) ≤ q^2 by nlinarith) (sq_nonneg (mu-nu))
      nlinarith
  | inr p =>
    change queryKL A A p.1 j p.2 mu nu ≤ _
    rw [same_set_joint_information A p.1 j p.2 hj he.1 he.2.2 mu nu]
    have hh := mul_le_mul_of_nonneg_left
      (joint_sensitivity_bound A p.1 j p.2 q hq he.2.1) (sq_nonneg (mu-nu))
    nlinarith

/-- The maximum sensitivity is attained by the actual unanchored B query. -/
theorem B_off_attains (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 2 ≤ q) (hj : j ∉ A) (hB : ((others A j).card : ℝ)=q)
    (mu nu : ℝ) :
    Legal j q (.inr (others A j,false)) ∧
      information A A j mu nu (.inr (others A j,false)) = q^2*(mu-nu)^2/2 := by
  have hjB : j ∉ others A j := by simp [others]
  have hcard : 2 ≤ (others A j).card := by exact_mod_cast (show (2:ℝ) ≤ (others A j).card by linarith)
  refine ⟨⟨hjB,by linarith,by intro _; exact hcard⟩,?_⟩
  change queryKL A A (others A j) j false mu nu = _
  rw [same_set_joint_information A (others A j) j false hj hjB (by intro _; exact hcard) mu nu]
  simp only [inter_self,bit_false,sub_zero,hB]
  ring

/-- Two specified hypotheses on opposite sides, with separation 2*epsilon. -/
theorem separated_pair_information (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 2 ≤ q) (hj : j ∉ A) (hB : ((others A j).card : ℝ)=q)
    (boundary epsilon : ℝ) :
    information A A j (boundary-epsilon) (boundary+epsilon)
      (.inr (others A j,false)) = 2*q^2*epsilon^2 := by
  rw [(B_off_attains A j q hq hj hB _ _).2]
  ring

/-- The limit to the phase boundary has one quarter of the pair information.
This is the relevant information for a procedure correct for every nonzero gap. -/
theorem boundary_information (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 2 ≤ q) (hj : j ∉ A) (hB : ((others A j).card : ℝ)=q)
    (boundary epsilon : ℝ) :
    information A A j (boundary+epsilon) boundary
      (.inr (others A j,false)) = q^2*epsilon^2/2 := by
  rw [(B_off_attains A j q hq hj hB _ _).2]
  ring

/-- Mixing legal queries cannot improve on the attained margin information. -/
theorem every_allocation_information_upper (A : Finset (I n)) (j : I n)
    (q : ℝ) (hq : 1 ≤ q) (hj : j ∉ A) (mu nu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hlegal : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e)
    (hnorm : ∑ e ∈ E, w e=1) :
    (∑ e ∈ E, w e * information A A j mu nu e) ≤ q^2*(mu-nu)^2/2 := by
  calc
    _ ≤ ∑ e ∈ E, w e * (q^2*(mu-nu)^2/2) := by
      apply sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left
        (actual_information_upper A j q hq hj mu nu e (hlegal e he)) (hw e he)
    _ = _ := by rw [← sum_mul,hnorm,one_mul]

#print axioms same_set_joint_information
#print axioms same_set_scalar_information
#print axioms actual_information_upper
#print axioms B_off_attains
#print axioms separated_pair_information
#print axioms boundary_information
#print axioms every_allocation_information_upper
end
end CIGAMF.P13.D6PhaseTestingInformation
