import «LeanD6AllocationMarginV1»

/-! Information available for discovering the hidden label set. Adjacent
alternatives keep the same margin. This is an actual-world information budget
certificate. A sequential change-of-measure theorem is a separate probability
bridge; it is not silently assumed as part of this result. -/
namespace CIGAMF.P13.D6LabelDiscoveryInformation
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6AllocationMargin
noncomputable section
variable {n : ℕ}

def twiceQueryCapacity (q mu : ℝ) := max (mu^2/q) ((1-mu)^2)

theorem same_margin_joint_point (A G : Finset (I n)) (j a b : I n) (h : Bool)
    (hj : j ∉ A) (ha : a ∈ A) (hb : b ∈ others A j)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (mu : ℝ) :
    2*queryKL A (swapped A a b) G j h mu mu =
      (1-mu)^2*(hit G a-hit G b)^2 := by
  unfold queryKL
  rw [actual_query_mean A G j h hj hjG hG,
    actual_query_mean (swapped A a b) G j h (swapped_j_not A j a b hj hb) hjG hG,
    swapped_query_count A G j a b hj ha hb]
  ring

theorem same_margin_joint_bound (A G : Finset (I n)) (j : I n) (h : Bool)
    (hj : j ∉ A) (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (mu : ℝ) :
    2*(∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) G j h mu mu) ≤
      (A.card : ℝ)*(others A j).card*(1-mu)^2 := by
  rw [mul_sum]
  simp_rw [mul_sum]
  calc
    _ ≤ ∑ _a ∈ A,∑ _b ∈ others A j,(1-mu)^2 := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      rw [same_margin_joint_point A G j a b h hj ha hb hjG hG]
      have hh : (hit G a-hit G b)^2 ≤ 1 := by unfold hit; split_ifs <;> norm_num
      nlinarith [mul_le_mul_of_nonneg_left hh (sq_nonneg (1-mu))]
    _ = _ := by simp [sum_const,nsmul_eq_mul]; ring

theorem same_margin_scalar_sum (A : Finset (I n)) (j i : I n) (hj : j ∉ A) (mu : ℝ) :
    2*(∑ a ∈ A,∑ b ∈ others A j,scalarKL A (swapped A a b) j i mu mu) =
      if i ∈ A then ((others A j).card : ℝ)*mu^2 else
        if i=j then 0 else (A.card : ℝ)*mu^2 := by
  have he := actual_scalar_margin_sum A j i hj (1-mu) 0
  simpa using he

/-- A single legal query has O(1/q) average adjacent-label information near
the allocation boundary, even though its margin information can be O(q^2). -/
theorem measurement_capacity (A : Finset (I n)) (j : I n) (q mu : ℝ)
    (hq : 0 < q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1)
    (hB : ((others A j).card : ℝ)=q) (e : Measurement n) (he : Legal j q e) :
    2*(∑ a ∈ A,∑ b ∈ others A j,information A (swapped A a b) j mu mu e) ≤
      q*(q+1)*twiceQueryCapacity q mu := by
  have hc1 := le_max_left (mu^2/q) ((1-mu)^2)
  have hc2 := le_max_right (mu^2/q) ((1-mu)^2)
  change mu^2/q ≤ twiceQueryCapacity q mu at hc1
  change (1-mu)^2 ≤ twiceQueryCapacity q mu at hc2
  have hnon : 0 ≤ twiceQueryCapacity q mu := le_trans (sq_nonneg _) hc2
  have hscalar : (q+1)*mu^2 ≤ q*(q+1)*twiceQueryCapacity q mu := by
    have h := (div_le_iff₀ hq).mp hc1
    have hh := mul_le_mul_of_nonneg_left h (show 0 ≤ q+1 by linarith)
    nlinarith
  cases e with
  | inl i =>
    change 2*(∑ a ∈ A,∑ b ∈ others A j,scalarKL A (swapped A a b) j i mu mu) ≤ _
    rw [same_margin_scalar_sum A j i hj mu,hA,hB]
    split_ifs
    · nlinarith [sq_nonneg mu]
    · positivity
    · exact hscalar
  | inr p =>
    have hb := same_margin_joint_bound A p.1 j p.2 hj he.1 he.2.2 mu
    rw [hA,hB] at hb
    have hh := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ q*(q+1) by positivity)
    change 2*(∑ a ∈ A,∑ b ∈ others A j,queryKL A (swapped A a b) p.1 j p.2 mu mu) ≤ _
    nlinarith

/-- Query counts may represent expectations, but this theorem assumes only
nonnegative real counts. It exposes the exact information-budget obligation
needed when attaching an adaptive stopping-time change of measure. -/
theorem discovery_budget (A : Finset (I n)) (j : I n) (q mu kappa : ℝ)
    (hq : 0 < q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1)
    (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (counts : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hc : ∀ e ∈ E,0 ≤ counts e)
    (hneed : ∀ a ∈ A,∀ b ∈ others A j,
      kappa ≤ ∑ e ∈ E,counts e*information A (swapped A a b) j mu mu e) :
    2*kappa ≤ twiceQueryCapacity q mu*(∑ e ∈ E,counts e) := by
  have hlower : (A.card : ℝ)*(others A j).card*kappa ≤
      ∑ a ∈ A,∑ b ∈ others A j,∑ e ∈ E,counts e*information A (swapped A a b) j mu mu e := by
    calc
      _ = ∑ _a ∈ A,∑ _b ∈ others A j,kappa := by simp [sum_const,nsmul_eq_mul]; ring
      _ ≤ _ := sum_le_sum (fun a ha => sum_le_sum (fun b hb => hneed a ha b hb))
  have hreorder : (∑ a ∈ A,∑ b ∈ others A j,∑ e ∈ E,
      counts e*information A (swapped A a b) j mu mu e)=
      ∑ e ∈ E,counts e*(∑ a ∈ A,∑ b ∈ others A j,information A (swapped A a b) j mu mu e) := by
    simp_rw [mul_sum]
    calc
      _ = ∑ a ∈ A,∑ e ∈ E,∑ b ∈ others A j,
          counts e*information A (swapped A a b) j mu mu e := by
        apply sum_congr rfl; intro a ha; exact sum_comm
      _ = _ := sum_comm
  rw [hreorder,hA,hB] at hlower
  have hupper : 2*(∑ e ∈ E,counts e*(∑ a ∈ A,∑ b ∈ others A j,
      information A (swapped A a b) j mu mu e)) ≤
      q*(q+1)*twiceQueryCapacity q mu*(∑ e ∈ E,counts e) := by
    rw [mul_sum]
    calc
      _ ≤ ∑ e ∈ E,counts e*(q*(q+1)*twiceQueryCapacity q mu) := by
        apply sum_le_sum; intro e he
        have hh := mul_le_mul_of_nonneg_left
          (measurement_capacity A j q mu hq hj hA hB e (hl e he)) (hc e he)
        nlinarith
      _ = _ := by rw [← sum_mul]; ring
  have hp : 0 < q*(q+1) := by positivity
  apply le_of_mul_le_mul_left (a := q*(q+1)) ?_ hp
  nlinarith [hlower,hupper]

#print axioms same_margin_joint_point
#print axioms same_margin_joint_bound
#print axioms same_margin_scalar_sum
#print axioms measurement_capacity
#print axioms discovery_budget
end
end CIGAMF.P13.D6LabelDiscoveryInformation
