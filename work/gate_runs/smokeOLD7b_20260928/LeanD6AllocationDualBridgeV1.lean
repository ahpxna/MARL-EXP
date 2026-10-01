import «LeanD6AllocationPrimalBridgeV1»

/-! Actual scalar-response dual, legal query counts, and the sharp upper bound
against arbitrary allocations. The adversary is chosen after the allocation,
not after a sampled query. -/
namespace CIGAMF.P13.D6AllocationDualBridge
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

def scalarKL (A A' : Finset (I n)) (j i : I n) (mu nu : ℝ) : ℝ :=
  (productResponse corner (world A j mu) i true-
    productResponse corner (world A' j nu) i true)^2/2

theorem scalar_A_point (A : Finset (I n)) (j i a b : I n) (hj : j ∉ A)
    (hi : i ∈ A) (ha : a ∈ A) (hb : b ∈ others A j) (z : ℝ) :
    8*scalarKL A (swapped A a b) j i (1/2) (1-(1+z)/2)=(1-z)^2*hit {i} a := by
  have hh := others_not_mem A j b hb
  have hij : i ≠ j := by intro he; subst i; exact hj hi
  have hib : i ≠ b := by intro he; subst i; exact hh.1 hi
  unfold scalarKL
  rw [world_response A j hj, world_response (swapped A a b) j (swapped_j_not A j a b hj hb)]
  by_cases hia : i=a
  · subst a
    simp [CIGAMF.P13.D6Threshold.slope, hi, hij, hib, swapped, hit, bit_true]
    ring
  · simp [CIGAMF.P13.D6Threshold.slope, hi, hij, hib, hia, Ne.symm hia, swapped, hit, bit_true]

theorem scalar_B_point (A : Finset (I n)) (j i a b : I n) (hj : j ∉ A)
    (hi : i ∈ others A j) (ha : a ∈ A) (hb : b ∈ others A j) (z : ℝ) :
    8*scalarKL A (swapped A a b) j i (1/2) (1-(1+z)/2)=z^2+(1-z^2)*hit {i} b := by
  have hh := others_not_mem A j i hi
  unfold scalarKL
  rw [world_response A j hj, world_response (swapped A a b) j (swapped_j_not A j a b hj hb)]
  by_cases hib : i=b
  · subst b
    simp [CIGAMF.P13.D6Threshold.slope, hh.1, hh.2, swapped, hit, bit_true]
    ring
  · simp [CIGAMF.P13.D6Threshold.slope, hh.1, hh.2, hib, Ne.symm hib, swapped, hit, bit_true]
    ring

theorem scalar_j_point (A : Finset (I n)) (j a b : I n) (hj : j ∉ A)
    (hb : b ∈ others A j) (z : ℝ) :
    8*scalarKL A (swapped A a b) j j (1/2) (1-(1+z)/2)=z^2 := by
  unfold scalarKL
  rw [world_response A j hj, world_response (swapped A a b) j (swapped_j_not A j a b hj hb)]
  simp only [CIGAMF.P13.D6Threshold.slope, hj, swapped_j_not A j a b hj hb, ↓reduceIte, bit_true, mul_one]
  ring

theorem sum_singleton_hit (H : Finset (I n)) (i : I n) (hi : i ∈ H) :
    ∑ a ∈ H, hit {i} a=1 := by
  rw [sum_hit]
  simp [inter_eq_left.mpr (singleton_subset_iff.mpr hi)]

/-- Actual scalar dual average for each of the three coordinate orbits. -/
theorem actual_scalar_sum (A : Finset (I n)) (j i : I n) (hj : j ∉ A) (z : ℝ) :
    8*(∑ a ∈ A, ∑ b ∈ others A j, scalarKL A (swapped A a b) j i (1/2) (1-(1+z)/2)) =
      if i ∈ A then ((others A j).card : ℝ)*(1-z)^2 else if i=j then
        (A.card : ℝ)*(others A j).card*z^2 else
        (A.card : ℝ)*(1+(((others A j).card : ℝ)-1)*z^2) := by
  rw [mul_sum]
  simp_rw [mul_sum]
  by_cases hiA : i ∈ A
  · rw [ite_eq_left hiA]
    have he : (∑ a ∈ A, ∑ b ∈ others A j, 8*scalarKL A (swapped A a b) j i (1/2) (1-(1+z)/2)) =
        ∑ a ∈ A, ∑ _b ∈ others A j, (1-z)^2*hit {i} a := by
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro b hb
      exact scalar_A_point A j i a b hj hiA ha hb z
    rw [he]
    simp only [sum_const, nsmul_eq_mul, ← mul_sum, sum_singleton_hit A i hiA]
    ring
  · rw [ite_eq_right hiA]
    by_cases hij : i=j
    · subst i
      rw [ite_eq_left rfl]
      have he : (∑ a ∈ A, ∑ b ∈ others A j, 8*scalarKL A (swapped A a b) j j (1/2) (1-(1+z)/2)) =
          ∑ _a ∈ A, ∑ _b ∈ others A j, z^2 := by
        apply sum_congr rfl; intro a ha
        apply sum_congr rfl; intro b hb
        exact scalar_j_point A j a b hj hb z
      rw [he]
      simp [mul_assoc]
    · rw [ite_eq_right hij]
      have hiB : i ∈ others A j := by simp [others, hiA, hij]
      have he : (∑ a ∈ A, ∑ b ∈ others A j, 8*scalarKL A (swapped A a b) j i (1/2) (1-(1+z)/2)) =
          ∑ _a ∈ A, ∑ b ∈ others A j, (z^2+(1-z^2)*hit {i} b) := by
        apply sum_congr rfl; intro a ha
        apply sum_congr rfl; intro b hb
        exact scalar_B_point A j i a b hj hiB ha hb z
      rw [he]
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum,
        sum_singleton_hit (others A j) i hiB]
      ring

/-- Query counts obey the analytic triangle because A and B partition every
coordinate except j. This is proved from the construction's `others`. -/
theorem query_count_partition (A G : Finset (I n)) (j : I n) (hjG : j ∉ G) :
    (G ∩ A).card+(G ∩ others A j).card=G.card := by
  have hu : (G ∩ A) ∪ (G ∩ others A j)=G := by
    ext i
    by_cases hiA : i ∈ A
    · simp [others, hiA]
    · by_cases hiG : i ∈ G
      · have hij : i ≠ j := by intro he; subst i; exact hjG hiG
        simp [others, hiA, hiG, hij]
      · simp [hiG]
  have hd : Disjoint (G ∩ A) (G ∩ others A j) := by
    apply disjoint_left.mpr
    intro i hi hi'
    have hh := others_not_mem A j i (mem_inter.mp hi').2
    exact hh.1 (mem_inter.mp hi).2
  rw [← card_union_of_disjoint hd, hu]

/-- A concrete query's adjacent-world KL sum is bounded by the analytic
value, without assuming an orbit formula or query-count condition. -/
theorem actual_joint_dual_bound (A G : Finset (I n)) (j : I n) (h : Bool) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (hsize : (G.card : ℝ) ≤ q) :
    8*(∑ a ∈ A, ∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h (1/2) (1-(1+root q (scale q))/2)) ≤
        q*(q+1)*value q (scale q) := by
  rw [actual_dual_sum A G j h q _ hj hA hB hjG hG]
  have hcnt : ((G ∩ A).card : ℝ)+(G ∩ others A j).card ≤ q := by
    have he : ((G ∩ A).card : ℝ)+(G ∩ others A j).card=G.card := by exact_mod_cast query_count_partition A G j hjG
    linarith
  have hb := all_width_both_query_dual q (G ∩ A).card (G ∩ others A j).card hq
    (by positivity) (by positivity) hcnt
  have he := dual_value_equals_primal q hq
  have hp : q*(q+1) ≠ 0 := ne_of_gt (mul_pos (by linarith) (by linarith))
  have he' := (div_eq_iff hp).mp he
  cases h <;> simp only [bit_false, bit_true] <;> nlinarith [hb.1, hb.2]

#print axioms actual_scalar_sum
#print axioms query_count_partition
#print axioms actual_joint_dual_bound

theorem actual_scalar_dual_bound (A : Finset (I n)) (j i : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    8*(∑ a ∈ A, ∑ b ∈ others A j,
      scalarKL A (swapped A a b) j i (1/2) (1-(1+root q (scale q))/2)) ≤
        q*(q+1)*value q (scale q) := by
  let z := root q (scale q)
  have hc := scale_properties q hq
  have hz := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  have hzle : z ≤ 1 := by dsimp [z]; nlinarith [hz.1, hz.2.1]
  have hs := scalar_dual q z hq hz.1.le hzle
  have hp : 0 < q := by linarith
  have hk : 0 < q+1 := by linarith
  have he := dual_value_equals_primal q hq
  have he' := (div_eq_iff (ne_of_gt (mul_pos hp hk))).mp he
  change q^2*(1+z)^2=value q (scale q)*(q*(q+1)) at he'
  rw [actual_scalar_sum A j i hj, hA, hB]
  change (if i ∈ A then q*(1-z)^2 else if i=j then (q+1)*q*z^2 else
    (q+1)*(1+(q-1)*z^2)) ≤ q*(q+1)*value q (scale q)
  split_ifs
  · have h := (div_le_div_iff_of_pos_right hk).mp hs.1
    have hh := mul_le_mul_of_nonneg_left h hp.le
    nlinarith
  · have h := (le_div_iff₀ hk).mp hs.2.2
    have hh := mul_le_mul_of_nonneg_left h hp.le
    nlinarith
  · have h := (div_le_div_iff₀ hp hk).mp hs.2.1
    nlinarith

abbrev Measurement (n : ℕ) := Sum (I n) (Finset (I n) × Bool)

def Legal (j : I n) (q : ℝ) : Measurement n → Prop
  | .inl _ => True
  | .inr (G,h) => j ∉ G ∧ (G.card : ℝ) ≤ q ∧ (h=false → 2 ≤ G.card)

def information (A A' : Finset (I n)) (j : I n) (mu nu : ℝ) : Measurement n → ℝ
  | .inl i => scalarKL A A' j i mu nu
  | .inr (G,h) => queryKL A A' G j h mu nu

theorem actual_measurement_dual_bound (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (e : Measurement n) (he : Legal j q e) :
    8*(∑ a ∈ A, ∑ b ∈ others A j,
      information A (swapped A a b) j (1/2) (1-(1+root q (scale q))/2) e) ≤
        q*(q+1)*value q (scale q) := by
  cases e with
  | inl i => exact actual_scalar_dual_bound A j i q hq hj hA hB
  | inr p => exact actual_joint_dual_bound A p.1 j p.2 q hq hj hA hB he.1 he.2.2 he.2.1

/-- One actual alternative defeats the entire allocation of all legal query
types. Both the hidden set and margin are valid, and the set differs from A. -/
theorem arbitrary_allocation_upper (A : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hlegal : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e) (hnorm : ∑ e ∈ E, w e=1) :
    ∃ A' : Finset (I n), ∃ nu : ℝ,
      A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ E, w e*information A A' j (1/2) nu e) ≤ value q (scale q)/8 := by
  let z := root q (scale q)
  let nu := 1-(1+z)/2
  let L := fun a b => ∑ e ∈ E, w e*information A (swapped A a b) j (1/2) nu e
  have hbound : 8*(∑ a ∈ A, ∑ b ∈ others A j, L a b) ≤ q*(q+1)*value q (scale q) := by
    have he : (∑ a ∈ A, ∑ b ∈ others A j, L a b) =
        ∑ e ∈ E, w e*(∑ a ∈ A, ∑ b ∈ others A j,
          information A (swapped A a b) j (1/2) nu e) := by
      dsimp [L]
      simp_rw [mul_sum]
      calc
        _ = ∑ a ∈ A, ∑ e ∈ E, ∑ b ∈ others A j,
            w e*information A (swapped A a b) j (1/2) nu e := by
          apply sum_congr rfl; intro a ha
          exact sum_comm
        _ = _ := sum_comm
    rw [he, mul_sum]
    calc
      _ ≤ ∑ e ∈ E, w e*(q*(q+1)*value q (scale q)) := by
        apply sum_le_sum; intro e he
        have hb := mul_le_mul_of_nonneg_left
          (actual_measurement_dual_bound A j q hq hj hA hB e (hlegal e he)) (hw e he)
        dsimp [nu,z]
        nlinarith
      _ = _ := by rw [← sum_mul, hnorm, one_mul]
  have hAnon : A.Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ) < A.card by linarith))
  have hBnon : (others A j).Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ) < (others A j).card by linarith))
  have hsum : (∑ a ∈ A, ∑ b ∈ others A j, L a b) ≤
      ∑ _a ∈ A, ∑ _b ∈ others A j, value q (scale q)/8 := by
    simp only [sum_const, nsmul_eq_mul, hA, hB]
    nlinarith
  obtain ⟨a, ha, hal⟩ := exists_le_of_sum_le hAnon hsum
  obtain ⟨b, hb, hbl⟩ := exists_le_of_sum_le hBnon hal
  have hc := scale_properties q hq
  have hz := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  have hnu : 0 ≤ nu ∧ nu ≤ 1 := by dsimp [nu,z]; constructor <;> nlinarith [hz.1, hz.2.1]
  exact ⟨swapped A a b, nu, swapped_ne A j a b hb, swapped_card A j a b ha hb,
    swapped_j_not A j a b hj hb, hnu.1, hnu.2, hbl⟩

#print axioms actual_scalar_dual_bound
#print axioms actual_measurement_dual_bound
#print axioms arbitrary_allocation_upper
end
end CIGAMF.P13.D6AllocationDualBridge
