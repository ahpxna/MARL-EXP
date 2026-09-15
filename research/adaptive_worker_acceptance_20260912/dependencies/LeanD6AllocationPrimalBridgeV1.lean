import «LeanD6AllocationFiniteBridgeV1»

/-! The actual two-orbit query allocation has exactly the analytic primal
loss, for every same-cardinality hidden alternative and every real margin. -/
namespace CIGAMF.P13.D6AllocationPrimalBridge
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6ExpandedAllocation
noncomputable section
variable {n : ℕ}

theorem intersection_others (H A : Finset (I n)) (j : I n) (hjH : j ∉ H) :
    H ∩ others A j=H \ A := by
  ext i
  simp only [mem_inter, others, mem_erase, mem_sdiff, mem_univ, true_and]
  aesop

theorem card_erase_real (H : Finset (I n)) (a : I n) :
    ((H.erase a).card : ℝ)=H.card-hit H a := by
  by_cases ha : a ∈ H
  · have he : ((H.erase a).card : ℝ)+1=H.card := by exact_mod_cast card_erase_add_one ha
    simp only [hit, ite_eq_left ha]
    linarith
  · simp [hit, ha]

/-- Each A-minus-one query counts d minus one possible omitted mistake. -/
theorem erased_A_count (A A' : Finset (I n)) (j a : I n) (hj : j ∉ A) :
    (((A.erase a) ∩ others A' j).card : ℝ)=(A \ A').card-hit (A \ A') a := by
  have he : (A.erase a) ∩ others A' j=(A ∩ others A' j).erase a := by ext i; simp
  rw [he, intersection_others A A' j hj, card_erase_real]

/-- The B query counts q-d in any alternative with the same cardinality. -/
theorem B_alternative_count (A A' : Finset (I n)) (j : I n) (hj' : j ∉ A')
    (hcard : A'.card=A.card) :
    ((others A j ∩ others A' j).card : ℝ)=(others A j).card-(A \ A').card := by
  have hjB : j ∉ others A j := by simp [others]
  have hswap : (others A j) ∩ A'=A' \ A := by
    rw [inter_comm, intersection_others A' A j hj']
  have hds : (A' \ A).card=(A \ A').card := card_sdiff_comm hcard
  have hn := card_sdiff_add_card_inter (others A j) A'
  rw [hswap, hds, ← intersection_others (others A j) A' j hjB] at hn
  have hr : ((others A j ∩ others A' j).card : ℝ)+(A \ A').card=(others A j).card := by exact_mod_cast hn
  linarith

theorem erased_query_legal (A : Finset (I n)) (j a : I n) (hj : j ∉ A)
    (ha : a ∈ A) (hA : 4 ≤ A.card) : j ∉ A.erase a ∧ 2 ≤ (A.erase a).card := by
  refine ⟨by simp [hj], ?_⟩
  rw [card_erase_of_mem ha]
  omega

/-- Pointwise actual unanchored KL, with no abstract loss assumption. -/
theorem erased_A_KL (A A' : Finset (I n)) (j a : I n) (hj : j ∉ A) (hj' : j ∉ A')
    (ha : a ∈ A) (hA : 4 ≤ A.card) (t : ℝ) :
    8*queryKL A A' (A.erase a) j false (1/2) (1-t/2) =
      t^2*(((A \ A').card : ℝ)-hit (A \ A') a)^2 := by
  have hlegal := erased_query_legal A j a hj ha hA
  have htrue : ((A.erase a) ∩ others A j)=∅ := by
    rw [intersection_others (A.erase a) A j hlegal.1]
    exact sdiff_eq_empty_iff_subset.mpr (erase_subset a A)
  unfold queryKL
  rw [actual_query_mean A (A.erase a) j false hj hlegal.1 (by intro _; exact hlegal.2),
    actual_query_mean A' (A.erase a) j false hj' hlegal.1 (by intro _; exact hlegal.2),
    htrue, card_empty, erased_A_count A A' j a hj]
  simp only [bit_false, Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
  ring

theorem single_second_moment (H G : Finset (I n)) (u v : ℝ) :
    (∑ i ∈ H, (u+v*hit G i)^2)=(H.card : ℝ)*u^2+(2*u*v+v^2)*(G ∩ H).card := by
  have he : ∀ i, (u+v*hit G i)^2=u^2+(2*u*v+v^2)*hit G i := by
    intro i
    by_cases hi : i ∈ G <;> simp [hit, hi] <;> ring
  simp_rw [he]
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, sum_hit]

/-- Exact average over the k actual A-minus-one queries; d may be any
exchange distance, including non-nearest alternatives. -/
theorem actual_A_query_sum (A A' : Finset (I n)) (j : I n) (hj : j ∉ A) (hj' : j ∉ A')
    (hA : 4 ≤ A.card) (t : ℝ) :
    8*(∑ a ∈ A, queryKL A A' (A.erase a) j false (1/2) (1-t/2)) =
      t^2*(A \ A').card*((A \ A').card*((A.card : ℝ)-2)+1) := by
  rw [mul_sum]
  have he : (∑ a ∈ A, 8*queryKL A A' (A.erase a) j false (1/2) (1-t/2)) =
      ∑ a ∈ A, t^2*(((A \ A').card : ℝ)+(-1)*hit (A \ A') a)^2 := by
    apply sum_congr rfl
    intro a ha
    rw [erased_A_KL A A' j a hj hj' ha hA]
    ring
  rw [he, ← mul_sum, single_second_moment]
  rw [inter_eq_left.mpr (sdiff_subset : A \ A' ⊆ A)]
  ring

/-- Exact contribution of the actual anchored B query. -/
theorem actual_B_query_KL (A A' : Finset (I n)) (j : I n) (hj : j ∉ A) (hj' : j ∉ A')
    (hcard : A'.card=A.card) (t : ℝ) :
    8*queryKL A A' (others A j) j true (1/2) (1-t/2) =
      (((others A j).card : ℝ)-1-(((others A j).card : ℝ)-(A \ A').card-1)*t)^2 := by
  have hjB : j ∉ others A j := by simp [others]
  unfold queryKL
  rw [actual_query_mean A (others A j) j true hj hjB (by simp),
    actual_query_mean A' (others A j) j true hj' hjB (by simp),
    inter_self, B_alternative_count A A' j hj' hcard]
  simp only [bit_true, ↓reduceIte]
  ring

def actualPrimal (A A' : Finset (I n)) (j : I n) (q c t : ℝ) : ℝ :=
  ((1-weight q c)/(q+1))*(∑ a ∈ A, queryKL A A' (A.erase a) j false (1/2) (1-t/2)) +
    weight q c*queryKL A A' (others A j) j true (1/2) (1-t/2)

/-- Complete primal bridge: a sum of squared differences of ACTUAL worlds
is exactly the analytic designLoss, for every hidden alternative. -/
theorem actual_primal_eq (A A' : Finset (I n)) (j : I n) (q c t : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    8*actualPrimal A A' j q c t=designLoss q c (A \ A').card t := by
  have hAn : 4 ≤ A.card := by exact_mod_cast (show (4:ℝ) ≤ A.card by linarith)
  have hsum := actual_A_query_sum A A' j hj hj' hAn t
  have hb := actual_B_query_KL A A' j hj hj' hcard t
  rw [hA] at hsum
  rw [hB] at hb
  unfold actualPrimal
  calc
    _ = ((1-weight q c)/(q+1))*(8*(∑ a ∈ A, queryKL A A' (A.erase a) j false (1/2) (1-t/2))) +
        weight q c*(8*queryKL A A' (others A j) j true (1/2) (1-t/2)) := by ring
    _ = designLoss q c (A \ A').card t := by rw [hsum, hb]; unfold designLoss; ring

/-- The proved analytic lower bound now applies to the actual allocation. -/
theorem actual_primal_lower (A A' : Finset (I n)) (j : I n) (q t : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hj' : j ∉ A') (hcard : A'.card=A.card)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hd : 1 ≤ ((A \ A').card : ℝ)) (hdq : ((A \ A').card : ℝ) ≤ q) :
    value q (scale q)/8 ≤ actualPrimal A A' j q (scale q) t := by
  have he := actual_primal_eq A A' j q (scale q) t hq hj hj' hcard hA hB
  have hl := all_distances_lower q (A \ A').card t hq hd hdq
  linarith

#print axioms B_alternative_count
#print axioms actual_A_query_sum
#print axioms actual_B_query_KL
#print axioms actual_primal_eq
#print axioms actual_primal_lower
end
end CIGAMF.P13.D6AllocationPrimalBridge
