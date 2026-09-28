import «LeanD6GaussianQueryDominanceV1»
import «LeanD6AllocationMarginSharpV1»

/-! Move true and nuisance margins together. For adjacent label worlds the
relative query slope is at most one, independent of q. This removes the q^2
curvature penalty in the earlier fixed-nuisance regret separation bound. -/
namespace CIGAMF.P13.D6MovingNuisanceRegret
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.P13.D6AllocationMargin CIGAMF.P13.D6AllocationMarginSharp
open CIGAMF.P13.D6GaussianQueryDominance
noncomputable section
variable {n : ℕ}

theorem adjacent_center_witness (A : Finset (I n)) (j : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hlegal : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e) (hnorm : ∑ e ∈ E,w e=1) :
    ∃ a ∈ A, ∃ b ∈ others A j,
      (∑ e ∈ E,w e*information A (swapped A a b) j (1-lam)
        (1-lam*(1+root q (scale q))) e) ≤ rate q lam := by
  let z := root q (scale q)
  let nu := 1-lam*(1+z)
  let L := fun a b => ∑ e ∈ E, w e*information A (swapped A a b) j (1-lam) nu e
  have hbound : 2*(∑ a ∈ A, ∑ b ∈ others A j, L a b) ≤ q*(q+1)*lam^2*value q (scale q) := by
    have he : (∑ a ∈ A, ∑ b ∈ others A j, L a b) =
        ∑ e ∈ E, w e*(∑ a ∈ A, ∑ b ∈ others A j,
          information A (swapped A a b) j (1-lam) nu e) := by
      dsimp [L]
      simp_rw [mul_sum]
      calc
        _ = ∑ a ∈ A, ∑ e ∈ E, ∑ b ∈ others A j,
            w e*information A (swapped A a b) j (1-lam) nu e := by
          apply sum_congr rfl; intro a ha
          exact sum_comm
        _ = _ := sum_comm
    rw [he,mul_sum]
    calc
      _ ≤ ∑ e ∈ E, w e*(q*(q+1)*lam^2*value q (scale q)) := by
        apply sum_le_sum; intro e he
        have hb := mul_le_mul_of_nonneg_left
          (measurement_margin_bound A j q lam hq hI hj hA hB e (hlegal e he)) (hw e he)
        dsimp [nu,z]
        nlinarith
      _ = _ := by rw [← sum_mul,hnorm,one_mul]
  have hAnon : A.Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ) < A.card by linarith))
  have hBnon : (others A j).Nonempty := card_pos.mp (by exact_mod_cast (show (0:ℝ) < (others A j).card by linarith))
  have hsum : (∑ a ∈ A, ∑ b ∈ others A j, L a b) ≤
      ∑ _a ∈ A, ∑ _b ∈ others A j, rate q lam := by
    simp only [sum_const,nsmul_eq_mul,hA,hB]
    unfold rate
    nlinarith
  obtain ⟨a,ha,hal⟩ := exists_le_of_sum_le hAnon hsum
  obtain ⟨b,hb,hbl⟩ := exists_le_of_sum_le hBnon hal
  exact ⟨a,ha,b,hb,hbl⟩

lemma information_eq_mean (A A' : Finset (I n)) (j : I n) (mu nu : ℝ)
    (e : Measurement n) : information A A' j mu nu e =
      (actualMean A j mu e-actualMean A' j nu e)^2/2 := by
  cases e <;> rfl

theorem adjacent_relative_slope (A : Finset (I n)) (j a b : I n)
    (hj : j ∉ A) (ha : a ∈ A) (hb : b ∈ others A j) (e : Measurement n) :
    (meanSlope A j e-meanSlope (swapped A a b) j e)^2 ≤ 1 := by
  cases e with
  | inl i =>
    by_cases hij : i=j
    · subst i
      simp [meanSlope,hj,swapped_j_not A j a b hj hb]
    · simp only [meanSlope,hij,↓reduceIte]
      split_ifs <;> norm_num
  | inr p =>
    simp only [meanSlope,swapped_query_count A p.1 j a b hj ha hb]
    have hid : (-(((p.1 ∩ others A j).card : ℝ)-bit p.2)-
        -(((p.1 ∩ others A j).card : ℝ)+hit p.1 a-hit p.1 b-bit p.2))^2 =
        (hit p.1 a-hit p.1 b)^2 := by ring
    rw [hid]
    unfold hit
    split_ifs <;> norm_num

theorem moving_information_midpoint (A A' : Finset (I n)) (j : I n)
    (hj : j ∉ A) (hj' : j ∉ A') (mu nu eps q : ℝ)
    (e : Measurement n) (he : Legal j q e) :
    information A A' j (mu-eps) (nu-eps) e+
      information A A' j (mu+eps) (nu+eps) e =
      2*information A A' j mu nu e+eps^2*(meanSlope A j e-meanSlope A' j e)^2 := by
  simp_rw [information_eq_mean,actual_mean_affine A j hj q _ e he,
    actual_mean_affine A' j hj' q _ e he]
  ring

theorem adjacent_allocation_midpoint (A : Finset (I n)) (j a b : I n)
    (hj : j ∉ A) (ha : a ∈ A) (hb : b ∈ others A j) (mu nu eps q : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hn : ∑ e ∈ E,w e=1) :
    (∑ e ∈ E,w e*information A (swapped A a b) j (mu-eps) (nu-eps) e)+
      (∑ e ∈ E,w e*information A (swapped A a b) j (mu+eps) (nu+eps) e) ≤
      2*(∑ e ∈ E,w e*information A (swapped A a b) j mu nu e)+eps^2 := by
  have hs : (∑ e ∈ E,w e*information A (swapped A a b) j (mu-eps) (nu-eps) e)+
      (∑ e ∈ E,w e*information A (swapped A a b) j (mu+eps) (nu+eps) e) ≤
      ∑ e ∈ E,w e*(2*information A (swapped A a b) j mu nu e+eps^2) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro e he
    have hm := moving_information_midpoint A (swapped A a b) j hj
      (swapped_j_not A j a b hj hb) mu nu eps q e (hl e he)
    have hc := mul_le_mul_of_nonneg_left (adjacent_relative_slope A j a b hj ha hb e) (sq_nonneg eps)
    have hh : information A (swapped A a b) j (mu-eps) (nu-eps) e+
        information A (swapped A a b) j (mu+eps) (nu+eps) e ≤
        2*information A (swapped A a b) j mu nu e+eps^2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hh (hw e he)]
  have heq : (∑ e ∈ E,w e*(2*information A (swapped A a b) j mu nu e+eps^2)) =
      2*(∑ e ∈ E,w e*information A (swapped A a b) j mu nu e)+eps^2 := by
    simp_rw [mul_add]
    rw [sum_add_distrib]
    have h1 : (∑ e ∈ E,w e*(2*information A (swapped A a b) j mu nu e)) =
        2*(∑ e ∈ E,w e*information A (swapped A a b) j mu nu e) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro e he
      ring
    rw [h1,← sum_mul,hn,one_mul]
  rwa [heq] at hs

/-- Actual legal alternative margins on both sides, with a dimension-free
second-order information correction. -/
theorem moving_adversary_two_margin (A : Finset (I n)) (j : I n) (q lam eps : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (heps : 0 ≤ eps)
    (hlo : eps ≤ 1-lam*(1+root q (scale q)))
    (hup : eps ≤ lam*(1+root q (scale q)))
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) (hn : ∑ e ∈ E,w e=1) :
    ∃ A' : Finset (I n), ∃ nu : ℝ,
      A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧
      0 ≤ nu-eps ∧ nu+eps ≤ 1 ∧
      (∑ e ∈ E,w e*information A A' j ((1-lam)-eps) (nu-eps) e)+
        (∑ e ∈ E,w e*information A A' j ((1-lam)+eps) (nu+eps) e) ≤
        2*rate q lam+eps^2 := by
  obtain ⟨a,ha,b,hb,hcenter⟩ := adjacent_center_witness A j q lam hq hI hj hA hB E w hl hw hn
  have hm := adjacent_allocation_midpoint A j a b hj ha hb (1-lam)
    (1-lam*(1+root q (scale q))) eps q E w hl hw hn
  exact ⟨swapped A a b,1-lam*(1+root q (scale q)),swapped_ne A j a b hb,
    swapped_card A j a b ha hb,swapped_j_not A j a b hj hb,
    by linarith,by linarith,by linarith⟩

#print axioms adjacent_center_witness
#print axioms adjacent_relative_slope
#print axioms moving_information_midpoint
#print axioms adjacent_allocation_midpoint
#print axioms moving_adversary_two_margin
end
end CIGAMF.P13.D6MovingNuisanceRegret
