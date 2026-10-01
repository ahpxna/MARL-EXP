import «LeanD6AllocationMarginV1»
import «LeanD6AllocationDistributionV1»

/-! Sharp actual-measurement game throughout the nontrivial true-margin
region. The optimal allocation itself is independent of the unknown margin. -/
namespace CIGAMF.P13.D6AllocationMarginSharp
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.P13.D6AllocationSharp CIGAMF.P13.D6AllocationDistribution
open CIGAMF.P13.D6AllocationMargin
noncomputable section
variable {n : ℕ}

theorem actual_joint_margin_bound (A G : Finset (I n)) (j : I n) (h : Bool) (q lam : ℝ)
    (hq : 3 ≤ q) (hj : j ∉ A) (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card) (hsize : (G.card : ℝ) ≤ q) :
    2*(∑ a ∈ A, ∑ b ∈ others A j,
      queryKL A (swapped A a b) G j h (1-lam) (1-lam*(1+root q (scale q)))) ≤
        q*(q+1)*lam^2*value q (scale q) := by
  let T := 1+root q (scale q)
  have he : (∑ a ∈ A, ∑ b ∈ others A j, queryKL A (swapped A a b) G j h (1-lam) (1-lam*T)) =
      4*lam^2*(∑ a ∈ A, ∑ b ∈ others A j, queryKL A (swapped A a b) G j h (1/2) (1-T/2)) := by
    rw [mul_sum]
    apply sum_congr rfl; intro a ha
    rw [mul_sum]
    apply sum_congr rfl; intro b hb
    exact joint_homogeneity A (swapped A a b) G j h hj (swapped_j_not A j a b hj hb) hjG hG lam T
  have hb := actual_joint_dual_bound A G j h q hq hj hA hB hjG hG hsize
  have hm := mul_le_mul_of_nonneg_left hb (sq_nonneg lam)
  change 2*(∑ a ∈ A, ∑ b ∈ others A j,
    queryKL A (swapped A a b) G j h (1-lam) (1-lam*T)) ≤ _
  rw [he]
  dsimp [T]
  nlinarith

theorem actual_scalar_margin_bound (A : Finset (I n)) (j i : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    2*(∑ a ∈ A, ∑ b ∈ others A j,
      scalarKL A (swapped A a b) j i (1-lam) (1-lam*(1+root q (scale q)))) ≤
        q*(q+1)*lam^2*value q (scale q) := by
  let z := root q (scale q)
  have hc := scale_properties q hq
  have hz := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  have hzle : z ≤ 1 := by dsimp [z]; nlinarith [hz.1,hz.2.1]
  have hp : 0 < q := by linarith
  have hk : 0 < q+1 := by linarith
  have he := (div_eq_iff (ne_of_gt (mul_pos hp hk))).mp (dual_value_equals_primal q hq)
  have hem := congrArg (fun x : ℝ => lam^2*x) he
  change lam^2*(q^2*(1+z)^2)=lam^2*(value q (scale q)*(q*(q+1))) at hem
  have hAi : (1-lam*(1+z))^2 ≤ q*lam^2*(1+z)^2 := hI.2.2.2.1
  have hBi : (q+1)*((1-lam)^2+(q-1)*lam^2*z^2) ≤ q^2*lam^2*(1+z)^2 := hI.2.2.2.2
  rw [actual_scalar_margin_sum A j i hj,hA,hB]
  change (if i ∈ A then q*(1-lam*(1+z))^2 else if i=j then
    (q+1)*q*lam^2*z^2 else (q+1)*((1-lam)^2+(q-1)*lam^2*z^2)) ≤ _
  split_ifs
  · have hh := mul_le_mul_of_nonneg_left hAi hp.le
    nlinarith
  · have hj0 := (le_div_iff₀ hk).mp (scalar_dual q z hq hz.1.le hzle).2.2
    have hh := mul_le_mul_of_nonneg_left hj0 (show 0 ≤ q*lam^2 by positivity)
    nlinarith
  · nlinarith

theorem measurement_margin_bound (A : Finset (I n)) (j : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (e : Measurement n) (he : Legal j q e) :
    2*(∑ a ∈ A, ∑ b ∈ others A j,
      information A (swapped A a b) j (1-lam) (1-lam*(1+root q (scale q))) e) ≤
        q*(q+1)*lam^2*value q (scale q) := by
  cases e with
  | inl i => exact actual_scalar_margin_bound A j i q lam hq hI hj hA hB
  | inr p => exact actual_joint_margin_bound A p.1 j p.2 q lam hq hj hA hB he.1 he.2.2 he.2.1

/-- A single actual adversary defeats the whole allocation for every true
margin in Interior. The adversary's nuisance margin is also legal. -/
theorem arbitrary_margin_allocation_upper (A : Finset (I n)) (j : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hlegal : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e) (hnorm : ∑ e ∈ E, w e=1) :
    ∃ A' : Finset (I n), ∃ nu : ℝ,
      A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ E, w e*information A A' j (1-lam) nu e) ≤ rate q lam := by
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
  have hc := scale_properties q hq
  have hz := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  have hnu : 0 ≤ nu ∧ nu ≤ 1 := by
    dsimp [nu,z]
    refine ⟨by linarith [hI.2.2.1], ?_⟩
    have hh := mul_nonneg hI.1.le (show 0 ≤ 1+root q (scale q) by linarith [hz.1])
    linarith
  exact ⟨swapped A a b,nu,swapped_ne A j a b hb,swapped_card A j a b ha hb,
    swapped_j_not A j a b hj hb,hnu.1,hnu.2,hbl⟩

/-- The exact same probability vector serves every true margin in the region. -/
theorem margin_distribution_information (A A' : Finset (I n)) (j : I n) (q lam nu : ℝ) :
    (∑ e ∈ primalQueries A j, primalWeight A j q e*information A A' j (1-lam) nu e) =
      actualPrimalMargin A A' j q lam nu := by
  rw [primal_sum]
  rfl

theorem margin_distribution_lower (A A' : Finset (I n)) (j : I n) (q lam nu : ℝ)
    (hq : 3 ≤ q) (hlam : 0 < lam) (hj : j ∉ A) (hj' : j ∉ A')
    (hcard : A'.card=A.card) (hne : A' ≠ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    rate q lam ≤ ∑ e ∈ primalQueries A j, primalWeight A j q e*information A A' j (1-lam) nu e := by
  rw [margin_distribution_information]
  exact actual_primal_margin_lower A A' j q lam nu hq hlam hj hj' hcard hne hA hB

/-- Sharp information allocation throughout the explicit margin region,
with lower and upper bounds expressed in the same actual-measurement game. -/
theorem sharp_margin_game (A : Finset (I n)) (j : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    (∃ (E : Finset (Measurement n)) (w : Measurement n → ℝ),
      (∀ e ∈ E, Legal j q e) ∧ (∀ e ∈ E, 0 ≤ w e) ∧ (∑ e ∈ E, w e)=1 ∧
      (∀ A' : Finset (I n), j ∉ A' → A'.card=A.card → A' ≠ A → ∀ nu : ℝ,
        0 ≤ nu → nu ≤ 1 → rate q lam ≤ ∑ e ∈ E, w e*information A A' j (1-lam) nu e)) ∧
    (∀ (E : Finset (Measurement n)) (w : Measurement n → ℝ),
      (∀ e ∈ E, Legal j q e) → (∀ e ∈ E, 0 ≤ w e) → (∑ e ∈ E, w e)=1 →
      ∃ A' : Finset (I n), ∃ nu : ℝ,
        A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
        (∑ e ∈ E, w e*information A A' j (1-lam) nu e) ≤ rate q lam) := by
  have hp := primal_distribution A j q hq hj hA hB
  constructor
  · refine ⟨primalQueries A j,primalWeight A j q,hp.1,(fun e _ => hp.2.1 e),hp.2.2,?_⟩
    intro A' hj' hcard hne nu _ _
    exact margin_distribution_lower A A' j q lam nu hq hI.1 hj hj' hcard hne hA hB
  · intro E w hl hw hn
    exact arbitrary_margin_allocation_upper A j q lam hq hI hj hA hB E w hl hw hn

theorem margin_value_attained (A : Finset (I n)) (j : I n) (q lam : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    ∃ A' : Finset (I n), ∃ nu : ℝ,
      A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ primalQueries A j, primalWeight A j q e*information A A' j (1-lam) nu e)=rate q lam := by
  have hp := primal_distribution A j q hq hj hA hB
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hu⟩ :=
    arbitrary_margin_allocation_upper A j q lam hq hI hj hA hB (primalQueries A j) (primalWeight A j q)
      hp.1 (fun e _ => hp.2.1 e) hp.2.2
  exact ⟨A',nu,hne,hcard,hj',hnu,hnu1,
    le_antisymm hu (margin_distribution_lower A A' j q lam nu hq hI.1 hj hj' hcard hne hA hB)⟩

#print axioms actual_joint_margin_bound
#print axioms actual_scalar_margin_bound
#print axioms measurement_margin_bound
#print axioms arbitrary_margin_allocation_upper
#print axioms margin_distribution_information
#print axioms margin_distribution_lower
#print axioms sharp_margin_game
#print axioms margin_value_attained
end
end CIGAMF.P13.D6AllocationMarginSharp
