import «LeanD6AllocationSharpV1»

/-! Non-singleton true-margin regime of the actual D6 allocation game.
`lambda=1-mu`. The same two-orbit allocation is optimal throughout an explicit
semialgebraic region; this is derived from actual observations, not an assumed
quadratic experiment. Unit variance/cost and the existing Legal query library
are retained. Sequential sample complexity is not claimed. -/
namespace CIGAMF.P13.D6AllocationMargin
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ExpandedMeasurements
open CIGAMF.P13.D6AllocationFiniteBridge CIGAMF.P13.D6AllocationPrimalBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.P13.D6AllocationSharp
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

def rate (q lam : ℝ) : ℝ := lam^2*value q (scale q)/2

/-- Explicit region where the least-favourable margin is feasible and scalar
queries do not beat the two joint-query orbits. These are scalar polynomial
inequalities, not assumptions of statistical optimality. -/
def Interior (q lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ 1 ∧ lam*(1+root q (scale q)) ≤ 1 ∧
  (1-lam*(1+root q (scale q)))^2 ≤ q*lam^2*(1+root q (scale q))^2 ∧
  (q+1)*((1-lam)^2+(q-1)*lam^2*(root q (scale q))^2) ≤
    q^2*lam^2*(1+root q (scale q))^2

/-- A whole interval belongs to Interior, so this result is not restricted to
mu=1/2. The exact region may extend below lambda=1/2 as well. -/
theorem interval_in_interior (q lam : ℝ) (hq : 3 ≤ q) (hlam : 1/2 ≤ lam)
    (hupper : lam*(1+root q (scale q)) ≤ 1) : Interior q lam := by
  let z := root q (scale q)
  have hc := scale_properties q hq
  have hz := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  have hzpos : 0 ≤ z := hz.1.le
  have hzle : z ≤ 1 := by dsimp [z]; nlinarith [hz.1, hz.2.1]
  have hl : 0 < lam := by linarith
  have hlu : lam ≤ 1 := by nlinarith [mul_nonneg hl.le hzpos]
  have hAl : 0 ≤ 1-lam*(1+z) := by linarith
  have hAh : 1-lam*(1+z) ≤ lam*(1-z) := by nlinarith
  have hAr : 0 ≤ lam*(1-z) := mul_nonneg hl.le (by linarith)
  have hAsq : (1-lam*(1+z))^2 ≤ (lam*(1-z))^2 := by nlinarith
  have hs := scalar_dual q z hq hzpos hzle
  have hk : 0 < q+1 := by linarith
  have hp : 0 < q := by linarith
  have hA0 := (div_le_div_iff_of_pos_right hk).mp hs.1
  have hA1 := mul_le_mul_of_nonneg_left hA0 (sq_nonneg lam)
  have hB0 := (div_le_div_iff₀ hp hk).mp hs.2.1
  have hB1 := mul_le_mul_of_nonneg_left hB0 (sq_nonneg lam)
  have hBsq : (1-lam)^2 ≤ lam^2 := by nlinarith
  have hB2 := mul_le_mul_of_nonneg_left hBsq hk.le
  exact ⟨hl,hlu,hupper,by nlinarith,by nlinarith⟩

theorem half_in_interior (q : ℝ) (hq : 3 ≤ q) : Interior q (1/2) := by
  have hc := scale_properties q hq
  have hz := root_properties q _ hq hc.1 hc.2.1 hc.2.2
  exact interval_in_interior q _ hq (by norm_num) (by nlinarith [hz.1,hz.2.1])

/-- Homogeneity for actual joint measurements, with arbitrary true and
alternative margins. The gate offsets cancel in the actual world difference. -/
theorem joint_homogeneity (A A' G : Finset (I n)) (j : I n) (h : Bool)
    (hj : j ∉ A) (hj' : j ∉ A') (hjG : j ∉ G) (hG : h=false → 2 ≤ G.card)
    (lam t : ℝ) :
    queryKL A A' G j h (1-lam) (1-lam*t)=
      4*lam^2*queryKL A A' G j h (1/2) (1-t/2) := by
  unfold queryKL
  rw [actual_query_mean A G j h hj hjG hG,
    actual_query_mean A' G j h hj' hjG hG,
    actual_query_mean A G j h hj hjG hG,
    actual_query_mean A' G j h hj' hjG hG]
  ring

def actualPrimalMargin (A A' : Finset (I n)) (j : I n) (q lam nu : ℝ) : ℝ :=
  ((1-weight q (scale q))/(q+1))*(∑ a ∈ A,
    queryKL A A' (A.erase a) j false (1-lam) nu) +
      weight q (scale q)*queryKL A A' (others A j) j true (1-lam) nu

/-- The same fixed allocation scales by lambda squared; it needs no estimate
of the true margin anywhere inside the regime. -/
theorem primal_homogeneity (A A' : Finset (I n)) (j : I n) (q lam t : ℝ)
    (hj : j ∉ A) (hj' : j ∉ A') (hA : 4 ≤ A.card) :
    actualPrimalMargin A A' j q lam (1-lam*t)=
      4*lam^2*actualPrimal A A' j q (scale q) t := by
  have he : (∑ a ∈ A, queryKL A A' (A.erase a) j false (1-lam) (1-lam*t)) =
      4*lam^2*(∑ a ∈ A, queryKL A A' (A.erase a) j false (1/2) (1-t/2)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro a ha
    have hl := erased_query_legal A j a hj ha hA
    exact joint_homogeneity A A' (A.erase a) j false hj hj' hl.1 (by intro _; exact hl.2) lam t
  unfold actualPrimalMargin actualPrimal
  rw [he, joint_homogeneity A A' (others A j) j true hj hj' (by simp [others]) (by simp) lam t]
  ring

/-- Actual primal guarantee for every different legal A' and every real
alternative margin; no Interior hypothesis is needed for this direction. -/
theorem actual_primal_margin_lower (A A' : Finset (I n)) (j : I n) (q lam nu : ℝ)
    (hq : 3 ≤ q) (hlam : 0 < lam) (hj : j ∉ A) (hj' : j ∉ A')
    (hcard : A'.card=A.card) (hne : A' ≠ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    rate q lam ≤ actualPrimalMargin A A' j q lam nu := by
  let t := (1-nu)/lam
  have ht : 1-lam*t=nu := by dsimp [t]; field_simp [ne_of_gt hlam]; ring
  have hd := alternative_distance_bounds A A' j q hj' hcard hne hB
  have hbase := actual_primal_lower A A' j q t hq hj hj' hcard hA hB hd.1 hd.2
  have hmul := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 4*lam^2 by positivity)
  have hAn : 4 ≤ A.card := by exact_mod_cast (show (4:ℝ) ≤ A.card by linarith)
  rw [← ht, primal_homogeneity A A' j q lam t hj hj' hAn]
  unfold rate
  nlinarith

/-- General-margin pointwise scalar identities for an actual world swap. -/
theorem scalar_A_margin_point (A : Finset (I n)) (j i a b : I n) (hj : j ∉ A)
    (hi : i ∈ A) (ha : a ∈ A) (hb : b ∈ others A j) (lam z : ℝ) :
    2*scalarKL A (swapped A a b) j i (1-lam) (1-lam*(1+z))=
      (1-lam*(1+z))^2*hit {i} a := by
  have hh := others_not_mem A j b hb
  have hij : i ≠ j := by intro he; subst i; exact hj hi
  have hib : i ≠ b := by intro he; subst i; exact hh.1 hi
  unfold scalarKL
  rw [world_response A j hj, world_response (swapped A a b) j (swapped_j_not A j a b hj hb)]
  by_cases hia : i=a
  · subst a
    simp [CIGAMF.P13.D6Threshold.slope,hi,hij,hib,swapped,hit,bit_true]
    ring
  · simp [CIGAMF.P13.D6Threshold.slope,hi,hib,hia,Ne.symm hia,swapped,hit,bit_true]

theorem scalar_B_margin_point (A : Finset (I n)) (j i a b : I n) (hj : j ∉ A)
    (hi : i ∈ others A j) (hb : b ∈ others A j) (lam z : ℝ) :
    2*scalarKL A (swapped A a b) j i (1-lam) (1-lam*(1+z))=
      lam^2*z^2+((1-lam)^2-lam^2*z^2)*hit {i} b := by
  have hh := others_not_mem A j i hi
  unfold scalarKL
  rw [world_response A j hj, world_response (swapped A a b) j (swapped_j_not A j a b hj hb)]
  by_cases hib : i=b
  · subst b
    simp [CIGAMF.P13.D6Threshold.slope,hh.1,hh.2,swapped,hit,bit_true]
    ring
  · simp [CIGAMF.P13.D6Threshold.slope,hh.1,hh.2,hib,Ne.symm hib,swapped,hit,bit_true]
    ring

theorem scalar_j_margin_point (A : Finset (I n)) (j a b : I n) (hj : j ∉ A)
    (hb : b ∈ others A j) (lam z : ℝ) :
    2*scalarKL A (swapped A a b) j j (1-lam) (1-lam*(1+z))=lam^2*z^2 := by
  unfold scalarKL
  rw [world_response A j hj, world_response (swapped A a b) j (swapped_j_not A j a b hj hb)]
  simp only [CIGAMF.P13.D6Threshold.slope,hj,swapped_j_not A j a b hj hb,↓reduceIte,bit_true,mul_one]
  ring

theorem actual_scalar_margin_sum (A : Finset (I n)) (j i : I n) (hj : j ∉ A) (lam z : ℝ) :
    2*(∑ a ∈ A, ∑ b ∈ others A j, scalarKL A (swapped A a b) j i (1-lam) (1-lam*(1+z))) =
      if i ∈ A then ((others A j).card : ℝ)*(1-lam*(1+z))^2 else if i=j then
        (A.card : ℝ)*(others A j).card*lam^2*z^2 else
        (A.card : ℝ)*((1-lam)^2+(((others A j).card : ℝ)-1)*lam^2*z^2) := by
  rw [mul_sum]
  simp_rw [mul_sum]
  by_cases hiA : i ∈ A
  · rw [ite_eq_left hiA]
    have he : (∑ a ∈ A, ∑ b ∈ others A j,
        2*scalarKL A (swapped A a b) j i (1-lam) (1-lam*(1+z))) =
        ∑ a ∈ A, ∑ _b ∈ others A j, (1-lam*(1+z))^2*hit {i} a := by
      apply sum_congr rfl; intro a ha
      apply sum_congr rfl; intro b hb
      exact scalar_A_margin_point A j i a b hj hiA ha hb lam z
    rw [he]
    simp only [sum_const,nsmul_eq_mul,← mul_sum,sum_singleton_hit A i hiA]
    ring
  · rw [ite_eq_right hiA]
    by_cases hij : i=j
    · subst i
      rw [ite_eq_left rfl]
      have he : (∑ a ∈ A, ∑ b ∈ others A j,
          2*scalarKL A (swapped A a b) j j (1-lam) (1-lam*(1+z))) =
          ∑ _a ∈ A, ∑ _b ∈ others A j, lam^2*z^2 := by
        apply sum_congr rfl; intro a ha
        apply sum_congr rfl; intro b hb
        exact scalar_j_margin_point A j a b hj hb lam z
      rw [he]
      simp [mul_assoc]
    · rw [ite_eq_right hij]
      have hiB : i ∈ others A j := by simp [others,hiA,hij]
      have he : (∑ a ∈ A, ∑ b ∈ others A j,
          2*scalarKL A (swapped A a b) j i (1-lam) (1-lam*(1+z))) =
          ∑ _a ∈ A, ∑ b ∈ others A j, (lam^2*z^2+((1-lam)^2-lam^2*z^2)*hit {i} b) := by
        apply sum_congr rfl; intro a ha
        apply sum_congr rfl; intro b hb
        exact scalar_B_margin_point A j i a b hj hiB hb lam z
      rw [he]
      simp only [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,sum_singleton_hit (others A j) i hiB]
      ring

#print axioms interval_in_interior
#print axioms half_in_interior
#print axioms joint_homogeneity
#print axioms primal_homogeneity
#print axioms actual_primal_margin_lower
#print axioms actual_scalar_margin_sum
end
end CIGAMF.P13.D6AllocationMargin
