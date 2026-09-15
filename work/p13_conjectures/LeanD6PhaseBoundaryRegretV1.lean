import «LeanD6PhaseTestingInformationV1»
import «LeanD6AllocationMarginSharpV1»

/-! A common actual-world dual controls allocation regret on BOTH sides of
an interior margin. This is the deterministic foundation of a local statistical
lower bound. No total-variation, Gaussian testing or stopping theorem is assumed.
The same alternative world and nuisance are used on both sides, after the full
allocation is fixed. -/
namespace CIGAMF.P13.D6PhaseBoundaryRegret
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6PhaseTestingInformation
open CIGAMF.P13.D6AllocationMargin CIGAMF.P13.D6AllocationMarginSharp
open CIGAMF.P13.D6ExpandedAllocation
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
noncomputable section
variable {n : ℕ}

def curvature (A : Finset (I n)) (j : I n) : Measurement n → ℝ
  | .inl i => if i ∈ A then 0 else 1
  | .inr (G,h) => (((G ∩ others A j).card : ℝ)-bit h)^2

theorem curvature_bound (A : Finset (I n)) (j : I n) (q : ℝ) (hq : 1 ≤ q)
    (e : Measurement n) (he : Legal j q e) : curvature A j e ≤ q^2 := by
  cases e with
  | inl i => dsimp [curvature]; split_ifs <;> nlinarith
  | inr p => exact joint_sensitivity_bound A p.1 j p.2 q hq he.2.1

/-- Actual means are affine in the true margin; the exact second difference
of information is independent of the alternative world and nuisance. -/
theorem information_midpoint (A A' : Finset (I n)) (j : I n) (hj : j ∉ A)
    (mu epsilon nu q : ℝ) (e : Measurement n) (he : Legal j q e) :
    information A A' j (mu-epsilon) nu e + information A A' j (mu+epsilon) nu e =
      2*information A A' j mu nu e+epsilon^2*curvature A j e := by
  cases e with
  | inl i =>
    change scalarKL A A' j i (mu-epsilon) nu+scalarKL A A' j i (mu+epsilon) nu =
      2*scalarKL A A' j i mu nu+epsilon^2*(if i ∈ A then 0 else 1)
    unfold scalarKL
    rw [world_response A j hj,world_response A j hj,world_response A j hj]
    by_cases hi : i ∈ A
    · simp [CIGAMF.P13.D6Threshold.slope,hi,bit_true]
      <;> ring
    · by_cases hij : i=j
      · simp [CIGAMF.P13.D6Threshold.slope,hi,hj,hij,bit_true]
        <;> ring
      · simp [CIGAMF.P13.D6Threshold.slope,hi,hj,hij,bit_true]
        <;> ring
  | inr p =>
    change queryKL A A' p.1 j p.2 (mu-epsilon) nu+queryKL A A' p.1 j p.2 (mu+epsilon) nu =
      2*queryKL A A' p.1 j p.2 mu nu+epsilon^2*(((p.1 ∩ others A j).card : ℝ)-bit p.2)^2
    unfold queryKL
    rw [actual_query_mean A p.1 j p.2 hj he.1 he.2.2,
      actual_query_mean A p.1 j p.2 hj he.1 he.2.2,
      actual_query_mean A p.1 j p.2 hj he.1 he.2.2]
    ring

theorem allocation_midpoint_upper (A A' : Finset (I n)) (j : I n) (q : ℝ)
    (hq : 1 ≤ q) (hj : j ∉ A) (mu epsilon nu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e) (hn : ∑ e ∈ E, w e=1) :
    (∑ e ∈ E,w e*information A A' j (mu-epsilon) nu e)+
      (∑ e ∈ E,w e*information A A' j (mu+epsilon) nu e) ≤
      2*(∑ e ∈ E,w e*information A A' j mu nu e)+epsilon^2*q^2 := by
  have hsum : (∑ e ∈ E,w e*information A A' j (mu-epsilon) nu e)+
      (∑ e ∈ E,w e*information A A' j (mu+epsilon) nu e) =
      2*(∑ e ∈ E,w e*information A A' j mu nu e)+
        epsilon^2*(∑ e ∈ E,w e*curvature A j e) := by
    simp_rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl; intro e he
    have hh := information_midpoint A A' j hj mu epsilon nu q e (hl e he)
    have hh' := congrArg (fun x : ℝ => w e*x) hh
    nlinarith [hh']
  have hb : (∑ e ∈ E,w e*curvature A j e) ≤ q^2 := by
    calc
      _ ≤ ∑ e ∈ E,w e*q^2 := by
        apply sum_le_sum; intro e he
        exact mul_le_mul_of_nonneg_left (curvature_bound A j q hq e (hl e he)) (hw e he)
      _ = _ := by rw [← sum_mul,hn,one_mul]
  rw [hsum]
  linarith [mul_le_mul_of_nonneg_left hb (sq_nonneg epsilon)]

/-- One actual admissible alternative simultaneously bounds the sum of
information on both sides of every margin in the already proved interval. -/
theorem common_adversary_two_margin (A : Finset (I n)) (j : I n) (q lam epsilon : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e) (hn : ∑ e ∈ E,w e=1) :
    ∃ A' : Finset (I n), ∃ nu : ℝ,
      A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
      (∑ e ∈ E,w e*information A A' j ((1-lam)-epsilon) nu e)+
        (∑ e ∈ E,w e*information A A' j ((1-lam)+epsilon) nu e) ≤
        2*rate q lam+epsilon^2*q^2 := by
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hcenter⟩ :=
    arbitrary_margin_allocation_upper A j q lam hq hI hj hA hB E w hl hw hn
  have hh := allocation_midpoint_upper A A' j q (by linarith) hj (1-lam) epsilon nu E w hl hw hn
  exact ⟨A',nu,hne,hcard,hj',hnu,hnu1,by linarith⟩

/-- Substitute any two established achievable rates for Gminus/Gplus. This
is a lower bound against every legal allocation, with actual information
regrets witnessed by a single real alternative. -/
theorem common_adversary_regret_separation (A : Finset (I n)) (j : I n) (q lam epsilon : ℝ)
    (hq : 3 ≤ q) (hI : Interior q lam) (hj : j ∉ A)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e) (hn : ∑ e ∈ E,w e=1)
    (Gminus Gplus : ℝ) :
    ∃ A' : Finset (I n), ∃ nu : ℝ,
      A' ≠ A ∧ A'.card=A.card ∧ j ∉ A' ∧ 0 ≤ nu ∧ nu ≤ 1 ∧
      Gminus+Gplus-2*rate q lam-epsilon^2*q^2 ≤
      (Gminus-∑ e ∈ E,w e*information A A' j ((1-lam)-epsilon) nu e)+
      (Gplus-∑ e ∈ E,w e*information A A' j ((1-lam)+epsilon) nu e) := by
  obtain ⟨A',nu,hne,hcard,hj',hnu,hnu1,hbound⟩ :=
    common_adversary_two_margin A j q lam epsilon hq hI hj hA hB E w hl hw hn
  exact ⟨A',nu,hne,hcard,hj',hnu,hnu1,by linarith⟩

#print axioms curvature_bound
#print axioms information_midpoint
#print axioms allocation_midpoint_upper
#print axioms common_adversary_two_margin
#print axioms common_adversary_regret_separation
end
end CIGAMF.P13.D6PhaseBoundaryRegret
