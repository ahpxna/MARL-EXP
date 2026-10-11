import «LeanD6GaussianQueryDominanceV1»
import «LeanMasterUnknownCalibrationV1»

/-! An A-independent legal scalar design cancels a common additive offset
for every pair of valid labels AND every pair of nuisance margins.
No assertion that this design maximizes the known-calibration game. -/
namespace CIGAMF.P13.D6CalibrationBalancedDesign
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.MasterUnknownCalibration
noncomputable section
variable {n : ℕ}

def weight (j : I n) (q : ℝ) (i : I n) : ℝ :=
  (if i=j then q else 1)/(3*q+1)

lemma scalar_mean_decomposition (A : Finset (I n)) (j i : I n) (hj : j ∉ A)
    (q mu : ℝ) :
    actualMean A j mu (.inl i) = (if i ∈ A then 1 else 0) +
      (if i ∈ others A j then 1-mu else 0) + (if i=j then mu-1 else 0) := by
  rw [actual_mean_affine A j hj q mu (.inl i) (by trivial)]
  by_cases hi : i ∈ A
  · have hij : i ≠ j := by intro h; subst i; exact hj hi
    simp [meanOffset,meanSlope,hi,hij,others]
  · by_cases hij : i=j
    · subst i; simp [meanOffset,meanSlope,hj,others]; ring
    · simp [meanOffset,meanSlope,hi,hij,others]; ring

lemma weighted_mean (A : Finset (I n)) (j : I n) (hj : j ∉ A) (q mu : ℝ)
    (hA : (A.card : ℝ)=q+1) (hB : ((others A j).card : ℝ)=q) :
    (∑ i, weight j q i * actualMean A j mu (.inl i)) = (q+1)/(3*q+1) := by
  have hf : ∀ i, (if i=j then q else (1:ℝ))*actualMean A j mu (.inl i) =
      (if i ∈ A then 1 else 0)+(if i ∈ others A j then 1-mu else 0)+
        (if i=j then q*(mu-1) else 0) := by
    intro i
    rw [scalar_mean_decomposition A j i hj q mu]
    by_cases hij : i=j
    · subst i; simp [hj,others]
    · simp [hij]
  have hs : (∑ i, (if i=j then q else (1:ℝ))*actualMean A j mu (.inl i)) = q+1 := by
    simp_rw [hf]
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
    simp only [Finset.sum_ite_mem, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
    rw [Finset.univ_inter,Finset.univ_inter,hA,hB]
    ring
  unfold weight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,hs]

lemma weight_nonneg (j : I n) (q : ℝ) (hq : 0 ≤ q) (i : I n) :
    0 ≤ weight j q i := by
  unfold weight
  split_ifs <;> positivity

lemma weight_sum (j : I n) (q : ℝ) (hq : 0 ≤ q)
    (hn : (Fintype.card (I n) : ℝ)=2*q+2) : ∑ i, weight j q i=1 := by
  have hf : ∀ i, (if i=j then q else (1:ℝ)) = 1+(if i=j then q-1 else 0) := by
    intro i; split_ifs <;> ring
  unfold weight
  rw [← Finset.sum_div]
  simp_rw [hf]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,
    Finset.sum_ite_eq',Finset.mem_univ,if_true]
  rw [hn]
  have hd : 3*q+1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem all_worlds_balanced (A B : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjB : j ∉ B) (q mu nu : ℝ)
    (hA : (A.card : ℝ)=q+1) (hAc : ((others A j).card : ℝ)=q)
    (hB : (B.card : ℝ)=q+1) (hBc : ((others B j).card : ℝ)=q) :
    cross (weight j q) (fun i => actualMean A j mu (.inl i)-actualMean B j nu (.inl i))
      (fun _ => 1) = 0 := by
  unfold cross
  simp only [mul_one,mul_sub,Finset.sum_sub_distrib]
  rw [weighted_mean A j hjA q mu hA hAc, weighted_mean B j hjB q nu hB hBc]
  ring

theorem actual_no_calibration_penalty (A B : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hjB : j ∉ B) (q mu nu : ℝ) (hq : 0 ≤ q)
    (hA : (A.card : ℝ)=q+1) (hAc : ((others A j).card : ℝ)=q)
    (hB : (B.card : ℝ)=q+1) (hBc : ((others B j).card : ℝ)=q) :
    let d := fun i => actualMean A j mu (.inl i)-actualMean B j nu (.inl i)
    (∀ u, raw (weight j q) d/2 ≤ energy (weight j q) d (fun _ => 1) u) ∧
    energy (weight j q) d (fun _ => 1) 0 = raw (weight j q) d/2 := by
  exact balanced_no_penalty _ _ _ (weight_nonneg j q hq)
    (all_worlds_balanced A B j hjA hjB q mu nu hA hAc hB hBc)

theorem scalar_queries_legal (j : I n) (q : ℝ) (i : I n) : Legal j q (.inl i) := by trivial

#print axioms scalar_mean_decomposition
#print axioms weighted_mean
#print axioms weight_sum
#print axioms all_worlds_balanced
#print axioms actual_no_calibration_penalty
#print axioms scalar_queries_legal
end
end CIGAMF.P13.D6CalibrationBalancedDesign
