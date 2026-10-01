import «LeanD6GaussianQueryDominanceV1»

/-! A nuisance-free discovery contrast built from four actual legal queries.
This is a mean identity and deterministic decoding margin. It is not an
adaptive stopping-time or Gamma-optimality theorem. -/
namespace CIGAMF.P13.D6NuisanceFreeDiscovery
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance
noncomputable section
variable {n : ℕ}

def label (A : Finset (I n)) (i : I n) : ℝ := if i ∈ A then 0 else 1

lemma singleton_mean (A : Finset (I n)) (j i : I n) (hj : j ∉ A)
    (hi : i ≠ j) (mu : ℝ) :
    actualMean A j mu (.inl i) = 1-mu*label A i := by
  rw [actual_mean_affine A j hj 2 mu _ (by trivial)]
  by_cases h : i ∈ A <;> simp [meanOffset,meanSlope,label,h,hi] <;> ring

lemma pair_legal (j i k : I n) (hi : i ≠ j) (hk : k ≠ j) (hik : i ≠ k)
    (q : ℝ) (hq : 2 ≤ q) : Legal j q (.inr ({i,k},false)) := by
  have hc : ({i,k} : Finset (I n)).card = 2 := by simp [hik]
  refine ⟨by simp [Ne.symm hi,Ne.symm hk], ?_, ?_⟩
  · simpa [hc] using hq
  · intro _; rw [hc]

lemma pair_mean (A : Finset (I n)) (j i k : I n) (hj : j ∉ A)
    (hi : i ≠ j) (hk : k ≠ j) (hik : i ≠ k) (mu : ℝ) :
    actualMean A j mu (.inr ({i,k},false)) =
      1+(1-mu)*(label A i+label A k) := by
  have hc : (({i,k} ∩ others A j).card : ℝ) = label A i+label A k := by
    by_cases hia : i ∈ A <;> by_cases hka : k ∈ A <;>
      norm_num [others,label,hia,hka,hi,hk,hik]
  rw [actual_mean_affine A j hj 2 mu _ (pair_legal j i k hi hk hik 2 (by norm_num))]
  simp only [meanOffset,meanSlope,Bool.false_eq_true,↓reduceIte,bit_false,sub_zero,hc]
  ring

/-- A and mu are both unknown to this fixed four-query design. The anchor a
and helper k are chosen by indices, not by membership in A. -/
theorem actual_contrast (A : Finset (I n)) (j a i k : I n) (hj : j ∉ A)
    (ha : a ≠ j) (hi : i ≠ j) (hk : k ≠ j) (hak : a ≠ k) (hik : i ≠ k)
    (mu : ℝ) :
    actualMean A j mu (.inl a)-actualMean A j mu (.inl i)+
      actualMean A j mu (.inr ({i,k},false))-
      actualMean A j mu (.inr ({a,k},false)) = label A i-label A a := by
  rw [singleton_mean A j a hj ha,singleton_mean A j i hj hi,
      pair_mean A j i k hj hi hk hik,pair_mean A j a k hj ha hk hak]
  ring

/-- Uniform error below one half separates every B coordinate from every A
coordinate, even when the anchor belongs to the unknown B set. -/
theorem decode_gap (A : Finset (I n)) (a i l : I n) (score : I n → ℝ)
    (hi : i ∉ A) (hl : l ∈ A)
    (hsi : |score i-(label A i-label A a)| < 1/2)
    (hsl : |score l-(label A l-label A a)| < 1/2) : score l < score i := by
  have h1 := (abs_lt.mp hsi).1
  have h2 := (abs_lt.mp hsl).2
  simp only [label,hi,hl,↓reduceIte] at h1 h2
  linarith

#print axioms pair_legal
#print axioms actual_contrast
#print axioms decode_gap
end
end CIGAMF.P13.D6NuisanceFreeDiscovery
