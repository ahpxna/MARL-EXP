import «LeanD6WidthCostInformationV1»
namespace CIGAMF.P13.D6ScalarWidthRegion
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationFiniteBridge
open CIGAMF.P13.D6AllocationDualBridge CIGAMF.P13.D6AllocationMargin
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6WidthCostInformation
noncomputable section
variable {n : ℕ}

lemma wrong_label_contains_B (A C : Finset (I n)) (j : I n)
    (hne : C ≠ A) (hcard : C.card=A.card) (hjC : j ∉ C) :
    ∃ b,b ∈ others A j ∧ b ∈ C := by
  have hnsub : ¬C ⊆ A := by
    intro h; exact hne (eq_of_subset_of_card_le h hcard.ge)
  obtain ⟨b,hbC,hbA⟩ := not_subset.mp hnsub
  have hbj : b ≠ j := by intro h; subst b; exact hjC hbC
  exact ⟨b,by simp [others,hbA,hbj],hbC⟩

lemma B_changed_scalar (A C : Finset (I n)) (j b : I n) (mu nu q : ℝ)
    (hjA : j ∉ A) (hjC : j ∉ C) (hb : b ∈ others A j) (hbC : b ∈ C) :
    (actualMean A j mu (.inl b)-actualMean C j nu (.inl b))^2=mu^2 := by
  have h := others_not_mem A j b hb
  rw [actual_mean_affine A j hjA q mu _ (by trivial),
    actual_mean_affine C j hjC q nu _ (by trivial)]
  simp [meanOffset,meanSlope,h.1,h.2,hbC]

/-- A single changed B cell provides information independently of nuisance nu.
Thus a true-B scalar design simultaneously separates every wrong label. -/
theorem uniform_B_lower (A C : Finset (I n)) (j : I n) (q mu nu : ℝ)
    (hq : 0<q) (hjA : j ∉ A) (hjC : j ∉ C) (hne : C ≠ A) (hcard : C.card=A.card) :
    mu^2/(2*q) ≤ ∑ b ∈ others A j,
      (actualMean A j mu (.inl b)-actualMean C j nu (.inl b))^2/(2*q) := by
  obtain ⟨b,hb,hbC⟩ := wrong_label_contains_B A C j hne hcard hjC
  have hs := single_le_sum (f:=fun b =>
    (actualMean A j mu (.inl b)-actualMean C j nu (.inl b))^2/(2*q))
    (fun i _ => div_nonneg (sq_nonneg _) (by positivity)) hb
  rwa [B_changed_scalar A C j b mu nu q hjA hjC hb hbC] at hs

theorem scalar_adjacent_mixture_bound (A : Finset (I n)) (j i : I n) (q mu : ℝ)
    (hq : 0<q) (hj : j ∉ A) (hA : (A.card:ℝ)=q+1) (hB : ((others A j).card:ℝ)=q) :
    (∑ a ∈ A,∑ b ∈ others A j,scalarKL A (swapped A a b) j i mu mu)/(q*(q+1)) ≤
      mu^2/(2*q) := by
  have hh := actual_scalar_margin_sum A j i hj (1-mu) 0
  have he : 1-(1-mu)=mu := by ring
  have he' : 1-(1-mu)*(1+0)=mu := by ring
  rw [he,he',hA,hB] at hh
  simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_add,sub_zero] at hh
  apply (div_le_div_iff₀ (by positivity : 0<q*(q+1)) (by positivity : 0<2*q)).mpr
  split_ifs at hh <;> nlinarith [sq_nonneg mu,mul_nonneg hq.le (sq_nonneg mu)]

#print axioms wrong_label_contains_B
#print axioms B_changed_scalar
#print axioms uniform_B_lower
#print axioms scalar_adjacent_mixture_bound
end
end CIGAMF.P13.D6ScalarWidthRegion
