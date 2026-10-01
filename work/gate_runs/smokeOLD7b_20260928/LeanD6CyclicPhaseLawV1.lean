import «LeanD6CyclicPhaseDesignV1»
import «LeanFiniteGaussianSumLawV1»

/-! Repeated actual D6 off queries: A-free estimator, exact Gaussian law and variance. -/
namespace CIGAMF.P13.D6CyclicPhaseLaw
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6CyclicPhaseDesign
noncomputable section
variable {n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]

def observations (G : C → Finset (I n)) (A : Finset (I n)) (j : I n)
    (mu : ℝ) (L : ℕ) : Measure (Fin L × C → ℝ) :=
  FiniteGaussianSumLaw.law (fun t => actualMean A j mu (.inr (G t.2,false)))

def estimate (q L : ℕ) (x : Fin L × C → ℝ) : ℝ :=
  ((L:ℝ)*Fintype.card C + (L:ℝ)*(q:ℝ)^2 - ∑ t,x t) / ((L:ℝ)*(q:ℝ)^2)

theorem repeated_sum_law (G : C → Finset (I n)) (A : Finset (I n))
    (j : I n) (q L : ℕ) (mu : ℝ)
    (hm : (∑ t,actualMean A j mu (.inr (G t,false))) =
      Fintype.card C + (q:ℝ)^2*(1-mu)) :
    HasLaw (fun x : Fin L × C → ℝ => ∑ t,x t)
      (gaussianReal ((L:ℝ)*(Fintype.card C+(q:ℝ)^2*(1-mu)))
        ((L*Fintype.card C:ℕ):NNReal)) (observations G A j mu L) := by
  have h := FiniteGaussianSumLaw.sum_law
    (fun t : Fin L × C => actualMean A j mu (.inr (G t.2,false)))
  simpa only [Fintype.sum_prod_type,hm,sum_const,card_univ,Fintype.card_fin,
    nsmul_eq_mul,Fintype.card_prod,observations] using h

theorem estimate_law (G : C → Finset (I n)) (A : Finset (I n))
    (j : I n) (q L : ℕ) (hq : 0 < q) (hL : 0 < L) (mu : ℝ)
    (hm : (∑ t,actualMean A j mu (.inr (G t,false))) =
      Fintype.card C + (q:ℝ)^2*(1-mu)) :
    HasLaw (estimate (C:=C) q L)
      (gaussianReal mu (((L*Fintype.card C:ℕ):NNReal) /
        NNReal.mk (((L:ℝ)*(q:ℝ)^2)^2) (sq_nonneg _))) (observations G A j mu L) := by
  have h := gaussianReal_div_const
    (gaussianReal_const_sub (repeated_sum_law G A j q L mu hm)
      ((L:ℝ)*Fintype.card C+(L:ℝ)*(q:ℝ)^2)) ((L:ℝ)*(q:ℝ)^2)
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have he : ((L:ℝ)*Fintype.card C+(L:ℝ)*(q:ℝ)^2 -
      (L:ℝ)*(Fintype.card C+(q:ℝ)^2*(1-mu))) / ((L:ℝ)*(q:ℝ)^2) = mu := by
    field_simp; ring
  rw [he] at h
  unfold estimate
  exact h

theorem estimate_variance (G : C → Finset (I n)) (A : Finset (I n))
    (j : I n) (q L : ℕ) (hq : 0 < q) (hL : 0 < L)
    (hC : 0 < Fintype.card C) (mu : ℝ)
    (hm : (∑ t,actualMean A j mu (.inr (G t,false))) =
      Fintype.card C + (q:ℝ)^2*(1-mu)) :
    variance (estimate (C:=C) q L) (observations G A j mu L) =
      (Fintype.card C:ℝ)^2 / ((q:ℝ)^4*((L:ℝ)*Fintype.card C)) := by
  have h := estimate_law G A j q L hq hL mu hm
  have hv := variance_id_map h.aemeasurable
  rw [h.map_eq,variance_id_gaussianReal] at hv
  have hq0 : (q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hL0 : (L:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  have hC0 : (Fintype.card C:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
  rw [← hv]
  push_cast
  field_simp
  <;> ring

theorem actual_design_law_exists (q : ℕ) (hq : 3 ≤ q) (j : I (2*q+1)) :
    ∃ G : ZMod (2*q+1) → Finset (I (2*q+1)),
      (∀ t,Legal j q (.inr (G t,false)) ∧ (G t).card=q) ∧
      ∀ A : Finset (I (2*q+1)), j ∉ A → (others A j).card=q →
      ∀ L : ℕ, 0 < L → ∀ mu : ℝ,
        HasLaw (estimate (C:=ZMod (2*q+1)) q L)
          (gaussianReal mu (((L*(2*q+1):ℕ):NNReal) /
            NNReal.mk (((L:ℝ)*(q:ℝ)^2)^2) (sq_nonneg _)))
          (observations G A j mu L) := by
  obtain ⟨G,hlegal,hm⟩ := design_exists q hq j
  refine ⟨G,hlegal,?_⟩
  intro A hj hB L hL mu
  have h := estimate_law G A j q L (by omega) hL mu (by simpa using hm A hj hB mu)
  simpa using h

#print axioms repeated_sum_law
#print axioms estimate_law
#print axioms estimate_variance
#print axioms actual_design_law_exists
end
end CIGAMF.P13.D6CyclicPhaseLaw
