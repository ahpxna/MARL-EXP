import «LeanD6FiniteNuisanceEvaluationV1»
import «LeanD6ApproximateProfileV1»

namespace CIGAMF.P13.D6ApproximateActualEvaluator
open scoped BigOperators
open Finset Set
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.D6FiniteNuisanceEvaluation
open CIGAMF.P13.D6ApproximateAnswers CIGAMF.P13.D6ApproximateProfile
open CIGAMF.P13.OpenQuadraticProfile
noncomputable section
variable {n : ℕ}

lemma curvature_nonneg (B : Finset (I n)) (j : I n) (E : Finset (Measurement n))
    (w : Measurement n → ℝ) (hw : ∀ e ∈ E,0 ≤ w e) : 0 ≤ curvature B j E w := by
  exact sum_nonneg (fun e he => mul_nonneg (hw e he) (sq_nonneg _))

lemma zero_curvature_cross (A B : Finset (I n)) (j : I n) (mu : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hw : ∀ e ∈ E,0 ≤ w e) (hc : curvature B j E w=0) : crossTerm A B j mu E w=0 := by
  have hsum : ∀ e ∈ E,w e*(meanSlope B j e)^2=0 := by
    exact (sum_eq_zero_iff_of_nonneg (fun e he => mul_nonneg (hw e he) (sq_nonneg _))).mp hc
  unfold crossTerm
  apply sum_eq_zero
  intro e he
  rcases mul_eq_zero.mp (hsum e he) with hw0 | hs0
  · simp [hw0]
  · have hs := sq_eq_zero_iff.mp hs0
    simp [hs]

def evaluator (A B C : Finset (I n)) (j : I n) (mu eps : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : ℝ :=
  let a := constantTerm A C j mu E w
  let b := crossTerm A C j mu E w
  let c := curvature C j E w
  let U := min 1 (2-2*eps/(exchange C B : ℝ))
  let p := clipped c b U
  if c=0 then a/2 else (a-2*b*p+c*p^2)/2

def labelCosts (A B C : Finset (I n)) (j : I n) (mu eps : ℝ)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ) : Set ℝ :=
  (fun nu => ∑ e ∈ E,w e*information A C j mu nu e) '' badDomain (exchange C B) eps

theorem actual_label_infimum (A B C : Finset (I n)) (j : I n) (hjC : j ∉ C)
    (q mu eps : ℝ) (he : 0 ≤ eps) (hd : eps < (exchange C B : ℝ))
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E,Legal j q e) (hw : ∀ e ∈ E,0 ≤ w e) :
    sInf (labelCosts A B C j mu eps E w)=evaluator A B C j mu eps E w := by
  have hdpos : 0 < exchange C B := by
    have h : (0 : ℝ) < exchange C B := lt_of_le_of_lt he hd
    exact_mod_cast h
  have hn : (badDomain (exchange C B) eps).Nonempty := by
    obtain ⟨nu,hnu⟩ := (bad_nuisance_nonempty _ eps he).mpr hd
    exact ⟨nu,hnu⟩
  have hf : (fun nu => ∑ e ∈ E,w e*information A C j mu nu e) =
      (fun nu => (constantTerm A C j mu E w-2*crossTerm A C j mu E w*nu+
        curvature C j E w*nu^2)/2) := by
    funext nu
    exact information_quadratic A C j hjC q mu nu E w hl
  unfold labelCosts
  rw [hf]
  unfold evaluator
  dsimp
  by_cases hc : curvature C j E w=0
  · rw [if_pos hc]
    have hb := zero_curvature_cross A C j mu E w hw hc
    simp only [hc,hb,mul_zero,zero_mul,sub_zero,add_zero]
    have himg : (fun _ : ℝ => constantTerm A C j mu E w/2) '' badDomain (exchange C B) eps =
        {constantTerm A C j mu E w/2} := by
      ext v
      simp only [Set.mem_image,Set.mem_singleton_iff]
      constructor
      · rintro ⟨x,hx,rfl⟩; rfl
      · intro h; obtain ⟨x,hx⟩ := hn; exact ⟨x,hx,h.symm⟩
    rw [himg]
    exact csInf_singleton _
  · rw [if_neg hc]
    have hcpos : 0 < curvature C j E w := lt_of_le_of_ne
      (curvature_nonneg C j E w hw) (Ne.symm hc)
    have h := positive_curvature_bad_inf (exchange C B) hdpos eps
      (constantTerm A C j mu E w/2) (crossTerm A C j mu E w/2)
      (curvature C j E w/2) hd (by positivity)
    have hclip : clipped (curvature C j E w/2) (crossTerm A C j mu E w/2)
        (min 1 (2-2*eps/(exchange C B : ℝ))) =
      clipped (curvature C j E w) (crossTerm A C j mu E w)
        (min 1 (2-2*eps/(exchange C B : ℝ))) := by
      unfold clipped
      congr 2
      field_simp
    dsimp at h
    rw [hclip] at h
    have heq : (fun nu => (constantTerm A C j mu E w-2*crossTerm A C j mu E w*nu+
        curvature C j E w*nu^2)/2) =
      (fun nu => constantTerm A C j mu E w/2-2*(crossTerm A C j mu E w/2)*nu+
        (curvature C j E w/2)*nu^2) := by funext nu; ring
    rw [heq,h]
    ring

#print axioms curvature_nonneg
#print axioms zero_curvature_cross
#print axioms actual_label_infimum
end
end CIGAMF.P13.D6ApproximateActualEvaluator
