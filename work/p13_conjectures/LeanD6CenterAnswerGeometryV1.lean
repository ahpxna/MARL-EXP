import «LeanD6ApproximateActualEvaluatorV1»

/-!
# Boundary obstruction for a newly admissible approximate answer

At the exact tolerance at which a noncentral answer enters the good-answer
set, moving only the nuisance of the true label makes that answer strictly bad
at arbitrarily small information cost.  The statement deliberately assumes a
positive true nuisance; the path is unavailable at `mu = 0`.
-/
namespace CIGAMF.P13.D6CenterAnswerGeometry

open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6MovingNuisanceRegret
open CIGAMF.P13.D6FiniteNuisanceEvaluation
open CIGAMF.P13.D6ApproximateAnswers
noncomputable section
variable {n : ℕ}

theorem boundary_same_label_bad (d : ℕ) (hd : 0 < d) (mu eta : ℝ)
    (hmu : mu ≤ 1) (heta : 0 < eta) (hle : eta ≤ mu) :
    BadNuisance d ((2-mu)*(d:ℝ)/2) (mu-eta) := by
  refine ⟨by linarith, by linarith, ?_⟩
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  nlinarith

/-- Along that same-label nuisance path, every actual D6 measurement has a
quadratic information cost whose coefficient is its true-label mean slope. -/
theorem same_label_path_information (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (q mu eta : ℝ) (e : Measurement n) (he : Legal j q e) :
    information A A j mu (mu-eta) e = (meanSlope A j e)^2*eta^2/2 := by
  rw [information_eq_mean,actual_mean_affine A j hj q mu e he,
    actual_mean_affine A j hj q (mu-eta) e he]
  ring

theorem same_label_path_sum (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (q mu eta : ℝ) (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E, Legal j q e) :
    (∑ e ∈ E, w e * information A A j mu (mu-eta) e) =
      eta^2/2 * curvature A j E w := by
  unfold curvature
  rw [mul_sum]
  apply sum_congr rfl
  intro e he
  rw [same_label_path_information A j hj q mu eta e (hl e he)]
  ring

/-- For every positive target cost there is a positive nuisance move on the
bad side of the boundary with smaller information, provided the allocation's
curvature is finite and nonnegative. -/
theorem boundary_arbitrarily_small (A B : Finset (I n)) (j : I n) (hj : j ∉ A)
    (q mu : ℝ) (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
    (E : Finset (Measurement n)) (w : Measurement n → ℝ)
    (hl : ∀ e ∈ E, Legal j q e) (hw : ∀ e ∈ E, 0 ≤ w e)
    (hd : 0 < exchange A B) (target : ℝ) (htarget : 0 < target) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ mu ∧
      BadNuisance (exchange A B) ((2-mu)*(exchange A B:ℝ)/2) (mu-eta) ∧
      (∑ e ∈ E,w e*information A A j mu (mu-eta) e) < target := by
  have hc : 0 ≤ curvature A j E w :=
    sum_nonneg (fun e he => mul_nonneg (hw e he) (sq_nonneg _))
  let eta := min (mu/2) (Real.sqrt (target/(curvature A j E w+1)))
  have hden : 0 < curvature A j E w+1 := by linarith
  have hrad : 0 < target/(curvature A j E w+1) := div_pos htarget hden
  have hsqrt : 0 < Real.sqrt (target/(curvature A j E w+1)) :=
    Real.sqrt_pos.2 hrad
  have heta : 0 < eta := lt_min (by linarith) hsqrt
  have heta_mu : eta ≤ mu := (min_le_left _ _).trans (by linarith)
  refine ⟨eta,heta,heta_mu,boundary_same_label_bad _ hd mu eta hmu1 heta heta_mu,?_⟩
  rw [same_label_path_sum A j hj q mu eta E w hl]
  have heta_sqrt := min_le_right (mu/2) (Real.sqrt (target/(curvature A j E w+1)))
  have hsquare : eta^2 ≤ target/(curvature A j E w+1) := by
    nlinarith [Real.sq_sqrt hrad.le]
  have hratio : target/(curvature A j E w+1) * curvature A j E w < target := by
    rw [div_mul_eq_mul_div]
    exact (div_lt_iff₀ hden).2 (by nlinarith)
  nlinarith [mul_le_mul_of_nonneg_right hsquare hc]

#print axioms boundary_same_label_bad
#print axioms same_label_path_information
#print axioms same_label_path_sum
#print axioms boundary_arbitrarily_small

end
end CIGAMF.P13.D6CenterAnswerGeometry
