import «LeanD6BlindLinearVarianceV1»
import «LeanD6CyclicPhaseLawV1»

/-! The algebraic lower bound is a variance bound on actual independent Gaussian
query observations. Its scope is fixed linear A-invariant off-query statistics. -/
namespace CIGAMF.P13.D6BlindLinearOptimality
open scoped BigOperators
open Finset MeasureTheory ProbabilityTheory
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6GaussianQueryDominance
open CIGAMF.P13.D6BlindLinearVariance
noncomputable section
variable {T : Type*} [Fintype T] [DecidableEq T]

def estimator (w : T → ℝ) (a : ℝ) (x : T → ℝ) : ℝ :=
  ((∑ t,w t)+a-∑ t,w t*x t)/a

theorem weighted_variance (means w : T → ℝ) :
    variance (fun x : T → ℝ => ∑ t,w t*x t) (FiniteGaussianSumLaw.law means) =
      ∑ t,(w t)^2 := by
  have h := variance_sum_pi (μ := fun t => gaussianReal (means t) 1)
    (X := fun t x => w t*x)
    (fun t => (memLp_id_gaussianReal (μ:=means t) (v:=1) 2).const_mul (w t))
  have he : (∑ t,(fun x : T → ℝ => w t*x t)) = (fun x => ∑ t,w t*x t) := by
    funext x; simp only [Finset.sum_apply]
  rw [he] at h
  have ht (t : T) : variance (fun x : ℝ => w t*x) (gaussianReal (means t) 1) = (w t)^2 := by
    change variance (fun x : ℝ => w t*id x) (gaussianReal (means t) 1) = _
    rw [variance_const_mul,variance_id_gaussianReal]
    simp
  simp_rw [ht] at h
  exact h

theorem estimator_variance (means w : T → ℝ) (a : ℝ) :
    variance (estimator w a) (FiniteGaussianSumLaw.law means) = (∑ t,(w t)^2)/a^2 := by
  have he : estimator w a =
      (fun x : T → ℝ => a⁻¹*((∑ t,w t)+a-∑ t,w t*x t)) := by
    funext x; unfold estimator; ring
  rw [he,variance_const_mul,variance_const_sub ((show Measurable (fun x : T → ℝ => ∑ t,w t*x t) by fun_prop).aestronglyMeasurable),weighted_variance]
  ring

/-- Lower bound for actual world/query means. The invariant coefficient premise
is precisely the definition of the comparison class, not a probability-law premise. -/
theorem actual_variance_lower {n : ℕ} (U : Finset (I n)) (q : ℕ) (hq : 2 ≤ q)
    (hqU : q ≤ U.card) (G : T → Finset (I n)) (w : T → ℝ)
    (hG : ∀ t,G t ⊆ U) (hsize : ∀ t,(G t).card ≤ q)
    (a : ℝ) (ha0 : a ≠ 0)
    (ha : ∀ B ∈ U.powersetCard q,coefficient G w B=a)
    (A : Finset (I n)) (j : I n) (mu : ℝ) :
    (U.card:ℝ)^2 ≤ (q:ℝ)^4*Fintype.card T*
      variance (estimator w a)
        (FiniteGaussianSumLaw.law (fun t => actualMean A j mu (.inr (G t,false)))) := by
  rw [estimator_variance]
  exact invariant_variance_lower U q hq hqU G w hG hsize a ha0 ha

#print axioms weighted_variance
#print axioms estimator_variance
#print axioms actual_variance_lower
end
end CIGAMF.P13.D6BlindLinearOptimality
