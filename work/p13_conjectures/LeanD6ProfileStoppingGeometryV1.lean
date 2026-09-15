import «LeanD6GaussianQueryDominanceV1»
import «LeanD6UniqueOptimumV1»

/-! Exact profile algebra from actual query means and the pathwise implication
from a likelihood certificate to the literal geometric answer. The probability
of the uniform likelihood event is a separate obligation. -/
namespace CIGAMF.P13.D6ProfileStoppingGeometry
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6UniqueOptimum
open CIGAMF.P13.D6Geometry
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ} {T : Type*}

def score (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (A : Finset (I n)) (j : I n) (mu : ℝ) : ℝ :=
  -(∑ t ∈ F,(y t-actualMean A j mu (e t))^2)/2

def C (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (A : Finset (I n)) (j : I n) : ℝ := ∑ t ∈ F,(y t-meanOffset A j (e t))^2

def Z (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (A : Finset (I n)) (j : I n) : ℝ :=
  ∑ t ∈ F,meanSlope A j (e t)*(y t-meanOffset A j (e t))

def V (F : Finset T) (e : T → Measurement n) (A : Finset (I n)) (j : I n) : ℝ :=
  ∑ t ∈ F,(meanSlope A j (e t))^2

def quadraticScore (c z v mu : ℝ) := -(c-2*mu*z+mu^2*v)/2

def mixtureExpression (c z v : ℝ) := -c/2-Real.log (1+v)/2+z^2/(2*(1+v))
def profilePenalty (z v : ℝ) := Real.log (1+v)/2+z^2/(2*v*(1+v))

theorem actual_score_quadratic (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (A : Finset (I n)) (j : I n) (mu q : ℝ) (hj : j ∉ A)
    (hl : ∀ t ∈ F,Legal j q (e t)) :
    score F e y A j mu=quadraticScore (C F e y A j) (Z F e y A j) (V F e A j) mu := by
  have he : (∑ t ∈ F,(y t-actualMean A j mu (e t))^2) =
      C F e y A j-2*mu*Z F e y A j+mu^2*V F e A j := by
    unfold C Z V
    simp_rw [mul_sum,← sum_sub_distrib,← sum_add_distrib]
    apply sum_congr rfl; intro t ht
    rw [actual_mean_affine A j hj q mu (e t) (hl t ht)]
    ring
  unfold score quadraticScore
  rw [he]

theorem profile_mixture_identity (c z v mu : ℝ) (hv : 0 < v) :
    mixtureExpression c z v+profilePenalty z v-quadraticScore c z v mu =
      v*(mu-z/v)^2/2 := by
  have hv' : 1+v ≠ 0 := by linarith
  unfold mixtureExpression profilePenalty quadraticScore
  field_simp [ne_of_gt hv,hv']
  <;> ring

theorem actual_profile_majorant (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (A : Finset (I n)) (j : I n) (mu q : ℝ) (hj : j ∉ A)
    (hl : ∀ t ∈ F,Legal j q (e t)) (hv : 0 < V F e A j) :
    score F e y A j mu ≤ mixtureExpression (C F e y A j) (Z F e y A j) (V F e A j)+
      profilePenalty (Z F e y A j) (V F e A j) := by
  rw [actual_score_quadratic F e y A j mu q hj hl]
  have he := profile_mixture_identity (C F e y A j) (Z F e y A j) (V F e A j) mu hv
  have hp := mul_nonneg hv.le (sq_nonneg (mu-Z F e y A j/V F e A j))
  linarith

/-- The displayed uniform likelihood event makes a profile-gap stop correct.
This is pathwise and does not assume an unproved probability bound. -/
theorem certificate_identifies_label (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (W : Finset (Finset (I n))) (A Ahat : Finset (I n)) (j : I n)
    (mu muhat q threshold : ℝ) (hA : A ∈ W) (hhat : Ahat ∈ W)
    (hjhat : j ∉ Ahat) (hl : ∀ t ∈ F,Legal j q (e t))
    (hv : 0 < V F e Ahat j) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (good : ∀ B ∈ W,mixtureExpression (C F e y B j) (Z F e y B j) (V F e B j)-
      score F e y A j mu < threshold)
    (stop : ∀ B ∈ W,B ≠ Ahat → ∀ nu : ℝ,0 ≤ nu → nu ≤ 1 →
      threshold+profilePenalty (Z F e y Ahat j) (V F e Ahat j) ≤
        score F e y Ahat j muhat-score F e y B j nu) : Ahat=A := by
  by_contra hne
  have hs := stop A hA (Ne.symm hne) mu hmu hmu1
  have hg := good Ahat hhat
  have hm := actual_profile_majorant F e y Ahat j muhat q hjhat hl hv
  linarith

/-- Certified output is optimal on the actual finite real support, with fixed
ambient projections and the original cardinality constraint. -/
theorem certificate_geometric_optimal (r : ℕ) (j : I (2*r+1)) (hr : 2 ≤ r)
    (F : Finset T) (e : T → Measurement (2*r+1)) (y : T → ℝ)
    (A Ahat : Finset (I (2*r+1))) (hA : A ∈ worlds r j) (hhat : Ahat ∈ worlds r j)
    (mu muhat threshold : ℝ) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (hl : ∀ t ∈ F,Legal j r (e t)) (hv : 0 < V F e Ahat j)
    (good : ∀ B ∈ worlds r j,
      mixtureExpression (C F e y B j) (Z F e y B j) (V F e B j)-score F e y A j mu < threshold)
    (stop : ∀ B ∈ worlds r j,B ≠ Ahat → ∀ nu : ℝ,0 ≤ nu → nu ≤ 1 →
      threshold+profilePenalty (Z F e y Ahat j) (V F e Ahat j) ≤
        score F e y Ahat j muhat-score F e y B j nu) :
    ∀ S : Finset (I (2*r+1)),S.card=A.card →
      selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
        (liftedSelection Ahatᶜ) ≤
      selectedRadius (restrictedProjection (world A j mu) (productResponse corner (world A j mu)))
        (liftedSelection S) := by
  have hp := world_parameters r j hr hA
  have hh := world_parameters r j hr hhat
  have he := certificate_identifies_label F e y (worlds r j) A Ahat j mu muhat r threshold
    hA hhat hh.1 hl hv hmu hmu1 good stop
  rw [he]
  exact (geometric_optimal_iff A Aᶜ j hp.1 mu hmu hmu1 hp.2.2.1 hp.2.2.1 hp.2.2.2).mpr rfl

#print axioms actual_score_quadratic
#print axioms profile_mixture_identity
#print axioms actual_profile_majorant
#print axioms certificate_identifies_label
#print axioms certificate_geometric_optimal
end
end CIGAMF.P13.D6ProfileStoppingGeometry
