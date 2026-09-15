import «LeanD6ThresholdConstructionV1»

/-! Unknown-margin allocation: actual-world confounding and analytic parts of
an exact m=10 certificate. The full orbit-averaging/optimal-design bridge is
NOT claimed as formalized here. The separate exact-rational verifier checks
all 265 measurements and 125 alternatives, minimizing each real quadratic. -/
namespace CIGAMF.P13.D6UnknownMargin
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold
open CIGAMF.V4.ProductMixedDifference

def A : Finset (I 9) := {0,1,2,3,4}
def A' : Finset (I 9) := {0,1,2,3,6}
def B : Finset (I 9) := {6,7,8,9}
def j : I 9 := 5

theorem j_not_A : j ∉ A := by decide
theorem j_not_A' : j ∉ A' := by decide

/-- Same actual joint observation, different hidden set AND margin. Repeating
this sole measurement cannot distinguish the two worlds under identical noise. -/
theorem actual_joint_confounding :
    world A j (1/2) (jointCorner B j) = 3/2 ∧
    world A' j (1/4) (jointCorner B j) = 3/2 := by
  rw [joint_measurement A B j j_not_A, joint_measurement A' B j j_not_A']
  have h : (B ∩ others A j).card = 4 := by decide
  have h' : (B ∩ others A' j).card = 3 := by decide
  rw [h, h']; norm_num

/-- Using the first world's optimum in the second causes strictly positive
actual regret. The error is not an artifact of an abstract answer map. -/
theorem confounded_wrong_optimum_regret :
    productCompressionLoss (world A' j (1/4)) (productResponse corner (world A' j (1/4))) Aᶜ -
      productCompressionLoss (world A' j (1/4)) (productResponse corner (world A' j (1/4))) A'ᶜ =
      7/8 := by
  rw [actual_regret A' Aᶜ j j_not_A' (1/4) (by norm_num) (by norm_num)
    (by decide) (by decide) (by decide)]
  have h : (Aᶜ ∩ A').card = 1 := by decide
  rw [h]; norm_num

theorem both_worlds_have_actual_optima (S : Finset (I 9)) (hS : S.card = 5) :
    productCompressionLoss (world A j (1/2)) (productResponse corner (world A j (1/2))) Aᶜ ≤
      productCompressionLoss (world A j (1/2)) (productResponse corner (world A j (1/2))) S ∧
    productCompressionLoss (world A' j (1/4)) (productResponse corner (world A' j (1/4))) A'ᶜ ≤
      productCompressionLoss (world A' j (1/4)) (productResponse corner (world A' j (1/4))) S := by
  constructor
  · exact complement_optimal A S j j_not_A (1/2) (by norm_num) (by norm_num)
      (hS.trans (by decide)) (by decide) (by decide)
  · exact complement_optimal A' S j j_not_A' (1/4) (by norm_num) (by norm_num)
      (hS.trans (by decide)) (by decide) (by decide)

noncomputable def rate : ℝ := 289/2888

noncomputable def nearestPrimal (nu : ℝ) : ℝ :=
  (170/171) * ((1 + (1/2-nu)^2)/10) + (1/171) * ((3/2-2*nu)^2/2)

/-- Completed square valid for every real alternative lambda, without a grid. -/
theorem primal_completed_square (nu : ℝ) :
    nearestPrimal nu = rate + (nu - 10/19)^2/9 := by
  unfold nearestPrimal rate
  ring

theorem primal_nearest_lower (nu : ℝ) : rate ≤ nearestPrimal nu := by
  rw [primal_completed_square]
  nlinarith [sq_nonneg (nu-10/19)]

theorem primal_attained : nearestPrimal (10/19) = rate := by
  rw [primal_completed_square]; norm_num

/-- For distance >=2, each A-only four-subset has alternative mean >=0,
whereas its true mean is -1/2. This scalar implication is used by the
certificate; the full combinatorial averaging remains in the exact verifier. -/
theorem distant_point_lower (y : ℝ) (hy : 0 ≤ y) :
    (1/8 : ℝ) ≤ (y+1/2)^2/2 := by nlinarith [sq_nonneg y]

theorem distant_primal_above_rate : rate < (170/171 : ℝ)*(1/8) := by
  norm_num [rate]

/-- Uniform adjacent-alternative dual polynomial. s/t are the counts of queried
coordinates in A/B. Its derivation from the 20 alternatives is exact-checked
in Python; this theorem proves its bound for every legal count pair. -/
noncomputable def jointDual (s t : ℕ) : ℝ :=
  ((1/2-10/19)^2*((t:ℝ)-1)^2 -
    2*(1/2-10/19)*(10/19)*((t:ℝ)-1)*((s:ℝ)/5-(t:ℝ)/4) +
    (10/19)^2*((s:ℝ)/5+(t:ℝ)/4-2*(s:ℝ)*(t:ℝ)/20))/2

theorem dual_all_joint_counts (s t : ℕ) (h : s+t ≤ 4) : jointDual s t ≤ rate := by
  have hs : s ≤ 4 := by omega
  have ht : t ≤ 4 := by omega
  interval_cases s <;> interval_cases t <;> norm_num [jointDual, rate] at *

theorem dual_scalar_counts :
    ((1-10/19)^2/10 : ℝ) ≤ rate ∧
    (((1/4)*(1-1/2)^2+(3/4)*(1/2-10/19)^2)/2 : ℝ) ≤ rate ∧
    ((1/2-10/19)^2/2 : ℝ) ≤ rate := by norm_num [rate]

theorem both_allocated_orbits_attain_dual : jointDual 0 4 = rate ∧ jointDual 4 0 = rate := by
  norm_num [jointDual, rate]

#print axioms actual_joint_confounding
#print axioms confounded_wrong_optimum_regret
#print axioms both_worlds_have_actual_optima
#print axioms primal_completed_square
#print axioms primal_nearest_lower
#print axioms dual_all_joint_counts
#print axioms dual_scalar_counts
end CIGAMF.P13.D6UnknownMargin
