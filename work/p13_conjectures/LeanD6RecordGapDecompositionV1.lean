import «LeanD6ProfileStoppingGeometryV1»

/-! Exact record likelihood gap and its grouping by the queries actually used.
These are pathwise identities; no independence of adaptive observations is used. -/
namespace CIGAMF.P13.D6RecordGapDecomposition
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6AllocationDualBridge
open CIGAMF.P13.D6GaussianQueryDominance CIGAMF.P13.D6ProfileStoppingGeometry
noncomputable section
variable {n : ℕ} {T : Type*}

def residual (A : Finset (I n)) (j : I n) (mu : ℝ)
    (e : T → Measurement n) (y : T → ℝ) (t : T) := y t-actualMean A j mu (e t)

def difference (A B : Finset (I n)) (j : I n) (mu nu : ℝ) (u : Measurement n) :=
  actualMean A j mu u-actualMean B j nu u

theorem actual_record_gap (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (A B : Finset (I n)) (j : I n) (mu nu : ℝ) :
    score F e y A j mu-score F e y B j nu =
      ∑ t ∈ F,((difference A B j mu nu (e t))^2/2+
        difference A B j mu nu (e t)*residual A j mu e y t) := by
  unfold score difference residual
  rw [← sum_div, ← sum_div, ← sum_sub_distrib]
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro t ht
  ring

theorem actual_grouped_gap (F : Finset T) (e : T → Measurement n) (y : T → ℝ)
    (A B : Finset (I n)) (j : I n) (mu nu : ℝ)
    (E : Finset (Measurement n)) (hE : ∀ t ∈ F,e t ∈ E) :
    score F e y A j mu-score F e y B j nu =
      ∑ u ∈ E,(((F.filter (fun t => e t=u)).card : ℝ)*
        (difference A B j mu nu u)^2/2 + difference A B j mu nu u*
          ∑ t ∈ F.filter (fun t => e t=u),residual A j mu e y t) := by
  classical
  rw [actual_record_gap, ← sum_fiberwise_of_maps_to hE]
  apply sum_congr rfl
  intro u hu
  have he : (∑ t ∈ F.filter (fun t => e t=u),
      ((difference A B j mu nu (e t))^2/2+
        difference A B j mu nu (e t)*residual A j mu e y t)) =
      ∑ t ∈ F.filter (fun t => e t=u),
      ((difference A B j mu nu u)^2/2+
        difference A B j mu nu u*residual A j mu e y t) := by
    apply sum_congr rfl
    intro t ht
    rw [(mem_filter.mp ht).2]
  rw [he, sum_add_distrib, ← mul_sum]
  simp only [sum_const, nsmul_eq_mul]
  ring

/-- A query-wise residual bound controls every alternative simultaneously. -/
theorem noise_lower (c d s b eta : ℝ) (hc : 0 < c) (heta : 0 < eta)
    (hs : s^2 ≤ 2*c*b) : -eta*c*d^2/2-b/eta ≤ d*s := by
  have hsq := sq_nonneg (eta*c*d+s)
  have hpos : 0 < 2*eta*c := by positivity
  apply (mul_le_mul_iff_left₀ hpos).mp
  field_simp
  nlinarith [mul_pos hc heta]

#print axioms actual_record_gap
#print axioms actual_grouped_gap
#print axioms noise_lower
end
end CIGAMF.P13.D6RecordGapDecomposition
