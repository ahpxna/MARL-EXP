import Mathlib

/-! Weighted Gaussian mean separation after profiling a real calibration offset.
No likelihood process or stopping theorem is assumed. -/
namespace CIGAMF.P13.MasterUnknownCalibration
open scoped BigOperators
noncomputable section
variable {E : Type*} [Fintype E]

def energy (a d v : E → ℝ) (u : ℝ) : ℝ :=
  (∑ e, a e * (d e - u * v e)^2) / 2

def curvature (a v : E → ℝ) : ℝ := ∑ e, a e * (v e)^2
def cross (a d v : E → ℝ) : ℝ := ∑ e, a e * d e * v e
def raw (a d : E → ℝ) : ℝ := ∑ e, a e * (d e)^2

theorem energy_expand (a d v : E → ℝ) (u : ℝ) :
    energy a d v u = (raw a d - 2*u*cross a d v + u^2*curvature a v)/2 := by
  unfold energy raw cross curvature
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem profile_square (a d v : E → ℝ) (h : curvature a v ≠ 0) (u : ℝ) :
    energy a d v u = (raw a d - (cross a d v)^2 / curvature a v)/2 +
      curvature a v / 2 * (u - cross a d v / curvature a v)^2 := by
  rw [energy_expand]
  field_simp
  <;> ring

theorem profile_minimum (a d v : E → ℝ) (h : 0 < curvature a v) :
    (∀ u, (raw a d - (cross a d v)^2/curvature a v)/2 ≤ energy a d v u) ∧
    energy a d v (cross a d v/curvature a v) =
      (raw a d - (cross a d v)^2/curvature a v)/2 := by
  constructor
  · intro u
    rw [profile_square a d v (ne_of_gt h)]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
  · rw [profile_square a d v (ne_of_gt h)]
    simp

theorem zero_curvature (a d v : E → ℝ) (ha : ∀ e, 0 ≤ a e)
    (h : curvature a v = 0) (u : ℝ) : energy a d v u = raw a d/2 := by
  have he : ∀ e, a e * (v e)^2 = 0 := by
    intro e
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => mul_nonneg (ha i) (sq_nonneg (v i)))).mp h
    exact hh e (Finset.mem_univ e)
  have hc : cross a d v = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    rcases mul_eq_zero.mp (he e) with h0 | h0
    · simp [h0]
    · have hv : v e = 0 := sq_eq_zero_iff.mp h0
      simp [hv]
  rw [energy_expand, hc, h]
  ring

theorem single_channel (a d : ℝ) : a * (d-d*1)^2/2 = 0 := by ring

theorem balanced_no_penalty (a d v : E → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hc : cross a d v = 0) :
    (∀ u, raw a d/2 ≤ energy a d v u) ∧ energy a d v 0 = raw a d/2 := by
  have hv : 0 ≤ curvature a v := Finset.sum_nonneg (fun e _ => mul_nonneg (ha e) (sq_nonneg _))
  constructor
  · intro u
    rw [energy_expand, hc]
    nlinarith [mul_nonneg (sq_nonneg u) hv]
  · rw [energy_expand]; ring

theorem opposite_channels (g u : ℝ) :
    ((g-u)^2/2 + (-g-u)^2/2)/2 = g^2/2 + u^2/2 := by ring

theorem control_channels (a b g u : ℝ) (h : a+b ≠ 0) :
    (a*u^2+b*(g-u)^2)/2 = a*b*g^2/(2*(a+b)) +
      (a+b)/2*(u-b*g/(a+b))^2 := by
  field_simp
  <;> ring

theorem cost_cauchy_identity (s t r v x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (s^2/x+t^2/y)*(r^2*x+v^2*y)-(s*r+t*v)^2 =
      (s*v*y-t*r*x)^2/(x*y) := by
  field_simp
  <;> ring

theorem cost_variance_lower (s t r v x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hb : r^2*x+v^2*y=1) : (s*r+t*v)^2 ≤ s^2/x+t^2/y := by
  have hi := cost_cauchy_identity s t r v x y (ne_of_gt hx) (ne_of_gt hy)
  rw [hb, mul_one] at hi
  have hn : 0 ≤ (s*v*y-t*r*x)^2/(x*y) := by positivity
  linarith

theorem optimal_cost_allocation (s t r v : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hr : 0 < r) (hv : 0 < v) :
    let x := (s/r)/(s*r+t*v)
    let y := (t/v)/(s*r+t*v)
    0 < x ∧ 0 < y ∧ r^2*x+v^2*y=1 ∧
      s^2/x+t^2/y=(s*r+t*v)^2 := by
  dsimp
  have hd : s*r+t*v ≠ 0 := ne_of_gt (by positivity)
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · field_simp; <;> ring
  · field_simp; <;> ring

#print axioms profile_square
#print axioms profile_minimum
#print axioms zero_curvature
#print axioms single_channel
#print axioms balanced_no_penalty
#print axioms opposite_channels
#print axioms control_channels
#print axioms cost_variance_lower
#print axioms optimal_cost_allocation
end
end CIGAMF.P13.MasterUnknownCalibration
