import Mathlib
example (a b : ℝ) (hb : 0 < b) (h2 : 2 * b < a) (h7 : 3 * a ≤ 7 * b) (h5b : 5 * b - a ≠ 0) :
    2 * b * (3 * b - a) / (5 * b - a) = (4 * b - a) / 3 - (a - b) / 6 * (2 * (a - 2 * b) / (5 * b - a)) := by
  field_simp [h5b]
  ring
example (a b : ℝ) (hb : 0 < b) (h2 : 2 * b < a) (h7 : 3 * a ≤ 7 * b) (h5b : 5 * b - a ≠ 0) :
    2 * b * (3 * b - a) / (5 * b - a) = (4 * b - a) / 3 - (a - b) / 6 * (2 * (a - 2 * b) / (5 * b - a)) := by
  rw [div_mul_div_comm, div_sub_div _ _ (by norm_num) (mul_ne_zero (by norm_num) h5b),
    div_eq_div_iff h5b (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num) h5b))]
  ring
example (a b : ℝ) (hb : 0 < b) (h2 : 2 * b < a) (h7 : 3 * a ≤ 7 * b) (h5b : 5 * b - a ≠ 0) :
    2 * b * (3 * b - a) / (5 * b - a) = (4 * b - a) / 3 - (a - b) / 6 * (2 * (a - 2 * b) / (5 * b - a)) := by
  have e : (5 * b - a) * (5 * b - a)⁻¹ = 1 := mul_inv_cancel₀ h5b
  simp only [div_eq_mul_inv]
  linear_combination (e := e) (0:ℝ)
