import Mathlib
theorem zz (x : ℝ) (hx : 0 < x) : 0 ≤ 1/x + Real.log x - 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/x by positivity)
  rw [one_div, Real.log_inv] at h
  have : (1:ℝ)/x = x⁻¹ := one_div x
  rw [this]; linarith
#print axioms zz
