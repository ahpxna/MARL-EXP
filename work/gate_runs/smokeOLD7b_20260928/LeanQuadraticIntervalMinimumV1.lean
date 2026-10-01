import Mathlib

/-! Exact finite arithmetic for the nuisance minimization over [0,1].
The zero-curvature branch is linear and is handled explicitly. -/
namespace CIGAMF.P13.QuadraticIntervalMinimum
noncomputable section

def value (C Z V x : ℝ) : ℝ := (C-2*Z*x+V*x^2)/2

def minimizer (Z V : ℝ) : ℝ :=
  if V=0 then (if 0 ≤ Z then 1 else 0) else max 0 (min 1 (Z/V))

lemma minimizer_mem (Z V : ℝ) : 0 ≤ minimizer Z V ∧ minimizer Z V ≤ 1 := by
  unfold minimizer
  split_ifs <;> try norm_num

lemma difference (C Z V x y : ℝ) :
    value C Z V y-value C Z V x=(V*(y-x)^2+2*(V*x-Z)*(y-x))/2 := by
  unfold value
  ring

/-- The constrained minimizer is valid even when the unconstrained estimate
lies outside [0,1], or the curvature vanishes. -/
theorem minimum (C Z V : ℝ) (hV : 0 ≤ V) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    value C Z V (minimizer Z V) ≤ value C Z V y := by
  apply sub_nonneg.mp
  rw [difference]
  have hsq : 0 ≤ V*(y-minimizer Z V)^2 := mul_nonneg hV (sq_nonneg _)
  suffices 0 ≤ (V*minimizer Z V-Z)*(y-minimizer Z V) by nlinarith
  by_cases h0 : V=0
  · unfold minimizer
    rw [if_pos h0]
    split_ifs with hZ
    · simp only [h0,zero_mul,zero_sub]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · simp only [h0,mul_zero,zero_sub,sub_zero]
      exact mul_nonneg (by linarith) hy0
  have hVp : 0 < V := lt_of_le_of_ne hV (Ne.symm h0)
  by_cases hz0 : Z ≤ 0
  · have hx : minimizer Z V=0 := by
      unfold minimizer
      rw [if_neg h0,max_eq_left ((min_le_right _ _).trans (div_nonpos_of_nonpos_of_nonneg hz0 hV))]
    rw [hx]
    simp only [mul_zero,zero_sub,sub_zero]
    exact mul_nonneg (by linarith) hy0
  by_cases hz1 : V ≤ Z
  · have hx : minimizer Z V=1 := by
      unfold minimizer
      rw [if_neg h0,min_eq_left ((le_div_iff₀ hVp).mpr (by linarith)),max_eq_right (by norm_num)]
    rw [hx,mul_one]
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · have hx : minimizer Z V=Z/V := by
      unfold minimizer
      rw [if_neg h0,min_eq_right ((div_le_one hVp).mpr (by linarith)),
        max_eq_right (div_nonneg (by linarith) hV)]
    rw [hx,mul_div_cancel₀ _ h0,sub_self,zero_mul]

#print axioms minimizer_mem
#print axioms minimum
end
end CIGAMF.P13.QuadraticIntervalMinimum
