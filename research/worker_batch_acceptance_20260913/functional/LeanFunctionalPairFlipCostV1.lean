import Mathlib

/-! Exact two-capacity boundary cost after reducing binary response endpoint
energies to slope variances. The reduction from a shared physical F is NOT
assumed here; this is the unrestricted two-score calculation, not a novelty
claim or a shared-response-model theorem. -/
namespace CIGAMF.P13.FunctionalPairFlipCost
noncomputable section

def energy (v w x y : ℝ) : ℝ := x^2/(2*v)+y^2/(2*w)

theorem energy_decomposition (v w x y : ℝ) (hv : 0 < v) (hw : 0 < w) :
    energy v w x y=(x+y)^2/(2*(v+w))+(w*x-v*y)^2/(2*v*w*(v+w)) := by
  have hsum : v+w ≠ 0 := by linarith
  unfold energy
  field_simp
  <;> ring

theorem pair_flip_lower (v w gap x y : ℝ) (hv : 0 < v) (hw : 0 < w)
    (hg : 0 ≤ gap) (hcross : gap ≤ x+y) :
    gap^2/(2*(v+w)) ≤ energy v w x y := by
  rw [energy_decomposition v w x y hv hw]
  have hden : 0 < 2*(v+w) := by positivity
  have hsq : gap^2 ≤ (x+y)^2 := by nlinarith
  have hfirst := div_le_div_of_nonneg_right hsq hden.le
  have hsecond : 0 ≤ (w*x-v*y)^2/(2*v*w*(v+w)) := by positivity
  linarith

/-- An explicit minimizer reaches the tie. Strict reversal has the same
infimum, but need not attain it; that distinction is not hidden in the name. -/
theorem pair_flip_attained (v w gap : ℝ) (hv : 0 < v) (hw : 0 < w) :
    gap*v/(v+w)+gap*w/(v+w)=gap ∧
      energy v w (gap*v/(v+w)) (gap*w/(v+w))=gap^2/(2*(v+w)) := by
  have hsum : v+w ≠ 0 := by linarith
  constructor
  · field_simp <;> ring
  · unfold energy; field_simp <;> ring

#print axioms pair_flip_lower
#print axioms pair_flip_attained
end
end CIGAMF.P13.FunctionalPairFlipCost
