import «LeanMasterUnknownCalibrationV1»

/-!
# Exact active-face criterion for an unknown common calibration offset

This module isolates the logical step needed after completing the square.  It
does not assume that every alternative is active: a non-active alternative may
carry a nonzero weighted mean difference when its known-offset slack absorbs
the profiling penalty.
-/
namespace CIGAMF.P13.D6CalibrationActiveFace

open CIGAMF.P13.MasterUnknownCalibration
noncomputable section

variable {Alt : Type*}

def profiled (D M : Alt → ℝ) (a : Alt) : ℝ := D a - (M a)^2 / 2
def slack (D : Alt → ℝ) (Gamma : ℝ) (a : Alt) : ℝ := D a - Gamma

/-- A fixed design whose known-offset information is at least `Gamma` keeps
that guarantee after profiling iff every alternative's squared cross term fits
inside twice its slack. -/
theorem profiled_ge_iff (D M : Alt → ℝ) (Gamma : ℝ)
    (hknown : ∀ a, Gamma ≤ D a) :
    (∀ a, Gamma ≤ profiled D M a) ↔
      ∀ a, (M a)^2 ≤ 2 * slack D Gamma a := by
  constructor <;> intro h a
  · have := h a
    unfold profiled slack at *
    linarith
  · have := h a
    unfold profiled slack at *
    linarith

/-- On an active known-offset alternative, retaining the same value is
equivalent to exact cancellation of the calibration cross term. -/
theorem active_iff_cross_zero (D M : Alt → ℝ) (Gamma : ℝ) (a : Alt)
    (hactive : D a = Gamma) :
    Gamma ≤ profiled D M a ↔ M a = 0 := by
  unfold profiled
  rw [hactive]
  constructor
  · intro h
    have hs : (M a)^2 ≤ 0 := by linarith
    exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
  · intro hzero
    rw [hzero]
    norm_num

/-- If even one active alternative has nonzero cross term, profiling strictly
reduces that design's worst-alternative value below `Gamma`. -/
theorem active_nonzero_forces_loss (D M : Alt → ℝ) (Gamma : ℝ) (a : Alt)
    (hactive : D a = Gamma) (hcross : M a ≠ 0) :
    profiled D M a < Gamma := by
  unfold profiled
  rw [hactive]
  have hs : 0 < (M a)^2 := sq_pos_of_ne_zero hcross
  linarith

/-- The abstract formula is the unit-curvature specialization of the actual
Gaussian-offset profile theorem. -/
theorem profile_formula_unit {E : Type*} [Fintype E]
    (w d : E → ℝ) (hcurv : curvature w (fun _ => 1) = 1) :
    energy w d (fun _ => 1) (cross w d (fun _ => 1)) =
      raw w d / 2 - (cross w d (fun _ => 1))^2 / 2 := by
  have h := (profile_minimum w d (fun _ => 1) (by linarith)).2
  rw [hcurv] at h
  rw [div_one] at h
  convert h using 1 <;> ring

#print axioms profiled_ge_iff
#print axioms active_iff_cross_zero
#print axioms active_nonzero_forces_loss
#print axioms profile_formula_unit

end
end CIGAMF.P13.D6CalibrationActiveFace
