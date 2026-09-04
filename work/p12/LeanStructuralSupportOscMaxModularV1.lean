import Mathlib
import «LeanSupportGeometryV4»

/-!
# Support oscillation as a finite maximum of modular scenarios

This is an algorithmic bridge, not a novelty claim: an actual support-aware
compression radius is the maximum, over two feasible support worlds, of a
modular set function.
-/

namespace CIGAMF.P13.StructuralSupportOscMaxModular

open scoped BigOperators
open CIGAMF.V4.SupportGeometry

variable {Ω I : Type*} [Fintype Ω] [Nonempty Ω]
  [Fintype I] [DecidableEq I]

def directedSupportContrast (T : Finset I) (f : I → Ω → ℝ)
    (ab : Ω × Ω) : ℝ :=
  T.sum fun j ↦ f j ab.1 - f j ab.2

theorem directedSupportContrast_eq_sumComponent_sub
    (T : Finset I) (f : I → Ω → ℝ) (a b : Ω) :
    directedSupportContrast T f (a, b) =
      sumComponent T f a - sumComponent T f b := by
  simp [directedSupportContrast, sumComponent, Finset.sum_sub_distrib]

/-- Exact finite identity: oscillation equals the largest directed pairwise
contrast on the feasible support. -/
theorem supportOsc_eq_max_directed_contrast
    (T : Finset I) (f : I → Ω → ℝ) :
    supportOsc T f = maxVal (directedSupportContrast T f) := by
  apply le_antisymm
  · rcases exists_eq_maxVal (sumComponent T f) with ⟨a, ha⟩
    rcases exists_eq_minVal (sumComponent T f) with ⟨b, hb⟩
    rw [supportOsc, osc, ← ha, ← hb,
      ← directedSupportContrast_eq_sumComponent_sub T f a b]
    exact le_maxVal (directedSupportContrast T f) (a, b)
  · apply maxVal_le
    rintro ⟨a, b⟩
    rw [directedSupportContrast_eq_sumComponent_sub]
    unfold supportOsc osc
    linarith [le_maxVal (sumComponent T f) a,
      minVal_le (sumComponent T f) b]

/-- Literal form requested for the CIG-AMF selected radius. -/
theorem two_selectedRadius_eq_max_pair_contrast
    (f : I → Ω → ℝ) (selected : Finset I) :
    2 * selectedRadius f selected =
      maxVal (directedSupportContrast selectedᶜ f) := by
  rw [selectedRadius, supportOsc_eq_max_directed_contrast]
  ring

/-- Scenario constant for the maximum-of-modular representation. -/
def scenarioConstant (f : I → Ω → ℝ) (ab : Ω × Ω) : ℝ :=
  ∑ j, (f j ab.1 - f j ab.2)

/-- Scenario coefficient removed when relation `j` is selected. -/
def scenarioCoefficient (f : I → Ω → ℝ) (ab : Ω × Ω) (j : I) : ℝ :=
  f j ab.1 - f j ab.2

theorem complement_contrast_eq_scenario_modular
    (f : I → Ω → ℝ) (selected : Finset I) (ab : Ω × Ω) :
    directedSupportContrast selectedᶜ f ab =
      scenarioConstant f ab - selected.sum (scenarioCoefficient f ab) := by
  classical
  let g : I → ℝ := fun j ↦ f j ab.1 - f j ab.2
  have hsum := Finset.sum_add_sum_compl selected g
  change selectedᶜ.sum g = (∑ j, g j) - selected.sum g
  linarith

/-- Actual `supportOsc` is a finite maximum of modular scenario objectives. -/
theorem two_selectedRadius_eq_max_modular_scenarios
    (f : I → Ω → ℝ) (selected : Finset I) :
    2 * selectedRadius f selected =
      maxVal (fun ab : Ω × Ω ↦
        scenarioConstant f ab - selected.sum (scenarioCoefficient f ab)) := by
  rw [two_selectedRadius_eq_max_pair_contrast]
  apply le_antisymm <;> apply maxVal_le <;> rintro ⟨a, b⟩
  · rw [complement_contrast_eq_scenario_modular]
    exact le_maxVal (fun ab : Ω × Ω ↦
      scenarioConstant f ab - selected.sum (scenarioCoefficient f ab)) (a, b)
  · rw [← complement_contrast_eq_scenario_modular]
    exact le_maxVal (directedSupportContrast selectedᶜ f) (a, b)

end CIGAMF.P13.StructuralSupportOscMaxModular
