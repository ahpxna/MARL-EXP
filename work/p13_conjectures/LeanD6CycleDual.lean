import Mathlib
import «LeanD6ResidualCentering»

/-!
# D6 projection-cycle / additive-annihilator primitives

The four-atom cycle is represented by its action on a world.  This is the
orientation already used by P12 `mixedDifference`, so no theorem assumption or
sign convention is changed.
-/

namespace CIGAMF.P13.D6CycleDual

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ResidualCentering

variable {U : Type*} [Fintype U] [Nonempty U]

def cycleFunctional {n : ℕ}
    (i : Fin (n + 1))
    (x c : Fin (n + 1) → U)
    (F : (Fin (n + 1) → U) → ℝ) : ℝ :=
  F x - F (Function.update x i (c i)) -
    F (Function.update c i (x i)) + F c

/- The signed mass of the four-atom cycle after projection to coordinate `k`
and action `u`.  Writing this object explicitly makes the zero-marginal
claim literal rather than only implicit through additive annihilation. -/
def cycleMarginalMass [DecidableEq U] {n : ℕ}
    (i k : Fin (n + 1)) (x c : Fin (n + 1) → U) (u : U) : ℝ :=
  (if x k = u then 1 else 0) -
    (if (Function.update x i (c i)) k = u then 1 else 0) -
    (if (Function.update c i (x i)) k = u then 1 else 0) +
    (if c k = u then 1 else 0)

theorem cycle_zero_marginal_every_coordinate [DecidableEq U] {n : ℕ}
    (i k : Fin (n + 1)) (x c : Fin (n + 1) → U) (u : U) :
    cycleMarginalMass i k x c u = 0 := by
  by_cases hki : k = i
  · subst k
    simp [cycleMarginalMass, Function.update]
  · simp [cycleMarginalMass, Function.update, hki]

theorem cycleFunctional_eq_mixedDifference {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    cycleFunctional i x c F = mixedDifference F i x c := by
  rfl

theorem cycle_annihilates_coordinate_additive {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (c0 : ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    cycleFunctional i x c (fun a ↦ (∑ j, g j (a j)) + c0) = 0 := by
  rw [cycleFunctional_eq_mixedDifference]
  exact mixedDifference_sum_coordinates_zero g c0 i x c

theorem cycle_annihilates_productA {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    cycleFunctional i x c (productA q F) = 0 := by
  rw [cycleFunctional_eq_mixedDifference]
  exact productA_mixedDifference_zero q F i x c

theorem cycle_residual_eq_cycle_world {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    cycleFunctional i x c (productResidual q F) =
      cycleFunctional i x c F := by
  simp only [cycleFunctional_eq_mixedDifference]
  exact R2_mixedDifference_residual q F i x c

theorem finite_cycle_combination_bound
    {R : Type*} [Fintype R]
    {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (delta : ℝ)
    (i : R → Fin (n + 1))
    (x c : R → Fin (n + 1) → U)
    (alpha : R → ℝ)
    (hdelta : ∀ r, |mixedDifference F (i r) (x r) (c r)| ≤ delta) :
    |∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F| ≤
      delta * ∑ r, |alpha r| := by
  calc
    |∑ r, alpha r * cycleFunctional (i r) (x r) (c r) F| ≤
        ∑ r, |alpha r * cycleFunctional (i r) (x r) (c r) F| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r, |alpha r| *
        |mixedDifference F (i r) (x r) (c r)| := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [abs_mul, cycleFunctional_eq_mixedDifference]
    _ ≤ ∑ r, |alpha r| * delta := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hdelta r) (abs_nonneg (alpha r))
    _ = delta * ∑ r, |alpha r| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

end CIGAMF.P13.D6CycleDual
