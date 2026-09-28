import Mathlib
import «LeanD6CycleDual»

/-!
# Centered local interaction contrast profiles for D6

This module uses the existing product-response semantics verbatim.  A profile
is the local action contrast after subtracting its product-reference
first-order contrast.  It is intentionally a function of a full world state:
the distinguished coordinate is overwritten, so its value depends only on the
complement context extensionally.

No decision bound is claimed here.  The purpose is to identify exactly what
D6 mixed differences measure after first-order centering.
-/

namespace CIGAMF.P13.D6InteractionContrastProfile

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual

variable {U : Type*} [Fintype U] [Nonempty U]

/-- The local contrast for action `u`, centered against anchor action `u0`
and against the same product-response contrast. -/
noncomputable def interactionContrastProfile {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u : U)
    (z : Fin (n + 1) → U) : ℝ :=
  (F (Function.update z i u) - F (Function.update z i u0)) -
    (productResponse q F i u - productResponse q F i u0)

/-- Coordinate-additive worlds are the D6 gauge directions. -/
noncomputable def coordinateAdditiveWorld {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (z : Fin (n + 1) → U) : ℝ :=
  (∑ j, g j (z j)) + b

theorem interactionContrastProfile_anchor {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (z : Fin (n + 1) → U) :
    interactionContrastProfile q F i u0 u0 z = 0 := by
  simp [interactionContrastProfile]

private theorem coordinateAdditiveWorld_update_difference {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (i : Fin (n + 1)) (u v : U)
    (z : Fin (n + 1) → U) :
    coordinateAdditiveWorld g b (Function.update z i u) -
      coordinateAdditiveWorld g b (Function.update z i v) =
      g i u - g i v := by
  classical
  unfold coordinateAdditiveWorld
  have hsum :
      (∑ j : Fin (n + 1), g j ((Function.update z i u) j)) -
        (∑ j : Fin (n + 1), g j ((Function.update z i v) j)) =
          g i u - g i v := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · simp [Function.update]
    · intro j _ hji
      simp [Function.update, hji]
    · simp
  linarith

private theorem productResponse_coordinateAdditive_difference {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (i : Fin (n + 1)) (u v : U) :
    productResponse q (coordinateAdditiveWorld g b) i u -
      productResponse q (coordinateAdditiveWorld g b) i v =
      g i u - g i v := by
  classical
  unfold productResponse productExpectation
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ c : Fin (n + 1) → U,
      jointWeight q c *
          coordinateAdditiveWorld g b (Function.update c i u) -
        jointWeight q c *
          coordinateAdditiveWorld g b (Function.update c i v) =
        jointWeight q c * (g i u - g i v) := by
    intro c
    rw [← mul_sub]
    rw [coordinateAdditiveWorld_update_difference]
  simp_rw [hterm]
  rw [← Finset.sum_mul, hNorm, one_mul]

theorem interactionContrastProfile_coordinateAdditive_invariant {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (i : Fin (n + 1)) (u0 u : U)
    (z : Fin (n + 1) → U) :
    interactionContrastProfile q
      (fun x ↦ F x + coordinateAdditiveWorld g b x) i u0 u z =
      interactionContrastProfile q F i u0 u z := by
  unfold interactionContrastProfile
  have hResponse : ∀ a : U,
      productResponse q (fun x ↦ F x + coordinateAdditiveWorld g b x) i a =
        productResponse q F i a +
          productResponse q (coordinateAdditiveWorld g b) i a := by
    intro a
    unfold productResponse productExpectation
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hResponse u, hResponse u0]
  have hLocal := coordinateAdditiveWorld_update_difference g b i u u0 z
  have hMean := productResponse_coordinateAdditive_difference q g b hNorm i u u0
  linarith

/-- Context variation of centered local contrasts is exactly the existing D6
mixed difference, with an explicit orientation. -/
theorem interactionContrastProfile_cycle_identity {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (x c : Fin (n + 1) → U) :
    (interactionContrastProfile q F i u0 u x -
        interactionContrastProfile q F i u0 v x) -
      (interactionContrastProfile q F i u0 u c -
        interactionContrastProfile q F i u0 v c) =
      mixedDifference F i (Function.update x i u) (Function.update c i v) := by
  unfold interactionContrastProfile mixedDifference
  simp [Function.update]
  ring

/-- A unit/delta mixed-difference bound controls every two-context change of
every centered local action contrast.  This is the strongest direct relation
that does not introduce an additional finite `sSup` API. -/
theorem interactionContrastProfile_two_context_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (delta : ℝ)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (i : Fin (n + 1)) (u0 u v : U)
    (x c : Fin (n + 1) → U) :
    |(interactionContrastProfile q F i u0 u x -
        interactionContrastProfile q F i u0 v x) -
      (interactionContrastProfile q F i u0 u c -
        interactionContrastProfile q F i u0 v c)| ≤ delta := by
  rw [interactionContrastProfile_cycle_identity]
  exact hdelta i (Function.update x i u) (Function.update c i v)

end CIGAMF.P13.D6InteractionContrastProfile
