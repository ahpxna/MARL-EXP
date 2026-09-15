import Mathlib
import «LeanD6RankOneLocalAffineSliceV1»

/-!
# D6-R2a: pivot action and two-corner interpolation under rank one

Under interaction-contrast rank one at coordinate `i`, the abstract context
factor `h` is not needed: a single pivot action `v` carries the whole profile
space, and every other action's centered profile is a scalar multiple of the
pivot profile.  The scalar is anchored, `phi u0 = 0`, in both the degenerate
and the nondegenerate case.

This is the seed of the two-corner (Bernstein-form) representation.  No
subset induction, no multiaffine normal form, and no decision bound is
claimed here.
-/

namespace CIGAMF.P13.D6RankOneTwoCornerInterpolation

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6RankOneLocalAffineSlice

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Rank one is exactly collinearity with one pivot action's profile. -/
theorem interactionContrastRankOne_pivot_profile {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    ∃ (v : U) (phi : U → ℝ),
      phi u0 = 0 ∧
        ∀ u z,
          interactionContrastProfile q F i u0 u z =
            phi u * interactionContrastProfile q F i u0 v z := by
  classical
  rcases hRank with ⟨h, lambda, hAnchor, hProfile⟩
  by_cases hLam : ∃ w : U, lambda w ≠ 0
  · rcases hLam with ⟨w, hw⟩
    have key : ∀ (u : U) (z : Fin (n + 1) → U),
        interactionContrastProfile q F i u0 u z =
          lambda u / lambda w * interactionContrastProfile q F i u0 w z := by
      intro u z
      have hcancel : lambda u / lambda w * lambda w = lambda u :=
        div_mul_cancel₀ (lambda u) hw
      rw [hProfile u z, hProfile w z, ← mul_assoc, hcancel]
    exact ⟨w, fun u ↦ lambda u / lambda w, by simp [hAnchor], key⟩
  · push_neg at hLam
    refine ⟨u0, fun _ ↦ 0, rfl, ?_⟩
    intro u z
    simp [hProfile, hLam]

/-- World-level two-corner interpolation: every raw local contrast, centered
by its product response, is a scalar multiple of the pivot's centered
contrast. -/
theorem interactionContrastRankOne_two_corner_interpolation {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    ∃ (v : U) (phi : U → ℝ),
      phi u0 = 0 ∧
        ∀ u z,
          F (Function.update z i u) - F (Function.update z i u0) -
              (productResponse q F i u - productResponse q F i u0) =
            phi u *
              (F (Function.update z i v) - F (Function.update z i u0) -
                (productResponse q F i v - productResponse q F i u0)) := by
  rcases interactionContrastRankOne_pivot_profile q F i u0 hRank with
    ⟨v, phi, hAnchor, hPivot⟩
  refine ⟨v, phi, hAnchor, ?_⟩
  intro u z
  have hz := hPivot u z
  unfold interactionContrastProfile at hz
  linarith

/-- The same statement in explicit affine-combination (Bernstein seed) form:
the anchor corner carries weight `1 - phi u`, the pivot corner `phi u`. -/
theorem interactionContrastRankOne_affine_combination {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    ∃ (v : U) (phi : U → ℝ),
      phi u0 = 0 ∧
        ∀ u z,
          interactionContrastProfile q F i u0 u z =
            (1 - phi u) * interactionContrastProfile q F i u0 u0 z +
              phi u * interactionContrastProfile q F i u0 v z := by
  rcases interactionContrastRankOne_pivot_profile q F i u0 hRank with
    ⟨v, phi, hAnchor, hPivot⟩
  refine ⟨v, phi, hAnchor, ?_⟩
  intro u z
  rw [interactionContrastProfile_anchor q F i u0 z, hPivot u z]
  ring

end CIGAMF.P13.D6RankOneTwoCornerInterpolation
