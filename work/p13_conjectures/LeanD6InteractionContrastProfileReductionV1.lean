import Mathlib
import «LeanD6InteractionContrastRankOneV1»

/-!
# Safe local reductions for D6 centered interaction profiles

These lemmas deliberately stop at context-local contrast identities.  Equal
interaction profiles do *not* make two actions globally interchangeable:
their product-response values can still differ, and downstream selection can
therefore still change.
-/

namespace CIGAMF.P13.D6InteractionContrastProfileReduction

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

/-- If two actions have the same centered interaction profile, their raw
local contrast is exactly the (context-independent) first-order response
contrast. -/
theorem identical_profiles_local_contrast {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (hProfile : ∀ z,
      interactionContrastProfile q F i u0 u z =
        interactionContrastProfile q F i u0 v z)
    (z : Fin (n + 1) → U) :
    F (Function.update z i u) - F (Function.update z i v) =
      productResponse q F i u - productResponse q F i v := by
  have hz := hProfile z
  unfold interactionContrastProfile at hz
  linarith

/-- A two-level local interaction representation.  It says only that every
action can be replaced by one of two profile representatives *inside the
centered interaction term*; it deliberately preserves its own response
offset through `identical_profiles_local_contrast`. -/
def HasAtMostTwoInteractionProfiles {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) : Prop :=
  ∃ a b : U, ∀ u,
    (∀ z, interactionContrastProfile q F i u0 u z =
      interactionContrastProfile q F i u0 a z) ∨
    (∀ z, interactionContrastProfile q F i u0 u z =
      interactionContrastProfile q F i u0 b z)

theorem two_profile_level_local_representative {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hTwo : HasAtMostTwoInteractionProfiles q F i u0)
    (u : U) :
    ∃ r : U, ∀ z,
      F (Function.update z i u) - F (Function.update z i r) =
        productResponse q F i u - productResponse q F i r := by
  rcases hTwo with ⟨a, b, hTwo⟩
  rcases hTwo u with hua | hub
  · exact ⟨a, identical_profiles_local_contrast q F i u0 u a hua⟩
  · exact ⟨b, identical_profiles_local_contrast q F i u0 u b hub⟩

/-- The already-proved rank-one factorization is exposed under a local
reduction name for downstream proof discovery. -/
theorem collinear_profiles_factor_all_cycles {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    ∃ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ), lambda u0 = 0 ∧ ∀ u v x c,
      cycleFunctional i (Function.update x i u) (Function.update c i v) F =
        (lambda u - lambda v) * (h x - h c) := by
  exact interactionContrastRankOne_cycle_factorization q F i u0 hRank

end CIGAMF.P13.D6InteractionContrastProfileReduction
