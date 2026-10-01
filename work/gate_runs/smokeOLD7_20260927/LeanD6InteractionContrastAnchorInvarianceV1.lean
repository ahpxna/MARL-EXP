import Mathlib
import «LeanD6InteractionContrastRankOneV1»

namespace CIGAMF.P13.D6InteractionContrastAnchorInvariance

open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

theorem interactionContrastProfile_change_anchor {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 v0 u : U)
    (z : Fin (n + 1) → U) :
    interactionContrastProfile q F i v0 u z =
      interactionContrastProfile q F i u0 u z -
        interactionContrastProfile q F i u0 v0 z := by
  unfold interactionContrastProfile
  ring

theorem interactionContrastRankOne_anchor {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 v0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    InteractionContrastRankOne q F i v0 := by
  rcases hRank with ⟨h, lambda, hAnchor, hProfile⟩
  refine ⟨h, (fun u ↦ lambda u - lambda v0), ?_, ?_⟩
  · ring
  · intro u z
    rw [interactionContrastProfile_change_anchor
      (q := q) (F := F) (i := i) (u0 := u0) (v0 := v0)
      (u := u) (z := z)]
    rw [hProfile u z, hProfile v0 z]
    ring

theorem interactionContrastRankOne_anchor_iff {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 v0 : U) :
    InteractionContrastRankOne q F i u0 ↔
      InteractionContrastRankOne q F i v0 := by
  constructor
  · intro h
    exact interactionContrastRankOne_anchor q F i u0 v0 h
  · intro h
    exact interactionContrastRankOne_anchor q F i v0 u0 h

end CIGAMF.P13.D6InteractionContrastAnchorInvariance
