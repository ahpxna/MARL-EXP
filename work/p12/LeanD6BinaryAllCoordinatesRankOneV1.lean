import Mathlib
import «LeanD6InteractionContrastAnchorInvarianceV1»

namespace CIGAMF.P13.D6BinaryAllCoordinatesRankOne

open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastAnchorInvariance

theorem binary_interactionContrastRankOne_any_anchor {n : ℕ}
    (q : Fin (n + 1) → Fin 2 → ℝ)
    (F : (Fin (n + 1) → Fin 2) → ℝ)
    (i : Fin (n + 1)) (a : Fin 2) :
    InteractionContrastRankOne q F i a := by
  exact interactionContrastRankOne_anchor q F i (0 : Fin 2) a
    (binary_interactionContrastRankOne q F i)

theorem binary_allCoordinatesInteractionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → Fin 2 → ℝ)
    (F : (Fin (n + 1) → Fin 2) → ℝ) :
    AllCoordinatesInteractionContrastRankOne q F := by
  intro i
  exact binary_interactionContrastRankOne_any_anchor q F i
    canonicalInteractionContrastAnchor

end CIGAMF.P13.D6BinaryAllCoordinatesRankOne
