import Mathlib
import «LeanD6InteractionContrastRankOneV1»

/-!
# Exact minor characterization of D6 interaction-contrast rank one

This is the semantic bridge for the B3 raw-world optimizer.  The optimizer
constrains every centred-profile `2 x 2` minor; this file proves that those
constraints are exactly the existing factorization predicate, including the
all-zero-profile degeneracy.

It deliberately proves no decision or half-factor bound.
-/

namespace CIGAMF.P13.D6InteractionContrastRankOneMinors

open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

def AllInteractionContrastProfileMinorsZero {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) : Prop :=
  ∀ (u v : U) (x y : Fin (n + 1) → U),
    interactionContrastProfile q F i u0 u x *
        interactionContrastProfile q F i u0 v y -
      interactionContrastProfile q F i u0 u y *
        interactionContrastProfile q F i u0 v x = 0

theorem interactionContrastRankOne_implies_all_minors_zero {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    AllInteractionContrastProfileMinorsZero q F i u0 := by
  rcases hRank with ⟨h, lambda, -, hProfile⟩
  intro u v x y
  rw [hProfile u x, hProfile v y, hProfile u y, hProfile v x]
  ring

theorem all_minors_zero_implies_interactionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hMinor : AllInteractionContrastProfileMinorsZero q F i u0) :
    InteractionContrastRankOne q F i u0 := by
  classical
  by_cases hNonzero : ∃ (u : U) (z : Fin (n + 1) → U),
      interactionContrastProfile q F i u0 u z ≠ 0
  · rcases hNonzero with ⟨uStar, zStar, hStar⟩
    let h : (Fin (n + 1) → U) → ℝ :=
      fun z ↦ interactionContrastProfile q F i u0 uStar z
    let lambda : U → ℝ :=
      fun u ↦ interactionContrastProfile q F i u0 u zStar /
        interactionContrastProfile q F i u0 uStar zStar
    refine ⟨h, lambda, ?_, ?_⟩
    · rw [show lambda u0 =
          interactionContrastProfile q F i u0 u0 zStar /
            interactionContrastProfile q F i u0 uStar zStar by rfl,
        interactionContrastProfile_anchor]
      simp
    · intro u z
      have hEq := hMinor u uStar z zStar
      change interactionContrastProfile q F i u0 u z =
        (interactionContrastProfile q F i u0 u zStar /
          interactionContrastProfile q F i u0 uStar zStar) *
          interactionContrastProfile q F i u0 uStar z
      calc
        interactionContrastProfile q F i u0 u z =
            (interactionContrastProfile q F i u0 u zStar *
              interactionContrastProfile q F i u0 uStar z) /
              interactionContrastProfile q F i u0 uStar zStar := by
                apply (eq_div_iff hStar).2
                linarith
        _ = (interactionContrastProfile q F i u0 u zStar /
              interactionContrastProfile q F i u0 uStar zStar) *
              interactionContrastProfile q F i u0 uStar z := by ring
  · refine ⟨fun _ ↦ 0, fun _ ↦ 0, rfl, ?_⟩
    intro u z
    have hZero : interactionContrastProfile q F i u0 u z = 0 := by
      by_contra h
      exact hNonzero ⟨u, z, h⟩
    simp [hZero]

theorem interactionContrastRankOne_iff_all_minors_zero {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) :
    InteractionContrastRankOne q F i u0 ↔
      AllInteractionContrastProfileMinorsZero q F i u0 := by
  exact ⟨interactionContrastRankOne_implies_all_minors_zero q F i u0,
    all_minors_zero_implies_interactionContrastRankOne q F i u0⟩

end CIGAMF.P13.D6InteractionContrastRankOneMinors
