import Mathlib
import «LeanD6InteractionContrastProfileReductionV1»

namespace CIGAMF.P13.D6TwoProfileImpliesRankOne

open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastProfileReduction

variable {U : Type*} [Fintype U] [Nonempty U]

theorem binary_hasAtMostTwoInteractionProfiles {n : ℕ}
    (q : Fin (n + 1) → Fin 2 → ℝ)
    (F : (Fin (n + 1) → Fin 2) → ℝ)
    (i : Fin (n + 1)) (u0 : Fin 2) :
    HasAtMostTwoInteractionProfiles q F i u0 := by
  refine ⟨0, 1, ?_⟩
  intro u
  fin_cases u
  · exact Or.inl (fun _ ↦ rfl)
  · exact Or.inr (fun _ ↦ rfl)

theorem hasAtMostTwoInteractionProfiles_zero_or_representative {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hTwo : HasAtMostTwoInteractionProfiles q F i u0) :
    ∃ r : U, ∀ u,
      (∀ z, interactionContrastProfile q F i u0 u z = 0) ∨
      (∀ z, interactionContrastProfile q F i u0 u z =
        interactionContrastProfile q F i u0 r z) := by
  rcases hTwo with ⟨a, b, hTwo⟩
  rcases hTwo u0 with h0a | h0b
  · refine ⟨b, ?_⟩
    intro u
    rcases hTwo u with hua | hub
    · left
      intro z
      calc
        interactionContrastProfile q F i u0 u z =
            interactionContrastProfile q F i u0 a z := hua z
        _ = interactionContrastProfile q F i u0 u0 z := (h0a z).symm
        _ = 0 := interactionContrastProfile_anchor q F i u0 z
    · exact Or.inr hub
  · refine ⟨a, ?_⟩
    intro u
    rcases hTwo u with hua | hub
    · exact Or.inr hua
    · left
      intro z
      calc
        interactionContrastProfile q F i u0 u z =
            interactionContrastProfile q F i u0 b z := hub z
        _ = interactionContrastProfile q F i u0 u0 z := (h0b z).symm
        _ = 0 := interactionContrastProfile_anchor q F i u0 z

theorem hasAtMostTwoInteractionProfiles_implies_rankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hTwo : HasAtMostTwoInteractionProfiles q F i u0) :
    InteractionContrastRankOne q F i u0 := by
  classical
  rcases hasAtMostTwoInteractionProfiles_zero_or_representative
    (q := q) (F := F) (i := i) (u0 := u0) hTwo with ⟨r, hr⟩
  let h : (Fin (n + 1) → U) → ℝ :=
    fun z ↦ interactionContrastProfile q F i u0 r z
  let lambda : U → ℝ := fun u ↦
    if (∀ z, interactionContrastProfile q F i u0 u z = 0) then 0 else 1
  refine ⟨h, lambda, ?_, ?_⟩
  · have hz : ∀ z, interactionContrastProfile q F i u0 u0 z = 0 := by
      intro z
      exact interactionContrastProfile_anchor q F i u0 z
    simp [lambda, hz]
  · intro u z
    rcases hr u with hzero | hrep
    · simp [lambda, hzero, h, hzero z]
    · by_cases hzall : ∀ x, interactionContrastProfile q F i u0 u x = 0
      · simp [lambda, hzall, h, hzall z]
      · have hone : lambda u = 1 := by simp [lambda, hzall]
        rw [hone, one_mul]
        exact hrep z

end CIGAMF.P13.D6TwoProfileImpliesRankOne
