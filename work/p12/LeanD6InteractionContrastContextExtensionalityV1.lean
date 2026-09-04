import Mathlib
import «LeanD6InteractionContrastProfileV1»

namespace CIGAMF.P13.D6InteractionContrastContextExtensionality

open CIGAMF.P13.D6InteractionContrastProfile

variable {U : Type*} [Fintype U] [Nonempty U]

theorem interactionContrastProfile_same_after_source_overwrite {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (z : Fin (n + 1) → U) :
    interactionContrastProfile q F i u0 u (Function.update z i v) =
      interactionContrastProfile q F i u0 u z := by
  have hu :
      Function.update (Function.update z i v) i u =
        Function.update z i u := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update, hji]
  have hu0 :
      Function.update (Function.update z i v) i u0 =
        Function.update z i u0 := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update, hji]
  unfold interactionContrastProfile
  rw [hu, hu0]

end CIGAMF.P13.D6InteractionContrastContextExtensionality
