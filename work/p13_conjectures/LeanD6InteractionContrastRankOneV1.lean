import Mathlib
import «LeanD6InteractionContrastProfileV1»

/-!
# Rank-one centered interaction contrast profiles

The predicate here is deliberately factorization-based rather than a matrix
rank construction.  It says exactly that all local action profiles at one
coordinate are collinear as functions of the complement context.
-/

namespace CIGAMF.P13.D6InteractionContrastRankOne

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6InteractionContrastProfile

variable {U : Type*} [Fintype U] [Nonempty U]

def InteractionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) : Prop :=
  ∃ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ),
    lambda u0 = 0 ∧
      ∀ u z,
        interactionContrastProfile q F i u0 u z = lambda u * h z

noncomputable def canonicalInteractionContrastAnchor : U :=
  Classical.choice (inferInstance : Nonempty U)

def AllCoordinatesInteractionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  ∀ i, InteractionContrastRankOne q F i canonicalInteractionContrastAnchor

theorem binary_interactionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → Fin 2 → ℝ)
    (F : (Fin (n + 1) → Fin 2) → ℝ)
    (i : Fin (n + 1)) :
    InteractionContrastRankOne q F i 0 := by
  let h : (Fin (n + 1) → Fin 2) → ℝ :=
    fun z ↦ interactionContrastProfile q F i 0 1 z
  let lambda : Fin 2 → ℝ := fun u ↦ if u = 1 then 1 else 0
  refine ⟨h, lambda, ?_, ?_⟩
  · simp [lambda]
  · intro u z
    fin_cases u
    · simp [h, lambda, interactionContrastProfile_anchor]
    · simp [h, lambda]

theorem interactionContrastRankOne_cycle_factorization {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    ∃ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ),
      lambda u0 = 0 ∧
      ∀ (u v : U) (x c : Fin (n + 1) → U),
        cycleFunctional i (Function.update x i u) (Function.update c i v) F =
          (lambda u - lambda v) * (h x - h c) := by
  rcases hRank with ⟨h, lambda, hAnchor, hProfile⟩
  refine ⟨h, lambda, hAnchor, ?_⟩
  intro u v x c
  rw [cycleFunctional_eq_mixedDifference,
    ← interactionContrastProfile_cycle_identity]
  rw [hProfile u x, hProfile v x, hProfile u c, hProfile v c]
  ring

/-- A nonzero `2 × 2` determinant of profile values is an exact obstruction
to rank one.  It supplies finite rational witnesses without matrix-rank API. -/
theorem interactionContrastProfile_determinant_obstruction {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (x y : Fin (n + 1) → U)
    (hdet :
      interactionContrastProfile q F i u0 u x *
          interactionContrastProfile q F i u0 v y -
        interactionContrastProfile q F i u0 u y *
          interactionContrastProfile q F i u0 v x ≠ 0) :
    ¬ InteractionContrastRankOne q F i u0 := by
  intro hRank
  rcases hRank with ⟨h, lambda, _, hProfile⟩
  apply hdet
  rw [hProfile u x, hProfile v y, hProfile u y, hProfile v x]
  ring

end CIGAMF.P13.D6InteractionContrastRankOne
