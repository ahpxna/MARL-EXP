import Mathlib
import «LeanD6InteractionContrastRankOneV1»

/-!
# D6-R1: the local affine slice form of interaction-contrast rank one

Rank one of the centered interaction-contrast profiles at coordinate `i` is
literally an affine slice statement about the world function itself: along the
`i`-th coordinate, `F` is its anchor value plus the (context-free) product
response contrast plus a single rank-one interaction term `lambda u * h z`.

This file is pure rearrangement of the existing factorization predicate.  No
decision bound, no half-factor claim, and no cardinality claim is made here.
-/

namespace CIGAMF.P13.D6RankOneLocalAffineSlice

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Rank one gives an explicit affine-in-the-slice normal form for `F`. -/
theorem interactionContrastRankOne_local_affine_slice {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : InteractionContrastRankOne q F i u0) :
    ∃ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ),
      lambda u0 = 0 ∧
        ∀ u z,
          F (Function.update z i u) =
            F (Function.update z i u0) +
              (productResponse q F i u - productResponse q F i u0) +
              lambda u * h z := by
  rcases hRank with ⟨h, lambda, hAnchor, hProfile⟩
  refine ⟨h, lambda, hAnchor, ?_⟩
  intro u z
  have hz := hProfile u z
  unfold interactionContrastProfile at hz
  linarith

/-- The affine slice form is not weaker: it returns the rank-one predicate. -/
theorem local_affine_slice_implies_interactionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hSlice : ∃ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ),
      lambda u0 = 0 ∧
        ∀ u z,
          F (Function.update z i u) =
            F (Function.update z i u0) +
              (productResponse q F i u - productResponse q F i u0) +
              lambda u * h z) :
    InteractionContrastRankOne q F i u0 := by
  rcases hSlice with ⟨h, lambda, hAnchor, hSliceEq⟩
  refine ⟨h, lambda, hAnchor, ?_⟩
  intro u z
  have hz := hSliceEq u z
  unfold interactionContrastProfile
  linarith

/-- Exact equivalence of the factorization predicate and the slice normal
form. -/
theorem interactionContrastRankOne_iff_local_affine_slice {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) :
    InteractionContrastRankOne q F i u0 ↔
      ∃ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ),
        lambda u0 = 0 ∧
          ∀ u z,
            F (Function.update z i u) =
              F (Function.update z i u0) +
                (productResponse q F i u - productResponse q F i u0) +
                lambda u * h z := by
  constructor
  · intro hRank
    exact interactionContrastRankOne_local_affine_slice q F i u0 hRank
  · intro hSlice
    exact local_affine_slice_implies_interactionContrastRankOne q F i u0 hSlice

end CIGAMF.P13.D6RankOneLocalAffineSlice
