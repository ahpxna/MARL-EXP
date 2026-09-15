import Mathlib
import «LeanD6InteractionContrastProfileReductionV1»

/-!
# Profile-fibre additive steering

Two actions in the SAME interaction fibre of a rank-one coordinate can still
carry different first-order response offsets.  That offset moves the
coordinate's response span, hence Top-C selection, while leaving the
interaction rank untouched.

The context-local half of this is already proved upstream:
`identical_profiles_local_contrast` says equal centred profiles force the raw
local contrast to be exactly the context-independent response contrast.  What
is added here is the rank-one form -- equal `lambda` values put two actions in
one fibre -- and the predicate that would forbid the steering.

`ProfileFibreConsistent` is stated as a PREDICATE ON A WORLD, deliberately not
as a theorem: whether rank one implies it is an open question and is not
asserted anywhere in this file.  Nothing here proves, or assumes, any decision
or half-factor bound.
-/

namespace CIGAMF.P13.D6ProfileFibreAdditiveSteering

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastProfileReduction

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Under rank one, equal action coefficients put two actions in one interaction
fibre: their centred profiles agree at every context. -/
theorem interactionContrastRankOne_same_lambda_profiles_eq {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ)
    (hProfile : ∀ w z, interactionContrastProfile q F i u0 w z = lambda w * h z)
    (huv : lambda u = lambda v) :
    ∀ z, interactionContrastProfile q F i u0 u z =
      interactionContrastProfile q F i u0 v z := by
  intro z
  rw [hProfile u z, hProfile v z, huv]

/-- Actions in one interaction fibre differ, at every context, by exactly their
first-order response contrast.  The interaction part is gone; what remains is a
pure additive offset. -/
theorem interactionContrastRankOne_same_lambda_implies_additive_difference {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ)
    (hProfile : ∀ w z, interactionContrastProfile q F i u0 w z = lambda w * h z)
    (huv : lambda u = lambda v) (z : Fin (n + 1) → U) :
    F (Function.update z i u) - F (Function.update z i v) =
      productResponse q F i u - productResponse q F i v :=
  identical_profiles_local_contrast q F i u0 u v
    (interactionContrastRankOne_same_lambda_profiles_eq q F i u0 u v h lambda hProfile huv) z

/-- The offset really is unconstrained by the fibre: the difference above is a
constant in the context, so it is carried entirely by `productResponse`. -/
theorem interactionContrastRankOne_same_lambda_difference_is_context_free {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ)
    (hProfile : ∀ w z, interactionContrastProfile q F i u0 w z = lambda w * h z)
    (huv : lambda u = lambda v) (y z : Fin (n + 1) → U) :
    F (Function.update y i u) - F (Function.update y i v) =
      F (Function.update z i u) - F (Function.update z i v) := by
  rw [interactionContrastRankOne_same_lambda_implies_additive_difference
        q F i u0 u v h lambda hProfile huv y,
    interactionContrastRankOne_same_lambda_implies_additive_difference
        q F i u0 u v h lambda hProfile huv z]

/-- The candidate condition that would forbid profile-fibre additive steering:
actions sharing an interaction coefficient must also share their first-order
response.  This is a HYPOTHESIS on a world.  It is NOT claimed to follow from
rank one, and no bound is derived from it here. -/
def ProfileFibreConsistent {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) : Prop :=
  ∀ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ),
    lambda u0 = 0 →
    (∀ w z, interactionContrastProfile q F i u0 w z = lambda w * h z) →
    ∀ u v, lambda u = lambda v → productResponse q F i u = productResponse q F i v

/-- Under `ProfileFibreConsistent`, fibre-mates are genuinely interchangeable:
the world value itself is unchanged at every context, not merely the
interaction part. -/
theorem profileFibreConsistent_fibre_mates_interchangeable {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U)
    (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ)
    (hAnchor : lambda u0 = 0)
    (hProfile : ∀ w z, interactionContrastProfile q F i u0 w z = lambda w * h z)
    (hConsistent : ProfileFibreConsistent q F i u0)
    (huv : lambda u = lambda v) (z : Fin (n + 1) → U) :
    F (Function.update z i u) = F (Function.update z i v) := by
  have hAdd := interactionContrastRankOne_same_lambda_implies_additive_difference
    q F i u0 u v h lambda hProfile huv z
  have hResp := hConsistent h lambda hAnchor hProfile u v huv
  rw [hResp] at hAdd
  linarith

end CIGAMF.P13.D6ProfileFibreAdditiveSteering
