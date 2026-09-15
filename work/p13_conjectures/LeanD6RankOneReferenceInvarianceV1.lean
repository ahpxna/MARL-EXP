import Mathlib
import «LeanD6InteractionContrastRankOneMinorsV1»

/-!
# The D6 rank-one class does not depend on the product reference

The centred interaction-contrast profile subtracts exactly the reference
expectation of the raw slice contrast.  Changing the product reference
therefore shifts every profile by a single constant per action, which is
absorbed into the context factor and leaves the action factor untouched.

Consequence: `InteractionContrastRankOne` is a property of the world `F`
alone, not of the pair `(q, F)`, for every normalized product reference.
The only hypothesis is normalization of the target reference -- no strict
positivity, so deterministic (point-mass) references are covered.

This is the formal justification for reusing one linear rank-one fibre
across every reference in the raw-world search: the fibre is reference-free,
only the decision objective is not.

No decision or half-factor bound is claimed here.
-/

namespace CIGAMF.P13.D6RankOneReferenceInvariance

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastRankOneMinors

variable {U : Type*} [Fintype U] [Nonempty U]

/-- The product-response contrast is the reference expectation of the raw
slice contrast.  This is the only place the reference enters a profile. -/
theorem productResponse_contrast_eq_productExpectation {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u : U) :
    productResponse q F i u - productResponse q F i u0 =
      productExpectation q
        (fun c => F (Function.update c i u) - F (Function.update c i u0)) := by
  classical
  unfold productResponse productExpectation
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro c _
  ring

theorem productExpectation_congr {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (G G' : (Fin (n + 1) → U) → ℝ)
    (hG : ∀ c, G c = G' c) :
    productExpectation q G = productExpectation q G' := by
  classical
  unfold productExpectation
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [hG c]

/-- A normalized product reference sends a constant plus a scaled function to
the constant plus the scaled expectation. -/
theorem productExpectation_const_add_smul {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (K lam : ℝ) (h : (Fin (n + 1) → U) → ℝ) :
    productExpectation q (fun c => K + lam * h c) =
      K + lam * productExpectation q h := by
  classical
  unfold productExpectation
  calc
    (∑ c, jointWeight q c * (K + lam * h c))
        = ∑ c, (jointWeight q c * K + lam * (jointWeight q c * h c)) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = (∑ c, jointWeight q c * K) + ∑ c, lam * (jointWeight q c * h c) :=
          Finset.sum_add_distrib
    _ = (∑ c, jointWeight q c) * K + lam * ∑ c, jointWeight q c * h c := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = K + lam * ∑ c, jointWeight q c * h c := by
          rw [hNorm, one_mul]

/-- Rank one transfers to any normalized product reference, with the SAME
action factor `lambda` and the context factor recentred. -/
theorem interactionContrastRankOne_reference_transfer {n : ℕ}
    (q q' : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hNorm : ∑ c, jointWeight q' c = 1)
    (hRank : InteractionContrastRankOne q F i u0) :
    InteractionContrastRankOne q' F i u0 := by
  classical
  rcases hRank with ⟨h, lambda, hAnchor, hProfile⟩
  refine ⟨fun z => h z - productExpectation q' h, lambda, hAnchor, ?_⟩
  intro u z
  show interactionContrastProfile q' F i u0 u z =
    lambda u * (h z - productExpectation q' h)
  have hslice : ∀ c : Fin (n + 1) → U,
      F (Function.update c i u) - F (Function.update c i u0) =
        (productResponse q F i u - productResponse q F i u0) +
          lambda u * h c := by
    intro c
    have hc := hProfile u c
    unfold interactionContrastProfile at hc
    linarith
  have hq' : productResponse q' F i u - productResponse q' F i u0 =
      (productResponse q F i u - productResponse q F i u0) +
        lambda u * productExpectation q' h := by
    rw [productResponse_contrast_eq_productExpectation q' F i u0 u,
      productExpectation_congr q'
        (fun c => F (Function.update c i u) - F (Function.update c i u0))
        (fun c => (productResponse q F i u - productResponse q F i u0) +
          lambda u * h c) hslice,
      productExpectation_const_add_smul q' hNorm
        (productResponse q F i u - productResponse q F i u0) (lambda u) h]
  unfold interactionContrastProfile
  rw [hq', hslice z]
  ring

theorem interactionContrastRankOne_reference_free {n : ℕ}
    (q q' : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hNorm' : ∑ c, jointWeight q' c = 1) :
    InteractionContrastRankOne q F i u0 ↔
      InteractionContrastRankOne q' F i u0 :=
  ⟨interactionContrastRankOne_reference_transfer q q' F i u0 hNorm',
    interactionContrastRankOne_reference_transfer q' q F i u0 hNorm⟩

theorem allCoordinatesInteractionContrastRankOne_reference_transfer {n : ℕ}
    (q q' : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hNorm : ∑ c, jointWeight q' c = 1)
    (hAll : AllCoordinatesInteractionContrastRankOne q F) :
    AllCoordinatesInteractionContrastRankOne q' F := by
  intro i
  exact interactionContrastRankOne_reference_transfer q q' F i
    canonicalInteractionContrastAnchor hNorm (hAll i)

theorem allCoordinatesInteractionContrastRankOne_reference_free {n : ℕ}
    (q q' : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hNorm' : ∑ c, jointWeight q' c = 1) :
    AllCoordinatesInteractionContrastRankOne q F ↔
      AllCoordinatesInteractionContrastRankOne q' F :=
  ⟨allCoordinatesInteractionContrastRankOne_reference_transfer q q' F hNorm',
    allCoordinatesInteractionContrastRankOne_reference_transfer q' q F hNorm⟩

/-- The exact minor constraints imposed by the raw-world search are themselves
reference-free.  Composing the two directions of the minor bridge, the
constraint set a solver writes at one reference is the constraint set at every
normalized reference. -/
theorem allInteractionContrastProfileMinorsZero_reference_transfer {n : ℕ}
    (q q' : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hNorm : ∑ c, jointWeight q' c = 1)
    (hMinor : AllInteractionContrastProfileMinorsZero q F i u0) :
    AllInteractionContrastProfileMinorsZero q' F i u0 :=
  interactionContrastRankOne_implies_all_minors_zero q' F i u0
    (interactionContrastRankOne_reference_transfer q q' F i u0 hNorm
      (all_minors_zero_implies_interactionContrastRankOne q F i u0 hMinor))

end CIGAMF.P13.D6RankOneReferenceInvariance
