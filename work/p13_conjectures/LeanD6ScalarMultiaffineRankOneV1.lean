import Mathlib
import «LeanD6RankOneReferenceInvarianceV1»
import «LeanD6InteractionContrastRankOneMinorsV1»

/-!
# Scalar multiaffine worlds are rank one at every coordinate

This is the SUFFICIENCY half of the D6 normal-form question.  A world in
scalar multiaffine normal form

  `F a = (sum_j g j (a j) + b) + sum_{S} W S * prod_{j in S} phi j (a j)`

has, at every coordinate `i`, a centred interaction-contrast profile that
factors as `(phi i u - phi i u0) * (H_i z - E_q H_i)`.  The action factor is
the latent scalar contrast and the context factor is the coordinate-`i`
cofactor of the tensor core, recentred at the reference.

Only normalization of the reference is assumed -- no strict positivity, so
deterministic references are covered.

The CONVERSE (rank one at every coordinate implies this normal form) is NOT
proved here and is not asserted anywhere in this file.  No decision or
half-factor bound is claimed either.
-/

namespace CIGAMF.P13.D6ScalarMultiaffineRankOne

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastRankOneMinors
open CIGAMF.P13.D6RankOneReferenceInvariance

variable {U : Type*} [Fintype U] [Nonempty U]

/-- A world in scalar multiaffine normal form: a coordinate-additive part plus
a tensor core in the scalar latent maps `phi`. -/
noncomputable def scalarMultiaffineWorld {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (a : Fin (n + 1) → U) : ℝ :=
  ((∑ j, g j (a j)) + b) +
    ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
      W S * ∏ j ∈ S, phi j (a j)

/-- The coordinate-`i` cofactor of the tensor core. -/
noncomputable def multiaffineContextFactor {n : ℕ}
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (z : Fin (n + 1) → U) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
    (if i ∈ S then W S * ∏ j ∈ S.erase i, phi j (z j) else 0)

private theorem additive_slice_contrast {n : ℕ}
    (g : Fin (n + 1) → U → ℝ)
    (i : Fin (n + 1)) (u v : U) (z : Fin (n + 1) → U) :
    (∑ j, g j ((Function.update z i u) j)) -
        (∑ j, g j ((Function.update z i v) j)) = g i u - g i v := by
  classical
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp [Function.update]
  · intro j _ hji
    simp [Function.update, hji]
  · simp

private theorem core_prod_update {n : ℕ}
    (phi : Fin (n + 1) → U → ℝ)
    (i : Fin (n + 1)) (u : U) (z : Fin (n + 1) → U)
    (S : Finset (Fin (n + 1))) (hiS : i ∈ S) :
    (∏ j ∈ S, phi j ((Function.update z i u) j)) =
      phi i u * ∏ j ∈ S.erase i, phi j (z j) := by
  classical
  have h1 : (∏ j ∈ S, phi j ((Function.update z i u) j)) =
      phi i ((Function.update z i u) i) *
        ∏ j ∈ S.erase i, phi j ((Function.update z i u) j) :=
    (Finset.mul_prod_erase S (fun j => phi j ((Function.update z i u) j)) hiS).symm
  have h2 : (Function.update z i u) i = u := by simp [Function.update]
  have h3 : (∏ j ∈ S.erase i, phi j ((Function.update z i u) j)) =
      ∏ j ∈ S.erase i, phi j (z j) := by
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [Function.update, hji]
  rw [h1, h2, h3]

private theorem core_prod_update_not_mem {n : ℕ}
    (phi : Fin (n + 1) → U → ℝ)
    (i : Fin (n + 1)) (u : U) (z : Fin (n + 1) → U)
    (S : Finset (Fin (n + 1))) (hiS : i ∉ S) :
    (∏ j ∈ S, phi j ((Function.update z i u) j)) = ∏ j ∈ S, phi j (z j) := by
  classical
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hji : j ≠ i := by
    intro hEq
    exact hiS (hEq ▸ hj)
  simp [Function.update, hji]

/-- The exact slice contrast of a scalar multiaffine world: a constant in the
context plus the latent action contrast times the coordinate cofactor. -/
theorem scalarMultiaffineWorld_slice_contrast {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (u v : U) (z : Fin (n + 1) → U) :
    scalarMultiaffineWorld g b phi W (Function.update z i u) -
        scalarMultiaffineWorld g b phi W (Function.update z i v) =
      (g i u - g i v) +
        (phi i u - phi i v) * multiaffineContextFactor phi W i z := by
  classical
  unfold scalarMultiaffineWorld multiaffineContextFactor
  have hAdd := additive_slice_contrast g i u v z
  have hCore :
      (∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
          W S * ∏ j ∈ S, phi j ((Function.update z i u) j)) -
        (∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
          W S * ∏ j ∈ S, phi j ((Function.update z i v) j)) =
      (phi i u - phi i v) *
        ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
          (if i ∈ S then W S * ∏ j ∈ S.erase i, phi j (z j) else 0) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro S _
    by_cases hiS : i ∈ S
    · rw [core_prod_update phi i u z S hiS, core_prod_update phi i v z S hiS,
        if_pos hiS]
      ring
    · rw [core_prod_update_not_mem phi i u z S hiS,
        core_prod_update_not_mem phi i v z S hiS, if_neg hiS]
      ring
  linarith [hAdd, hCore]

/-- The EXPLICIT centred profile of a scalar multiaffine world.  Stating it as an
equation, rather than only as the existential `InteractionContrastRankOne`, is
what lets downstream results talk about the actual action coefficient
`phi i u - phi i u0` instead of an anonymous witness. -/
theorem scalarMultiaffineWorld_profile_explicit {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (u0 u : U) (z : Fin (n + 1) → U) :
    interactionContrastProfile q (scalarMultiaffineWorld g b phi W) i u0 u z =
      (phi i u - phi i u0) *
        (multiaffineContextFactor phi W i z -
          productExpectation q (multiaffineContextFactor phi W i)) := by
  classical
  set F := scalarMultiaffineWorld g b phi W with hF
  set H := multiaffineContextFactor phi W i with hH
  have hslice : ∀ c : Fin (n + 1) → U,
      F (Function.update c i u) - F (Function.update c i u0) =
        (g i u - g i u0) + (phi i u - phi i u0) * H c := by
    intro c
    rw [hF, hH]
    exact scalarMultiaffineWorld_slice_contrast g b phi W i u u0 c
  have hq : productResponse q F i u - productResponse q F i u0 =
      (g i u - g i u0) + (phi i u - phi i u0) * productExpectation q H := by
    rw [productResponse_contrast_eq_productExpectation q F i u0 u,
      productExpectation_congr q
        (fun c => F (Function.update c i u) - F (Function.update c i u0))
        (fun c => (g i u - g i u0) + (phi i u - phi i u0) * H c) hslice,
      productExpectation_const_add_smul q hNorm
        (g i u - g i u0) (phi i u - phi i u0) H]
  unfold interactionContrastProfile
  rw [hq, hslice z]
  ring

/-- Two actions with the same latent value have the SAME centred profile, at
every context.  This is the two-profile mechanism: the number of distinct
profiles at a coordinate is at most the number of distinct values of `phi`. -/
theorem scalarMultiaffineWorld_profile_eq_of_phi_eq {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U) (hphi : phi i u = phi i v)
    (z : Fin (n + 1) → U) :
    interactionContrastProfile q (scalarMultiaffineWorld g b phi W) i u0 u z =
      interactionContrastProfile q (scalarMultiaffineWorld g b phi W) i u0 v z := by
  rw [scalarMultiaffineWorld_profile_explicit q hNorm g b phi W i u0 u z,
    scalarMultiaffineWorld_profile_explicit q hNorm g b phi W i u0 v z, hphi]

/-- A scalar multiaffine world is rank one at every coordinate, for every
normalized product reference. -/
theorem scalarMultiaffineWorld_interactionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (u0 : U) :
    InteractionContrastRankOne q (scalarMultiaffineWorld g b phi W) i u0 := by
  refine ⟨fun z => multiaffineContextFactor phi W i z -
      productExpectation q (multiaffineContextFactor phi W i),
    fun u => phi i u - phi i u0, by ring, ?_⟩
  intro u z
  exact scalarMultiaffineWorld_profile_explicit q hNorm g b phi W i u0 u z

theorem scalarMultiaffineWorld_allCoordinatesInteractionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ) :
    AllCoordinatesInteractionContrastRankOne q
      (scalarMultiaffineWorld g b phi W) := by
  intro i
  exact scalarMultiaffineWorld_interactionContrastRankOne q hNorm g b phi W i
    canonicalInteractionContrastAnchor

/-- Every scalar multiaffine world satisfies the exact minor constraints that
the raw-world search writes.  This is what makes the normal-form
parametrization a sound search space: every point it produces is a genuine
rank-one witness. -/
theorem scalarMultiaffineWorld_allMinorsZero {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (u0 : U) :
    AllInteractionContrastProfileMinorsZero q
      (scalarMultiaffineWorld g b phi W) i u0 :=
  interactionContrastRankOne_implies_all_minors_zero q
    (scalarMultiaffineWorld g b phi W) i u0
    (scalarMultiaffineWorld_interactionContrastRankOne q hNorm g b phi W i u0)

end CIGAMF.P13.D6ScalarMultiaffineRankOne
