import Mathlib
import «LeanD6InteractionContrastRankOneV1»

/-!
# Raw (uncentred) local contrast rank one

`interactionContrastProfile` is the local action contrast **after** subtracting
the product-reference first-order contrast.  That subtraction is exactly a
gauge quotient: it discards the additive layer.  This module keeps the additive
layer and studies the *raw* local contrast

  `rawLocalContrast F i u0 u z = F (z[i ← u]) - F (z[i ← u0])`.

The main content:

* `rawLocalContrastRankOne_iff_minors_zero` — the raw predicate is exactly the
  vanishing of every `2 × 2` minor of the (action × context) matrix of raw
  contrasts.  This is a *definition-level* falsifier: no anchor, no reference
  measure, no factorisation witness is needed to refute it.
* `rawLocalContrastRankOne_implies_interactionContrastRankOne` — raw rank one is
  strictly stronger than the centred predicate.  Centring is a projection, so it
  can only lose rank.
* `rawLocalContrastRankOne_iff_aligned` — the exact gap between the two.  Raw
  rank one holds iff the centred profile is rank one **and** the first-order
  response contrast is a scalar multiple of the very same `lambda`.  In the
  `alpha`/`lambda` language: `alpha = kappa • lambda`.  Raw rank one is therefore
  precisely "centred rank one with no independent additive gauge".
* `rawLocalContrastRankOne_of_alignment_determinant` — the determinant test
  `mu i (u,v) = alpha u * lambda v - alpha v * lambda u = 0` is *sufficient*
  for raw rank one, with no non-degeneracy hypothesis at all.
* `binary_rawLocalContrastRankOne` — a two-letter alphabet forces raw rank one
  unconditionally, for every `F`.  After anchoring there is exactly one
  non-anchor contrast, and the span of a single function has dimension at most
  one.  This is the alphabet phase, with no analytic input.

### Deliberate non-claim (degeneracy)

The converse of `rawLocalContrastRankOne_of_alignment_determinant` is **not**
stated, and is false as stated: `mu` is computed against a *chosen* centred
witness `(lambda, h)`, and when `h` is constant the witness `lambda` is not
determined by `F`, so `mu` can be made nonzero while raw rank one still holds
(then every raw contrast is a multiple of the constant function).  Any
equivalence `RawLocalContrastRankOne <-> mu = 0` must carry a hypothesis that
`h` is non-constant.  Nothing here depends on that equivalence: the falsifier
used downstream is the minor obstruction, which is witness-free.
-/

namespace CIGAMF.P13.D6RawLocalContrastRankOne

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

/-- The raw (uncentred) local action contrast at coordinate `i`, anchored at
`u0`.  It is a function of a full world state; coordinate `i` is overwritten. -/
noncomputable def rawLocalContrast {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u : U)
    (z : Fin (n + 1) → U) : ℝ :=
  F (Function.update z i u) - F (Function.update z i u0)

/-- All raw local contrasts at coordinate `i` are collinear as functions of the
complement context.  No reference measure occurs. -/
def RawLocalContrastRankOne {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) : Prop :=
  ∃ (H : (Fin (n + 1) → U) → ℝ) (theta : U → ℝ),
    theta u0 = 0 ∧ ∀ u z, rawLocalContrast F i u0 u z = theta u * H z

def AllCoordinatesRawLocalContrastRankOne {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) : Prop :=
  ∀ i, RawLocalContrastRankOne F i canonicalInteractionContrastAnchor

@[simp] theorem rawLocalContrast_anchor {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 : U)
    (z : Fin (n + 1) → U) :
    rawLocalContrast F i u0 u0 z = 0 := by
  simp [rawLocalContrast]

/-- The centred profile is the raw contrast minus its first-order part. -/
theorem interactionContrastProfile_eq_raw_sub_response {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u : U) (z : Fin (n + 1) → U) :
    interactionContrastProfile q F i u0 u z =
      rawLocalContrast F i u0 u z -
        (productResponse q F i u - productResponse q F i u0) := rfl

/-! ## Minor characterisation -/

theorem rawLocalContrastRankOne_minor_zero {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRank : RawLocalContrastRankOne F i u0)
    (u v : U) (x y : Fin (n + 1) → U) :
    rawLocalContrast F i u0 u x * rawLocalContrast F i u0 v y -
      rawLocalContrast F i u0 u y * rawLocalContrast F i u0 v x = 0 := by
  obtain ⟨H, theta, _, hfac⟩ := hRank
  rw [hfac u x, hfac v y, hfac u y, hfac v x]
  ring

theorem rawLocalContrastRankOne_of_minors_zero {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hmin : ∀ (u v : U) (x y : Fin (n + 1) → U),
      rawLocalContrast F i u0 u x * rawLocalContrast F i u0 v y -
        rawLocalContrast F i u0 u y * rawLocalContrast F i u0 v x = 0) :
    RawLocalContrastRankOne F i u0 := by
  classical
  by_cases hzero : ∀ (u : U) (z : Fin (n + 1) → U), rawLocalContrast F i u0 u z = 0
  · refine ⟨fun _ ↦ 0, fun _ ↦ 0, rfl, ?_⟩
    intro u z
    simp [hzero u z]
  · push_neg at hzero
    obtain ⟨u1, z1, hne⟩ := hzero
    refine ⟨fun z ↦ rawLocalContrast F i u0 u1 z,
      fun u ↦ rawLocalContrast F i u0 u z1 / rawLocalContrast F i u0 u1 z1, ?_, ?_⟩
    · simp
    · intro u z
      have h := hmin u u1 z z1
      rw [div_mul_eq_mul_div, eq_div_iff hne]
      linarith [h]

theorem rawLocalContrastRankOne_iff_minors_zero {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) :
    RawLocalContrastRankOne F i u0 ↔
      ∀ (u v : U) (x y : Fin (n + 1) → U),
        rawLocalContrast F i u0 u x * rawLocalContrast F i u0 v y -
          rawLocalContrast F i u0 u y * rawLocalContrast F i u0 v x = 0 :=
  ⟨fun h ↦ rawLocalContrastRankOne_minor_zero F i u0 h,
   rawLocalContrastRankOne_of_minors_zero F i u0⟩

/-- Witness-free falsifier: one nonzero `2 × 2` raw minor refutes raw rank one.
No reference measure and no factorisation candidate are involved. -/
theorem not_rawLocalContrastRankOne_of_minor_ne_zero {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 u v : U) (x y : Fin (n + 1) → U)
    (hdet :
      rawLocalContrast F i u0 u x * rawLocalContrast F i u0 v y -
        rawLocalContrast F i u0 u y * rawLocalContrast F i u0 v x ≠ 0) :
    ¬ RawLocalContrastRankOne F i u0 := by
  intro hRank
  exact hdet (rawLocalContrastRankOne_minor_zero F i u0 hRank u v x y)

/-! ## Anchor invariance -/

theorem rawLocalContrastRankOne_anchor {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 a : U)
    (hRank : RawLocalContrastRankOne F i u0) :
    RawLocalContrastRankOne F i a := by
  obtain ⟨H, theta, _, hfac⟩ := hRank
  refine ⟨H, fun u ↦ theta u - theta a, by simp, ?_⟩
  intro u z
  have h1 := hfac u z
  have h2 := hfac a z
  simp only [rawLocalContrast] at h1 h2 ⊢
  linear_combination h1 - h2

/-! ## Raw rank one slaves the additive layer to the interaction layer -/

/-- Under a raw factorisation the first-order response contrast is the *same*
`theta`, scaled by the reference mean of the context factor.  This is the
statement that raw rank one leaves no independent additive gauge.  No
normalisation of `q` is required. -/
theorem rawLocalContrast_response_contrast {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (H : (Fin (n + 1) → U) → ℝ) (theta : U → ℝ)
    (hfac : ∀ u z, rawLocalContrast F i u0 u z = theta u * H z)
    (u : U) :
    productResponse q F i u - productResponse q F i u0 =
      theta u * productExpectation q H := by
  classical
  simp only [productResponse, productExpectation]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro c _
  have hc := hfac u c
  simp only [rawLocalContrast] at hc
  linear_combination jointWeight q c * hc

theorem rawLocalContrastRankOne_implies_interactionContrastRankOne {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (hRaw : RawLocalContrastRankOne F i u0) :
    InteractionContrastRankOne q F i u0 := by
  obtain ⟨H, theta, hAnchor, hfac⟩ := hRaw
  refine ⟨fun z ↦ H z - productExpectation q H, theta, hAnchor, ?_⟩
  intro u z
  have hl := hfac u z
  simp only [rawLocalContrast] at hl
  have hr := rawLocalContrast_response_contrast q F i u0 H theta hfac u
  simp only [interactionContrastProfile]
  linear_combination hl - hr

theorem allCoordinatesRaw_implies_allCoordinatesInteractionContrastRankOne
    {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hRaw : AllCoordinatesRawLocalContrastRankOne F) :
    AllCoordinatesInteractionContrastRankOne q F := fun i ↦
  rawLocalContrastRankOne_implies_interactionContrastRankOne q F i
    canonicalInteractionContrastAnchor (hRaw i)

/-! ## The exact gap: centred rank one plus additive alignment -/

theorem rawLocalContrastRankOne_iff_aligned {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U) :
    RawLocalContrastRankOne F i u0 ↔
      ∃ (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ) (kappa : ℝ),
        lambda u0 = 0 ∧
        (∀ u z, interactionContrastProfile q F i u0 u z = lambda u * h z) ∧
        (∀ u, productResponse q F i u - productResponse q F i u0 =
          kappa * lambda u) := by
  constructor
  · rintro ⟨H, theta, hAnchor, hfac⟩
    refine ⟨fun z ↦ H z - productExpectation q H, theta, productExpectation q H,
      hAnchor, ?_, ?_⟩
    · intro u z
      have hl := hfac u z
      simp only [rawLocalContrast] at hl
      have hr := rawLocalContrast_response_contrast q F i u0 H theta hfac u
      simp only [interactionContrastProfile]
      linear_combination hl - hr
    · intro u
      rw [rawLocalContrast_response_contrast q F i u0 H theta hfac u]
      ring
  · rintro ⟨h, lambda, kappa, hAnchor, hprof, halpha⟩
    refine ⟨fun z ↦ h z + kappa, lambda, hAnchor, ?_⟩
    intro u z
    have h1 := hprof u z
    simp only [interactionContrastProfile] at h1
    have h2 := halpha u
    simp only [rawLocalContrast]
    linear_combination h1 + h2

/-! ## The determinant criterion -/

/-- Pairwise vanishing of `2 × 2` determinants of a family of plane vectors
forces a common direction.  Elementary, but it is the step that turns the
pointwise test `mu = 0` into a genuine factorisation. -/
theorem exists_common_direction {U : Type*} (alpha lam : U → ℝ)
    (hdet : ∀ u v, alpha u * lam v - alpha v * lam u = 0) :
    ∃ (a b : ℝ) (t : U → ℝ), (∀ u, alpha u = t u * a) ∧ (∀ u, lam u = t u * b) := by
  classical
  by_cases hA : ∃ u1, alpha u1 ≠ 0
  · obtain ⟨u1, hu1⟩ := hA
    refine ⟨alpha u1, lam u1, fun u ↦ alpha u / alpha u1, ?_, ?_⟩
    · intro u
      field_simp
    · intro u
      have key : lam u * alpha u1 = alpha u * lam u1 := by linarith [hdet u u1]
      rw [div_mul_eq_mul_div, eq_div_iff hu1]
      linarith [key]
  · push_neg at hA
    by_cases hB : ∃ u1, lam u1 ≠ 0
    · obtain ⟨u1, hu1⟩ := hB
      refine ⟨0, lam u1, fun u ↦ lam u / lam u1, ?_, ?_⟩
      · intro u
        simp [hA u]
      · intro u
        field_simp
    · push_neg at hB
      exact ⟨0, 0, fun _ ↦ 0, fun u ↦ by simp [hA u], fun u ↦ by simp [hB u]⟩

/-- Alignment of the first-order layer with the interaction layer, expressed as
the vanishing of the `alpha`/`lambda` determinant, is **sufficient** for raw
rank one.  There is no non-degeneracy hypothesis: when the interaction layer
collapses the raw contrasts are multiples of a constant function. -/
theorem rawLocalContrastRankOne_of_alignment_determinant {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ)
    (hAnchor : lambda u0 = 0)
    (hprof : ∀ u z, interactionContrastProfile q F i u0 u z = lambda u * h z)
    (hdet : ∀ u v,
      (productResponse q F i u - productResponse q F i u0) * lambda v -
        (productResponse q F i v - productResponse q F i u0) * lambda u = 0) :
    RawLocalContrastRankOne F i u0 := by
  obtain ⟨a, b, t, hta, htb⟩ :=
    exists_common_direction
      (fun w ↦ productResponse q F i w - productResponse q F i u0) lambda hdet
  have ha0 : t u0 * a = 0 := by have := hta u0; linarith
  have hb0 : t u0 * b = 0 := by
    have := htb u0
    rw [hAnchor] at this
    linarith
  refine ⟨fun z ↦ b * h z + a, fun u ↦ t u - t u0, by simp, ?_⟩
  intro u z
  have hp := hprof u z
  simp only [interactionContrastProfile] at hp
  have hA := hta u
  have hB := htb u
  simp only [rawLocalContrast]
  linear_combination hp + hA + h z * hB + h z * hb0 + ha0

/-- Necessity, with the non-degeneracy hypothesis made explicit.  If the centred
profile factors through `(lambda, h)` with `h` separating two contexts, then a
nonzero `alpha`/`lambda` determinant refutes raw rank one.  The hypothesis
`h x <> h y` is exactly what the degeneracy remark in the header demands: it is
what pins `lambda` down up to scale.  Without it `lambda` is not determined by
`F` and the determinant carries no information. -/
theorem not_rawLocalContrastRankOne_of_misaligned {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u0 : U)
    (h : (Fin (n + 1) → U) → ℝ) (lambda : U → ℝ)
    (hprof : ∀ w z, interactionContrastProfile q F i u0 w z = lambda w * h z)
    (x y : Fin (n + 1) → U) (hnc : h x ≠ h y)
    (u v : U)
    (hmis :
      (productResponse q F i u - productResponse q F i u0) * lambda v -
        (productResponse q F i v - productResponse q F i u0) * lambda u ≠ 0) :
    ¬ RawLocalContrastRankOne F i u0 := by
  intro hRaw
  obtain ⟨H, theta, _, hfac⟩ := hRaw
  have halpha : ∀ w, productResponse q F i w - productResponse q F i u0 =
      theta w * productExpectation q H := fun w ↦
    rawLocalContrast_response_contrast q F i u0 H theta hfac w
  have hprof' : ∀ w z, interactionContrastProfile q F i u0 w z =
      theta w * (H z - productExpectation q H) := by
    intro w z
    have hl := hfac w z
    simp only [rawLocalContrast] at hl
    have hr := halpha w
    simp only [interactionContrastProfile]
    linear_combination hl - hr
  have key : ∀ w : U, lambda w * (h x - h y) =
      theta w * ((H x - productExpectation q H) -
        (H y - productExpectation q H)) := by
    intro w
    have e1 : lambda w * h x = theta w * (H x - productExpectation q H) := by
      rw [← hprof w x, hprof' w x]
    have e2 : lambda w * h y = theta w * (H y - productExpectation q H) := by
      rw [← hprof w y, hprof' w y]
    linear_combination e1 - e2
  apply hmis
  rw [halpha u, halpha v]
  have hD : h x - h y ≠ 0 := sub_ne_zero.mpr hnc
  have hz : ((theta u * productExpectation q H) * lambda v -
      (theta v * productExpectation q H) * lambda u) * (h x - h y) = 0 := by
    linear_combination (theta u * productExpectation q H) * key v -
      (theta v * productExpectation q H) * key u
  rcases mul_eq_zero.mp hz with h3 | h3
  · exact h3
  · exact absurd h3 hD

/-! ## Interpolation form: raw rank one pins each coordinate slice

The predicate `RawLocalContrastRankOne` is existential in `(H, theta)`.  The
lemmas below remove that existential entirely: once one action `r` is known to
move `F` at one context `zstar`, the value at EVERY action is an explicit affine
combination of the values at the anchor and at `r`, with weights that depend on
the action only.  Nothing downstream has to carry a factorisation witness.

Note that the anchor `u0` and the pair `(r, zstar)` are chosen from `F` itself,
never from the (non-unique) factorisation.
-/

/-- Coordinate `i` moves `F` somewhere.  Stated in terms of `F` alone. -/
def ActiveCoordinate {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 : U) : Prop :=
  ∃ (u : U) (z : Fin (n + 1) → U), rawLocalContrast F i u0 u z ≠ 0

/-- An inactive coordinate is a coordinate `F` does not depend on.  No rank
hypothesis is needed: this is just the definition of inactivity. -/
theorem inactive_coordinate_constant {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 : U)
    (hInactive : ¬ ActiveCoordinate F i u0)
    (u : U) (z : Fin (n + 1) → U) :
    F (Function.update z i u) = F (Function.update z i u0) := by
  unfold ActiveCoordinate at hInactive
  push_neg at hInactive
  have h := hInactive u z
  simp only [rawLocalContrast] at h
  linarith

/-- The normalised action weight.  `rawTheta ... u0 = 0` and, when `r` moves `F`
at `zstar`, `rawTheta ... r = 1`. -/
noncomputable def rawTheta {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 r : U)
    (zstar : Fin (n + 1) → U) (u : U) : ℝ :=
  rawLocalContrast F i u0 u zstar / rawLocalContrast F i u0 r zstar

@[simp] theorem rawTheta_anchor {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 r : U)
    (zstar : Fin (n + 1) → U) :
    rawTheta F i u0 r zstar u0 = 0 := by
  simp [rawTheta]

theorem rawTheta_representative {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 r : U)
    (zstar : Fin (n + 1) → U)
    (hr : rawLocalContrast F i u0 r zstar ≠ 0) :
    rawTheta F i u0 r zstar r = 1 := by
  simp [rawTheta, div_self hr]

/-- Every raw contrast is the same multiple of the representative contrast, with
a coefficient that does not depend on the context. -/
theorem rawLocalContrastRankOne_contrast_interpolation {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 r : U)
    (zstar : Fin (n + 1) → U)
    (hRank : RawLocalContrastRankOne F i u0)
    (hr : rawLocalContrast F i u0 r zstar ≠ 0)
    (u : U) (z : Fin (n + 1) → U) :
    rawLocalContrast F i u0 u z =
      rawTheta F i u0 r zstar u * rawLocalContrast F i u0 r z := by
  have hmin := rawLocalContrastRankOne_minor_zero F i u0 hRank u r z zstar
  rw [rawTheta, div_mul_eq_mul_div, eq_div_iff hr]
  linarith [hmin]

/-- **(star)**  Exact linear interpolation between two slices.

`F (z[i <- u]) = (1 - theta u) * F (z[i <- u0]) + theta u * F (z[i <- r])`

This is the statement that makes the reconstruction argument go through: raw
rank one does not merely bound a rank, it forces each coordinate of `F` to be an
affine interpolation between the anchor slice and one representative slice, with
context-free weights. -/
theorem rawLocalContrastRankOne_interpolation {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 r : U)
    (zstar : Fin (n + 1) → U)
    (hRank : RawLocalContrastRankOne F i u0)
    (hr : rawLocalContrast F i u0 r zstar ≠ 0)
    (u : U) (z : Fin (n + 1) → U) :
    F (Function.update z i u) =
      (1 - rawTheta F i u0 r zstar u) * F (Function.update z i u0) +
        rawTheta F i u0 r zstar u * F (Function.update z i r) := by
  have h := rawLocalContrastRankOne_contrast_interpolation
    F i u0 r zstar hRank hr u z
  simp only [rawLocalContrast] at h
  linear_combination h

/-- The interpolation weights are recovered from `F` at the two slices, so an
active coordinate always supplies a usable `(r, zstar)`. -/
theorem exists_representative_of_active {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u0 : U)
    (hActive : ActiveCoordinate F i u0) :
    ∃ (r : U) (zstar : Fin (n + 1) → U),
      rawLocalContrast F i u0 r zstar ≠ 0 := by
  obtain ⟨u, z, hz⟩ := hActive
  exact ⟨u, z, hz⟩

/-! ## Binary alphabets force raw rank one -/

theorem binary_rawLocalContrastRankOne {n : ℕ}
    (F : (Fin (n + 1) → Fin 2) → ℝ) (i : Fin (n + 1)) :
    RawLocalContrastRankOne F i 0 := by
  let H : (Fin (n + 1) → Fin 2) → ℝ := fun z ↦ rawLocalContrast F i 0 1 z
  let theta : Fin 2 → ℝ := fun u ↦ if u = 1 then 1 else 0
  refine ⟨H, theta, ?_, ?_⟩
  · simp [theta]
  · intro u z
    fin_cases u
    · simp [H, theta]
    · simp [H, theta]

theorem binary_rawLocalContrastRankOne_any_anchor {n : ℕ}
    (F : (Fin (n + 1) → Fin 2) → ℝ) (i : Fin (n + 1)) (a : Fin 2) :
    RawLocalContrastRankOne F i a :=
  rawLocalContrastRankOne_anchor F i 0 a (binary_rawLocalContrastRankOne F i)

theorem binary_allCoordinatesRawLocalContrastRankOne {n : ℕ}
    (F : (Fin (n + 1) → Fin 2) → ℝ) :
    AllCoordinatesRawLocalContrastRankOne F := fun i ↦
  binary_rawLocalContrastRankOne_any_anchor F i canonicalInteractionContrastAnchor

end CIGAMF.P13.D6RawLocalContrastRankOne
