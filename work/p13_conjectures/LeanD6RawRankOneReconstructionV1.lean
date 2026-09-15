import Mathlib
import «LeanD6RawLocalContrastRankOneV1»

/-!
# Corner reconstruction from raw rank one

`rawLocalContrastRankOne_interpolation` (star) says that at one coordinate the
value of `F` at an arbitrary action is an affine interpolation between its value
at the anchor and its value at one representative action, with weights that do
not depend on the context.  Applying it once per coordinate drives every
coordinate to one of two values, so `F` is determined by its values on the
`2^|T|` corners.

The statement proved here is the *partial* one, over an arbitrary
`T : Finset (Fin (n+1))` of already-reduced coordinates.  That is the form the
induction needs; the intended corollary is `T = univ`.

Two deliberate choices:

* the interpolation weight `rawTheta` is built from `F` alone -- no factorisation
  witness `(H, theta)` is carried anywhere, so no uniqueness or gauge lemma is
  ever required;
* the reduction is written so that each step produces `constant + theta * rest`
  directly.  Nothing here builds Bernstein weights and then inverts them, so no
  Moebius inversion is needed.

The hypothesis `hr` says every coordinate of `T` is *active*: some action moves
`F` somewhere.  Inactive coordinates are not covered and must be removed first
with `inactive_coordinate_constant`, which shows `F` does not depend on them.
-/

namespace CIGAMF.P13.D6RawRankOneReconstruction

open scoped BigOperators
open CIGAMF.P13.D6RawLocalContrastRankOne

variable {U : Type*} [Fintype U] [Nonempty U] [DecidableEq U]

/-- The corner point: coordinates in `S` take the representative action, the
other coordinates of `T` take the anchor, everything outside `T` keeps `x`. -/
def cornerPoint {n : ℕ} (r : Fin (n + 1) → U) (u0 : U)
    (T S : Finset (Fin (n + 1))) (x : Fin (n + 1) → U) : Fin (n + 1) → U :=
  fun j => if j ∈ S then r j else if j ∈ T then u0 else x j

/-- The tensor-product interpolation weight attached to a corner. -/
noncomputable def cornerWeight {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))
    (T S : Finset (Fin (n + 1))) (x : Fin (n + 1) → U) : ℝ :=
  (∏ i ∈ S, rawTheta F i u0 (r i) (zs i) (x i)) *
    (∏ i ∈ T \ S, (1 - rawTheta F i u0 (r i) (zs i) (x i)))

section Corners

variable {n : ℕ} (r : Fin (n + 1) → U) (u0 : U)
  {T S : Finset (Fin (n + 1))} {a : Fin (n + 1)} (x : Fin (n + 1) → U)

theorem cornerPoint_empty : cornerPoint r u0 ∅ ∅ x = x := by
  funext j
  simp [cornerPoint]

theorem cornerPoint_apply_of_not_mem (haT : a ∉ T) (haS : a ∉ S) :
    cornerPoint r u0 T S x a = x a := by
  simp [cornerPoint, haT, haS]

theorem cornerPoint_update_anchor (haT : a ∉ T) (haS : a ∉ S) :
    Function.update (cornerPoint r u0 T S x) a u0 =
      cornerPoint r u0 (insert a T) S x := by
  funext j
  by_cases hj : j = a
  · subst hj
    simp [cornerPoint, Function.update_apply, haS]
  · simp [cornerPoint, Function.update_apply, hj, Finset.mem_insert]

theorem cornerPoint_update_representative (haT : a ∉ T) (haS : a ∉ S) :
    Function.update (cornerPoint r u0 T S x) a (r a) =
      cornerPoint r u0 (insert a T) (insert a S) x := by
  funext j
  by_cases hj : j = a
  · subst hj
    simp [cornerPoint, Function.update_apply]
  · simp [cornerPoint, Function.update_apply, hj, Finset.mem_insert]

end Corners

section Weights

variable {n : ℕ} {F : (Fin (n + 1) → U) → ℝ} {u0 : U}
  {r : Fin (n + 1) → U} {zs : Fin (n + 1) → (Fin (n + 1) → U)}
  {T S : Finset (Fin (n + 1))} {a : Fin (n + 1)} {x : Fin (n + 1) → U}

private theorem insert_sdiff_of_not_mem_right (haS : a ∉ S) :
    insert a T \ S = insert a (T \ S) := by
  ext j
  by_cases hj : j = a
  · subst hj
    simp [Finset.mem_sdiff, Finset.mem_insert, haS]
  · simp [Finset.mem_sdiff, Finset.mem_insert, hj]

private theorem insert_sdiff_insert (haT : a ∉ T) :
    insert a T \ insert a S = T \ S := by
  ext j
  by_cases hj : j = a
  · subst hj
    simp [Finset.mem_sdiff, Finset.mem_insert, haT]
  · simp [Finset.mem_sdiff, Finset.mem_insert, hj]

theorem cornerWeight_of_not_mem (haT : a ∉ T) (haS : a ∉ S) :
    cornerWeight F u0 r zs (insert a T) S x =
      (1 - rawTheta F a u0 (r a) (zs a) (x a)) *
        cornerWeight F u0 r zs T S x := by
  unfold cornerWeight
  rw [insert_sdiff_of_not_mem_right haS,
    Finset.prod_insert (fun h => haT (Finset.mem_sdiff.mp h).1)]
  ring

theorem cornerWeight_of_mem (haT : a ∉ T) (haS : a ∉ S) :
    cornerWeight F u0 r zs (insert a T) (insert a S) x =
      rawTheta F a u0 (r a) (zs a) (x a) * cornerWeight F u0 r zs T S x := by
  unfold cornerWeight
  rw [insert_sdiff_insert haT, Finset.prod_insert haS]
  ring

end Weights

/-- One reduction step: (star) applied at a coordinate outside `T`. -/
theorem rawRankOne_split_at {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))
    {T S : Finset (Fin (n + 1))} {a : Fin (n + 1)} (x : Fin (n + 1) → U)
    (hRank : RawLocalContrastRankOne F a u0)
    (hra : rawLocalContrast F a u0 (r a) (zs a) ≠ 0)
    (haT : a ∉ T) (haS : a ∉ S) :
    F (cornerPoint r u0 T S x) =
      (1 - rawTheta F a u0 (r a) (zs a) (x a)) *
          F (cornerPoint r u0 (insert a T) S x) +
        rawTheta F a u0 (r a) (zs a) (x a) *
          F (cornerPoint r u0 (insert a T) (insert a S) x) := by
  have hval : cornerPoint r u0 T S x a = x a :=
    cornerPoint_apply_of_not_mem r u0 x haT haS
  have hself :
      Function.update (cornerPoint r u0 T S x) a (x a) = cornerPoint r u0 T S x := by
    rw [← hval]
    exact Function.update_eq_self a _
  have h := rawLocalContrastRankOne_interpolation F a u0 (r a) (zs a) hRank hra
    (x a) (cornerPoint r u0 T S x)
  rw [hself, cornerPoint_update_anchor r u0 x haT haS,
    cornerPoint_update_representative r u0 x haT haS] at h
  exact h

/-- **Partial corner reconstruction.**  Every coordinate of `T` has been driven
to the anchor or to its representative, and `F x` is the tensor-product
interpolation of the resulting corner values. -/
theorem rawRankOne_partial_reconstruction {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))
    (hRank : ∀ i, RawLocalContrastRankOne F i u0)
    (x : Fin (n + 1) → U) (T : Finset (Fin (n + 1))) :
    (∀ i ∈ T, rawLocalContrast F i u0 (r i) (zs i) ≠ 0) →
      F x = ∑ S ∈ T.powerset,
        cornerWeight F u0 r zs T S x * F (cornerPoint r u0 T S x) := by
  induction T using Finset.induction_on with
  | empty =>
      intro _
      simp [cornerWeight, cornerPoint_empty]
  | @insert a s ha ih =>
      intro hr
      rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib,
        ih (fun i hi => hr i (Finset.mem_insert_of_mem hi))]
      refine Finset.sum_congr rfl ?_
      intro S hS
      have hSs : S ⊆ s := Finset.mem_powerset.mp hS
      have haS : a ∉ S := fun h => ha (hSs h)
      have hra : rawLocalContrast F a u0 (r a) (zs a) ≠ 0 :=
        hr a (Finset.mem_insert_self a s)
      rw [cornerWeight_of_not_mem ha haS, cornerWeight_of_mem ha haS,
        rawRankOne_split_at F u0 r zs x (hRank a) hra ha haS]
      ring

/-- The intended corollary: with every coordinate active, `F` is determined by
its `2^(n+1)` corner values. -/
theorem rawRankOne_corner_reconstruction {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))
    (hRank : ∀ i, RawLocalContrastRankOne F i u0)
    (hr : ∀ i, rawLocalContrast F i u0 (r i) (zs i) ≠ 0)
    (x : Fin (n + 1) → U) :
    F x = ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
      cornerWeight F u0 r zs Finset.univ S x *
        F (cornerPoint r u0 Finset.univ S x) :=
  rawRankOne_partial_reconstruction F u0 r zs hRank x Finset.univ
    (fun i _ => hr i)

end CIGAMF.P13.D6RawRankOneReconstruction
