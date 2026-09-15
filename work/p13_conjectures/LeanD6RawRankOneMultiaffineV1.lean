import Mathlib
import «LeanD6RawRankOneReconstructionV1»

/-!
# Raw rank one puts `F` in the multiaffine span of the action coefficients

`rawRankOne_corner_reconstruction` writes `F` as a combination of the `2^(n+1)`
tensor-product (Bernstein) weights attached to the corners.  This file converts
that to membership in the span of the **subset monomials**
`x ↦ ∏ i ∈ S, theta i (x i)`, which is the statement that matters:

  the raw-rank-one worlds with a given action coefficient `theta` are exactly the
  span of the `2^(n+1)` subset monomials in `theta`,

so the fibre searched by the raw-fibre falsification driver is the whole raw
variety at that `theta`, not a slice of it.  Numerically this is the dimension
`1 + m + (2^m - 1 - m) = 2^m` measured exactly in `E1_rawfiber_m6_K3.json`
(64, against 70 for the centred fibre).

The conversion deliberately avoids Moebius inversion and the explicit
inclusion-exclusion coefficient formula.  Working with `Submodule.span`
membership instead of explicit coefficients means the Bernstein-to-monomial step
is a two-term recursion

  `(∏_S theta) * ∏_{insert a A} (1 - theta) =
     (∏_S theta) * ∏_A (1 - theta)  -  (∏_{insert a S} theta) * ∏_A (1 - theta)`

closed under `Submodule.sub_mem`, with no signs, no binomial coefficients and no
incidence algebra.
-/

namespace CIGAMF.P13.D6RawRankOneMultiaffine

open scoped BigOperators
open CIGAMF.P13.D6RawLocalContrastRankOne
open CIGAMF.P13.D6RawRankOneReconstruction

variable {U : Type*} [Fintype U] [Nonempty U] [DecidableEq U]

/-- The subset monomials in a family of scalar action coefficients. -/
def monomialSet {n : ℕ} (t : Fin (n + 1) → U → ℝ) :
    Set ((Fin (n + 1) → U) → ℝ) :=
  Set.range fun S : Finset (Fin (n + 1)) => fun x => ∏ i ∈ S, t i (x i)

/-- A Bernstein weight lies in the span of the subset monomials.  Induction on
the complement block `A`, splitting off one factor `1 - t a` at a time. -/
theorem bernstein_mem_monomialSpan {n : ℕ}
    (t : Fin (n + 1) → U → ℝ) (A : Finset (Fin (n + 1))) :
    ∀ S : Finset (Fin (n + 1)), Disjoint A S →
      (fun (x : Fin (n + 1) → U) =>
        (∏ i ∈ S, t i (x i)) * ∏ i ∈ A, (1 - t i (x i))) ∈
        Submodule.span ℝ (monomialSet t) := by
  induction A using Finset.induction_on with
  | empty =>
      intro S _
      have : (fun (x : Fin (n + 1) → U) =>
          (∏ i ∈ S, t i (x i)) * ∏ i ∈ (∅ : Finset (Fin (n + 1))),
                (1 - t i (x i)))
          = fun (x : Fin (n + 1) → U) => ∏ i ∈ S, t i (x i) := by
        funext x
        simp
      rw [this]
      exact Submodule.subset_span ⟨S, rfl⟩
  | @insert a A' ha ih =>
      intro S hdisj
      have haS : a ∉ S := (Finset.disjoint_insert_left.mp hdisj).1
      have hA'S : Disjoint A' S := (Finset.disjoint_insert_left.mp hdisj).2
      have hA'aS : Disjoint A' (insert a S) :=
        Finset.disjoint_insert_right.mpr ⟨ha, hA'S⟩
      have key :
          (fun (x : Fin (n + 1) → U) => (∏ i ∈ S, t i (x i)) *
              ∏ i ∈ insert a A', (1 - t i (x i)))
            = (fun (x : Fin (n + 1) → U) =>
                (∏ i ∈ S, t i (x i)) * ∏ i ∈ A', (1 - t i (x i)))
              - (fun (x : Fin (n + 1) → U) => (∏ i ∈ insert a S, t i (x i)) *
                  ∏ i ∈ A', (1 - t i (x i))) := by
        funext x
        simp only [Pi.sub_apply, Finset.prod_insert ha, Finset.prod_insert haS]
        ring
      rw [key]
      exact Submodule.sub_mem _ (ih S hA'S) (ih (insert a S) hA'aS)

section Reconstruction

variable {n : ℕ} (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
  (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))

/-- With every coordinate reduced, the corner no longer depends on `x`: the
`2^(n+1)` corners are fixed points of the action space. -/
theorem cornerPoint_univ (S : Finset (Fin (n + 1))) (x : Fin (n + 1) → U) :
    cornerPoint r u0 Finset.univ S x = fun j => if j ∈ S then r j else u0 := by
  funext j
  simp [cornerPoint]

/-- `F` is the Bernstein combination of its corner values. -/
theorem rawRankOne_eq_bernstein_combination
    (hRank : ∀ i, RawLocalContrastRankOne F i u0)
    (hr : ∀ i, rawLocalContrast F i u0 (r i) (zs i) ≠ 0) :
    F = ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
      (F fun j => if j ∈ S then r j else u0) •
        fun x => cornerWeight F u0 r zs Finset.univ S x := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [rawRankOne_corner_reconstruction F u0 r zs hRank hr x]
  refine Finset.sum_congr rfl ?_
  intro S _
  rw [cornerPoint_univ (r := r) (u0 := u0) S x]
  ring

/-- **Raw rank one puts `F` in the multiaffine span.**

Every world satisfying raw local contrast rank one at every coordinate, with
every coordinate active, lies in the span of the `2^(n+1)` subset monomials in
its own normalised action coefficients `rawTheta`.  Since `rawTheta` is built
from `F` alone, no factorisation witness appears in the statement. -/
theorem rawRankOne_mem_monomialSpan
    (hRank : ∀ i, RawLocalContrastRankOne F i u0)
    (hr : ∀ i, rawLocalContrast F i u0 (r i) (zs i) ≠ 0) :
    F ∈ Submodule.span ℝ
      (monomialSet fun i u => rawTheta F i u0 (r i) (zs i) u) := by
  let t : Fin (n + 1) → U → ℝ :=
    fun i u => rawTheta F i u0 (r i) (zs i) u
  change F ∈ Submodule.span ℝ (monomialSet t)
  have hcomb := rawRankOne_eq_bernstein_combination F u0 r zs hRank hr
  have hmem :
      (∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset,
        (F fun j => if j ∈ S then r j else u0) •
          fun x => cornerWeight F u0 r zs Finset.univ S x) ∈
        Submodule.span ℝ (monomialSet t) := by
    refine Submodule.sum_mem _ ?_
    intro S _
    refine Submodule.smul_mem _ _ ?_
    have hrewrite :
        (fun x => cornerWeight F u0 r zs Finset.univ S x)
          = fun x => (∏ i ∈ S, t i (x i)) *
              ∏ i ∈ Finset.univ \ S, (1 - t i (x i)) := by
      funext x
      simp only [t]
      rfl
    rw [hrewrite]
    exact bernstein_mem_monomialSpan t (Finset.univ \ S) S Finset.sdiff_disjoint
  rw [hcomb]
  exact hmem

end Reconstruction

end CIGAMF.P13.D6RawRankOneMultiaffine
