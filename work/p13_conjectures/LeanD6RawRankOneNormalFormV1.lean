import Mathlib
import «LeanD6RawRankOneMultiaffineV1»

/-!
# `RawRankOne ⟹ F = P(theta)` with `P` multiaffine

`rawRankOne_mem_monomialSpan` says `F` lies in the span of the subset monomials.
Over a finite index type, span membership is the same as an explicit coefficient
family, so this file extracts it and states the normal form

  `F x = ∑ S, c S * ∏ i ∈ S, theta i (x i)`,

which is the boxed conclusion of the interpolation route: raw local contrast
rank one at every coordinate forces `F` to be multiaffine in its own normalised
action coefficients.  Splitting off `S = ∅` gives the `P(phi) + const` shape, and
the `|S| = 1` terms are the additive layer -- which is now *forced* to be affine
in `theta i`, exactly the raw-fibre constraint whose dimension
`1 + m + (2^m - 1 - m) = 2^m` was measured exactly in `E1_rawfiber_m6_K3.json`.

### What is still assumed

`hr` requires every coordinate to be ACTIVE.  A world with an inactive
coordinate is not covered: `rawTheta` is then built from a division by zero and
carries no information.  Removing that hypothesis needs a canonical choice of
representative (`Classical.choose` on `ActiveCoordinate`) together with the
convention `theta i ≡ 0` on inactive coordinates, at which point the
interpolation identity holds unconditionally -- on an inactive coordinate it
degenerates to `inactive_coordinate_constant`.  That generalisation is NOT done
here and the theorems below must not be quoted as if it were.
-/

namespace CIGAMF.P13.D6RawRankOneNormalForm

open scoped BigOperators
open CIGAMF.P13.D6RawLocalContrastRankOne
open CIGAMF.P13.D6RawRankOneReconstruction
open CIGAMF.P13.D6RawRankOneMultiaffine

variable {U : Type*} [Fintype U] [Nonempty U] [DecidableEq U]

/-- **Multiaffine normal form.**  Under raw rank one at every coordinate, with
every coordinate active, `F` is a multiaffine polynomial in the normalised
action coefficients `rawTheta`, with coefficients indexed by subsets. -/
theorem rawRankOne_exists_multiaffine_coefficients {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))
    (hRank : ∀ i, RawLocalContrastRankOne F i u0)
    (hr : ∀ i, rawLocalContrast F i u0 (r i) (zs i) ≠ 0) :
    ∃ c : Finset (Fin (n + 1)) → ℝ,
      ∀ x, F x = ∑ S : Finset (Fin (n + 1)),
        c S * ∏ i ∈ S, rawTheta F i u0 (r i) (zs i) (x i) := by
  classical
  have hmem := rawRankOne_mem_monomialSpan F u0 r zs hRank hr
  rw [monomialSet] at hmem
  -- `Submodule.mem_span_range_iff_exists_fun` takes the ring explicitly and
  -- needs `Fintype` on the index, which here is `Finset (Fin (n+1))`.
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨c, fun x => ?_⟩
  have hx := congrFun hc x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
  exact hx.symm

/-- The same statement split into a constant and a purely interacting part, i.e.
`F = P(theta) + const` with `P` having no constant term. -/
theorem rawRankOne_normal_form_const_plus_interaction {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (u0 : U)
    (r : Fin (n + 1) → U) (zs : Fin (n + 1) → (Fin (n + 1) → U))
    (hRank : ∀ i, RawLocalContrastRankOne F i u0)
    (hr : ∀ i, rawLocalContrast F i u0 (r i) (zs i) ≠ 0) :
    ∃ (b : ℝ) (c : Finset (Fin (n + 1)) → ℝ),
      c ∅ = 0 ∧
      ∀ x, F x = b + ∑ S : Finset (Fin (n + 1)),
        c S * ∏ i ∈ S, rawTheta F i u0 (r i) (zs i) (x i) := by
  classical
  obtain ⟨c, hc⟩ := rawRankOne_exists_multiaffine_coefficients F u0 r zs hRank hr
  refine ⟨c ∅, fun S => if S = ∅ then 0 else c S, by simp, fun x => ?_⟩
  rw [hc x]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset (Fin (n + 1))))]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset (Fin (n + 1))))]
  have hzero : ∀ S ∈ (Finset.univ : Finset (Finset (Fin (n + 1)))).erase ∅,
      (if S = ∅ then (0 : ℝ) else c S) *
          ∏ i ∈ S, rawTheta F i u0 (r i) (zs i) (x i)
        = c S * ∏ i ∈ S, rawTheta F i u0 (r i) (zs i) (x i) := by
    intro S hS
    rw [if_neg (Finset.ne_of_mem_erase hS)]
  rw [Finset.sum_congr rfl hzero]
  simp

end CIGAMF.P13.D6RawRankOneNormalForm
