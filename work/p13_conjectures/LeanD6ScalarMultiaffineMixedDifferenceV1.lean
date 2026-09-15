import Mathlib
import «LeanD6ScalarMultiaffineRankOneV1»

/-!
# Mixed differences of a scalar multiaffine world factor exactly

For a world in scalar multiaffine normal form the D6 mixed difference is a
PRODUCT of an action factor and a context factor:

  `mixedDifference F i x c = (phi i (x i) - phi i (c i)) * (H_i x - H_i c)`

This is the reduction that makes the interaction bound cheap.  Bounding
`|mixedDifference|` over all `(i, x, c)` naively is `6 * 729 * 729` instances;
after this lemma it is `|phi i (x i) - phi i (c i)| <= 1` -- immediate when
`phi` is two-valued -- times the oscillation of a single coordinate cofactor.

Nothing here assumes anything about the reference `q`: the mixed difference is
a property of `F` alone.  No decision or half-factor bound is claimed.
-/

namespace CIGAMF.P13.D6ScalarMultiaffineMixedDifference

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ScalarMultiaffineRankOne

variable {U : Type*} [Fintype U] [Nonempty U]

/-- The exact factorization. -/
theorem scalarMultiaffineWorld_mixedDifference {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    mixedDifference (scalarMultiaffineWorld g b phi W) i x c =
      (phi i (x i) - phi i (c i)) *
        (multiaffineContextFactor phi W i x - multiaffineContextFactor phi W i c) := by
  classical
  have hx := scalarMultiaffineWorld_slice_contrast g b phi W i (x i) (c i) x
  have hc := scalarMultiaffineWorld_slice_contrast g b phi W i (x i) (c i) c
  rw [Function.update_eq_self i x] at hx
  rw [Function.update_eq_self i c] at hc
  unfold mixedDifference
  linarith [hx, hc]

/-- With a two-valued `phi` the action factor is bounded by one, so the whole
mixed difference is bounded by the oscillation of the coordinate cofactor. -/
theorem scalarMultiaffineWorld_mixedDifference_abs_le {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (b : ℝ)
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U)
    (width : ℝ)
    (hphi : |phi i (x i) - phi i (c i)| ≤ 1)
    (hH : |multiaffineContextFactor phi W i x -
      multiaffineContextFactor phi W i c| ≤ width)
    (hwidth : 0 ≤ width) :
    |mixedDifference (scalarMultiaffineWorld g b phi W) i x c| ≤ width := by
  rw [scalarMultiaffineWorld_mixedDifference g b phi W i x c, abs_mul]
  calc |phi i (x i) - phi i (c i)| *
        |multiaffineContextFactor phi W i x - multiaffineContextFactor phi W i c|
      ≤ 1 * width := by
        refine mul_le_mul hphi hH (abs_nonneg _) zero_le_one
    _ = width := one_mul width

/-- A two-sided bound on the cofactor gives the oscillation bound the previous
lemma needs.  Stating it this way means the finite work downstream is a bound on
ONE function of the context, not a bound on a difference of two. -/
theorem contextFactor_abs_sub_le {n : ℕ}
    (phi : Fin (n + 1) → U → ℝ)
    (W : Finset (Fin (n + 1)) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) (lo hi : ℝ)
    (hlo : ∀ z, lo ≤ multiaffineContextFactor phi W i z)
    (hhi : ∀ z, multiaffineContextFactor phi W i z ≤ hi) :
    |multiaffineContextFactor phi W i x -
      multiaffineContextFactor phi W i c| ≤ hi - lo := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [hhi x, hlo c]
  · linarith [hhi c, hlo x]

end CIGAMF.P13.D6ScalarMultiaffineMixedDifference
