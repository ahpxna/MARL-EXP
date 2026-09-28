import Mathlib
import «LeanProductMixedDifferenceV4»

/-!
# D6 residual centering identities

This P13 module keeps the P12 baseline immutable.  It starts from the literal
product-reference reconstruction `productA` and its residual `F - productA`.
-/

namespace CIGAMF.P13.D6ResidualCentering

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def productResidual {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (x : Fin (n + 1) → U) : ℝ :=
  F x - productA q F x

theorem mixedDifference_sum_coordinates_zero {n : ℕ}
    (g : Fin (n + 1) → U → ℝ) (c0 : ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    mixedDifference (fun a ↦ (∑ j, g j (a j)) + c0) i x c = 0 := by
  classical
  unfold mixedDifference
  have hterm : ∀ j : Fin (n + 1),
      g j (x j) - g j ((Function.update x i (c i)) j) -
          g j ((Function.update c i (x i)) j) + g j (c j) = 0 := by
    intro j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update, hji]
  rw [show
      ((∑ j, g j (x j)) + c0) -
          ((∑ j, g j ((Function.update x i (c i)) j)) + c0) -
          ((∑ j, g j ((Function.update c i (x i)) j)) + c0) +
          ((∑ j, g j (c j)) + c0) =
        ∑ j, (g j (x j) - g j ((Function.update x i (c i)) j) -
          g j ((Function.update c i (x i)) j) + g j (c j)) by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib]
      ring]
  exact Finset.sum_eq_zero (fun j _ ↦ hterm j)

theorem productA_mixedDifference_zero {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    mixedDifference (productA q F) i x c = 0 := by
  unfold productA surrogate
  simpa [sub_eq_add_neg] using
    (mixedDifference_sum_coordinates_zero
      (productResponse q F)
      (-(((Fintype.card (Fin (n + 1)) : ℝ) - 1) * productB q F)) i x c)

theorem R2_mixedDifference_residual {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (x c : Fin (n + 1) → U) :
    mixedDifference (productResidual q F) i x c = mixedDifference F i x c := by
  rw [show productResidual q F = fun a ↦ F a - productA q F a by
    funext a; rfl]
  unfold mixedDifference
  have hzero := productA_mixedDifference_zero q F i x c
  unfold mixedDifference at hzero
  linarith

theorem residual_retained_decomposition {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1)))
    (x : Fin (n + 1) → U) :
    F x - selected.sum (fun j ↦ productResponse q F j (x j)) =
      productResidual q F x +
        selectedᶜ.sum (fun j ↦ productResponse q F j (x j)) -
          ((Fintype.card (Fin (n + 1)) : ℝ) - 1) * productB q F := by
  classical
  have hsum := Finset.sum_add_sum_compl selected
    (fun j ↦ productResponse q F j (x j))
  unfold productResidual productA surrogate
  linarith

theorem R3_residual_loss_rewrite {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1))) :
    productCompressionLoss F (productResponse q F) selected =
      osc (fun x ↦ productResidual q F x +
        selectedᶜ.sum (fun j ↦ productResponse q F j (x j))) / 2 := by
  let core : (Fin (n + 1) → U) → ℝ := fun x ↦
    productResidual q F x +
      selectedᶜ.sum (fun j ↦ productResponse q F j (x j))
  let shift : ℝ := -(((Fintype.card (Fin (n + 1)) : ℝ) - 1) * productB q F)
  have hfun :
      (fun x ↦ F x - selected.sum
        (fun j ↦ productResponse q F j (x j))) =
      (fun x ↦ core x + shift) := by
    funext x
    rw [residual_retained_decomposition q F selected x]
    rfl
  unfold productCompressionLoss
  rw [hfun, osc_add_const]

end CIGAMF.P13.D6ResidualCentering
