import Mathlib
import «LeanProductMixedDifferenceV4»
import «LeanD6ResidualCentering»
import «LeanD6ResidualOrthogonality»
import «LeanD6CycleDual»

/-!
# Packaged residual API for the PAEC programme

This file only packages the already proved product-centering facts.  It does
not use the killed free-response relaxation: every identity is derived from a
single product reference `q` and its row normalizations.
-/

namespace CIGAMF.P13.D6ResidualAPI

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6ResidualCentering
open CIGAMF.P13.D6ResidualOrthogonality

variable {U : Type*} [Fintype U] [Nonempty U]

theorem residual_core {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1) :
    productExpectation q (productResidual q F) = 0 ∧
      (∀ i u, productResponse q (productResidual q F) i u = 0) ∧
      (∀ i x c,
        mixedDifference (productResidual q F) i x c =
          mixedDifference F i x c) := by
  refine ⟨R0_productResidual_expectation_zero q hRow F, ?_, ?_⟩
  · intro i u
    exact R1_productResidual_response_zero q hRow F i u
  · intro i x c
    exact R2_mixedDifference_residual q F i x c

theorem residual_loss_api {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1))) :
    productCompressionLoss F (productResponse q F) selected =
      osc (fun x ↦ productResidual q F x +
        selectedᶜ.sum (fun j ↦ productResponse q F j (x j))) / 2 := by
  exact R3_residual_loss_rewrite q F selected

end CIGAMF.P13.D6ResidualAPI
