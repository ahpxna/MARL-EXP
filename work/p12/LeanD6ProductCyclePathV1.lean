import Mathlib
import «LeanD6H3Exchange»
import «LeanD6CycleDual»

/-!
# Product-reference residual steps are finite PAEC-atom averages

This is the mechanical product-reference bridge needed before any balanced
two-path splice can be attempted.  A single selected-coordinate residual
update is exactly a product-weighted finite sum of actual D6 cycle atoms.
It uses only `hNorm`, not the stronger row-normalization premise from the
older residual API.
-/

namespace CIGAMF.P13.D6ProductCyclePath

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6CycleDual

variable {U : Type*} [Fintype U] [Nonempty U]

theorem retainedResidual_step_eq_cycle_average {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ selected)
    (z : Fin (n + 1) → U) (u : U)
    (hNorm : ∑ c, jointWeight q c = 1) :
    retainedResidual q F selected (Function.update z i u) -
        retainedResidual q F selected z =
      productExpectation q (fun c ↦
        cycleFunctional i (Function.update z i u)
          (Function.update c i (z i)) F) := by
  have hsum :
      selected.sum (fun j ↦ productResponse q F j
          ((Function.update z i u) j)) -
        selected.sum (fun j ↦ productResponse q F j (z j)) =
      productResponse q F i u - productResponse q F i (z i) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Function.update, hji]
    · intro hnot
      exact (hnot hi).elim
  unfold retainedResidual
  rw [show
      (F (Function.update z i u) -
        selected.sum (fun j ↦ productResponse q F j
          ((Function.update z i u) j))) -
        (F z - selected.sum (fun j ↦ productResponse q F j (z j))) =
      (F (Function.update z i u) - F z) -
        (selected.sum (fun j ↦ productResponse q F j
          ((Function.update z i u) j)) -
          selected.sum (fun j ↦ productResponse q F j (z j))) by ring,
      hsum]
  change F (Function.update z i u) - F z -
      (productResponse q F i u - productResponse q F i (z i)) =
    productExpectation q (fun c ↦
      mixedDifference F i (Function.update z i u)
        (Function.update c i (z i)))
  simpa only [Function.update_eq_self] using
    (coordinate_contrast_error_eq_expectation_mixed q F hNorm i u (z i) z)

theorem retainedResidual_step_eq_finite_cycle_sum {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ selected)
    (z : Fin (n + 1) → U) (u : U)
    (hNorm : ∑ c, jointWeight q c = 1) :
    retainedResidual q F selected (Function.update z i u) -
        retainedResidual q F selected z =
      ∑ c, jointWeight q c *
        cycleFunctional i (Function.update z i u)
          (Function.update c i (z i)) F := by
  rw [retainedResidual_step_eq_cycle_average q F selected i hi z u hNorm]
  rfl

theorem selected_residual_step_cycle_mass_one {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1) :
    ∑ c, |jointWeight q c| = 1 := by
  rw [Finset.sum_congr rfl (fun c hc ↦ abs_of_nonneg (hWeight c)), hNorm]

end CIGAMF.P13.D6ProductCyclePath
