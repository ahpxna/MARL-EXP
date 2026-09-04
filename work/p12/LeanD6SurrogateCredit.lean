import Mathlib
import «LeanD6HalfFactorCore»

/-!
# D6 surrogate-gap credit

The failed BEX route tried to pay the entire half-factor from transfer error.
This module records the exact decomposition in which Top-C surrogate
optimality contributes a nonnegative credit.  It does not assume or prove the
still-open analytic transfer bound.
-/

namespace CIGAMF.P13.D6SurrogateCredit

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
open CIGAMF.P13.D6HalfFactorCore

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def surrogateGap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1))) : ℝ :=
  productCompressionLoss (productA q F) (productResponse q F) T -
    productCompressionLoss (productA q F) (productResponse q F) S

theorem true_loss_diff_eq_transfer_sub_surrogateGap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1))) :
    productCompressionLoss F (productResponse q F) S -
        productCompressionLoss F (productResponse q F) T =
      transferErr q F S - transferErr q F T - surrogateGap q F S T := by
  rw [D6H1_true_loss_diff_eq_surrogate_diff_add_transfer]
  simp only [surrogateGap]
  ring

theorem surrogateGap_formula {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1))) :
    surrogateGap q F S T =
      (Tᶜ.sum (fun j ↦ osc (productResponse q F j)) -
        Sᶜ.sum (fun j ↦ osc (productResponse q F j))) / 2 := by
  simp only [surrogateGap, productA_compression_loss_formula]
  ring

theorem surrogateGap_complement_formula {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1)))
    (hComplement : T = Sᶜ) :
    surrogateGap q F S T =
      (S.sum (fun j ↦ osc (productResponse q F j)) -
        T.sum (fun j ↦ osc (productResponse q F j))) / 2 := by
  rw [surrogateGap_formula, hComplement]
  simp

theorem surrogateGap_nonnegative_of_topC {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected T : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hT : T.card = k) :
    0 ≤ surrogateGap q F selected T := by
  unfold surrogateGap
  exact sub_nonneg.mpr
    (D6H2_surrogate_selected_le_competitor q F selected T k hTop hT)

theorem true_loss_diff_le_of_transfer_bound_and_credit {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1))) (transferBudget credit : ℝ)
    (hTransfer : transferErr q F S - transferErr q F T ≤ transferBudget)
    (hCredit : credit ≤ surrogateGap q F S T) :
    productCompressionLoss F (productResponse q F) S -
        productCompressionLoss F (productResponse q F) T ≤
      transferBudget - credit := by
  rw [true_loss_diff_eq_transfer_sub_surrogateGap]
  linarith

end CIGAMF.P13.D6SurrogateCredit
