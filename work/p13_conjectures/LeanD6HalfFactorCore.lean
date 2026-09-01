import Mathlib
import «LeanProductMixedDifferenceV4»

/-!
# D6 half-factor proof decomposition

This extension leaves the zero-sorry P12 baseline immutable.  It isolates the
only genuinely new inequality needed by the P13 half-factor target: a direct
comparison of the two *shared* transfer errors.  In particular, it does not
apply the two independent uniform-world perturbation bounds from D4.
-/

namespace CIGAMF.P13.D6HalfFactorCore

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

variable {U : Type*} [Fintype U] [Nonempty U]

noncomputable def transferErr {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S : Finset (Fin (n + 1))) : ℝ :=
  productCompressionLoss F (productResponse q F) S -
    productCompressionLoss (productA q F) (productResponse q F) S

theorem D6H1_true_loss_diff_eq_surrogate_diff_add_transfer {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (S T : Finset (Fin (n + 1))) :
    productCompressionLoss F (productResponse q F) S -
        productCompressionLoss F (productResponse q F) T =
      (productCompressionLoss (productA q F) (productResponse q F) S -
        productCompressionLoss (productA q F) (productResponse q F) T) +
      (transferErr q F S - transferErr q F T) := by
  simp only [transferErr]
  ring

theorem D6H2_surrogate_selected_le_competitor {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected T : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hT : T.card = k) :
    productCompressionLoss (productA q F) (productResponse q F) selected ≤
      productCompressionLoss (productA q F) (productResponse q F) T := by
  exact productA_topC_surrogate_optimal q F selected k hTop T hT

/- The final minimizer step is completely independent of the hard analytic
lemma.  Keeping it explicit prevents a future proof from hiding the desired
pair-transfer inequality inside an external `hSurrogateOptimal` premise. -/
theorem D6H4_half_factor_from_direct_pair_transfer {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore
      (fun j ↦ osc (productResponse q F j)) selected k)
    (hPairTransfer : ∀ T : Finset (Fin (n + 1)), T.card = k →
      transferErr q F selected - transferErr q F T ≤
        (n : ℝ) * delta / 2) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          (n : ℝ) * delta / 2 := by
  have hne :
      (CIGAMF.V4.ProductMixedDifference.cardinalityFamily
        (R := Fin (n + 1)) k).Nonempty :=
    ⟨selected, by
      simp [CIGAMF.V4.ProductMixedDifference.cardinalityFamily, hTop.1]⟩
  rcases finiteObjectiveMin_attained
      (fun S : Finset (Fin (n + 1)) ↦
        productCompressionLoss F (productResponse q F) S) k hne with
    ⟨optimal, hOptimalCard, hOptimalValue⟩
  have hA := D6H2_surrogate_selected_le_competitor q F selected optimal k
    hTop hOptimalCard
  have hE := hPairTransfer optimal hOptimalCard
  have hId := D6H1_true_loss_diff_eq_surrogate_diff_add_transfer q F
    selected optimal
  rw [← hOptimalValue]
  linarith

end CIGAMF.P13.D6HalfFactorCore
