import Mathlib
import «LeanProductMixedDifferenceV4»

/-! QUARANTINED / OPEN. Not part of the active build. -/
namespace CIGAMF.P13.D6HalfFactor

open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

variable {U : Type*} [Fintype U] [Nonempty U]

/-- High-upside conjecture suggested by exact/random/adversarial search.
    This improves the active decision-transfer additive term from
    `2 * n * delta` to `n * delta / 2`. -/
theorem D6_product_topC_decision_half_factor_conjecture {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1))) (k : ℕ)
    (hTop : IsTopKByScore (fun j ↦ osc (productResponse q F j)) selected k) :
    productCompressionLoss F (productResponse q F) selected ≤
      finiteObjectiveMin (fun S ↦
        productCompressionLoss F (productResponse q F) S) k +
          (n : ℝ) * delta / 2 := by
  sorry

end CIGAMF.P13.D6HalfFactor
