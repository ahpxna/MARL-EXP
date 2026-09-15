import «LeanD6SharpMarginSteeringV1»
import «LeanD6MarginSensitiveExchangeV1»

/-! Universal sufficiency of margin >= 2 delta for product-response compression,
and a dimension-parametric matching witness at every margin 1 <= rho < 2.
Sufficiency permits degenerate product references. Necessity uses corner.
This is a Top-C optimality threshold, not a theorem about the entire same-Q
fibre's minimax value. These are different quantifiers. -/
namespace CIGAMF.P13.D6SharpMarginThreshold
open scoped BigOperators
open Finset
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry CIGAMF.P13.D6Threshold
open CIGAMF.P13.D6SharpMarginSteering CIGAMF.P13.D6MarginSensitiveExchange
noncomputable section

/-- Every same-cardinality competitor has at least the Top-C loss. -/
theorem margin_two_sufficient {U : Type*} [Fintype U] [Nonempty U] {n : ℕ}
    (q : I n → U → ℝ) (F : (I n → U) → ℝ) (delta rho : ℝ)
    (hWeight : ∀ c,0 ≤ jointWeight q c) (hNorm : ∑ c,jointWeight q c=1)
    (hd : 0 ≤ delta) (hdelta : ∀ i x c,|mixedDifference F i x c| ≤ delta)
    (T : Finset (I n)) (k : ℕ)
    (htop : IsTopKByScore (fun i => osc (productResponse q F i)) T k)
    (hmargin : ∀ i ∈ T,∀ j ∉ T,rho+osc (productResponse q F j) ≤ osc (productResponse q F i))
    (hrho : 2*delta ≤ rho) (S : Finset (I n)) (hS : S.card=k) :
    productCompressionLoss F (productResponse q F) T ≤ productCompressionLoss F (productResponse q F) S := by
  have h := pair_doubled_loss_le_card_mul_two_delta_sub_margin q F delta rho
    hWeight hNorm hd hdelta T S k htop hS hmargin
  have hn : ((T \ S).card:ℝ)*(2*delta-rho) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  linarith

/-- The steering construction exactly attains the exchange bound against the
complement. It is not an enumeration or an abstract regret-table witness. -/
theorem steered_exchange_equality {n : ℕ} (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (rho : ℝ) (hr : 1 ≤ rho) (hbal : Aᶜ.card=A.card) (hB : 2 ≤ (others A j).card) :
    2*(productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) A-
      productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) Aᶜ)=
      (A.card:ℝ)*(2-rho) := by
  have htop := steered_is_top A j hj rho (by linarith)
  have hm : ∀ i ∈ A,∀ l ∉ A,rho+osc (productResponse corner (steered A j rho) l) ≤
      osc (productResponse corner (steered A j rho) i) := by
    intro i hi l hl
    rw [steered_span A j hj rho (by linarith) i,steered_span A j hj rho (by linarith) l]
    simp [hi,hl]
  have hu := pair_doubled_loss_le_card_mul_two_delta_sub_margin corner (steered A j rho) 1 rho
    corner_nonnegative corner_normalized (by norm_num) (steered_mixed_bound A j · rho)
    A Aᶜ A.card htop hbal hm
  have he : A \ Aᶜ=A := by ext i; simp
  rw [he] at hu
  have hl := sharp_margin_witness A j hj rho hr hbal hB
  linarith

/-- A nonzero A supplies strict failure for every rho below two. -/
theorem every_subthreshold_margin_fails {n : ℕ} (A : Finset (I n)) (j : I n) (hj : j ∉ A)
    (hne : A.Nonempty) (rho : ℝ) (hr : 1 ≤ rho) (hr2 : rho < 2)
    (hbal : Aᶜ.card=A.card) (hB : 2 ≤ (others A j).card) :
    IsTopKByScore (fun i => osc (productResponse corner (steered A j rho) i)) A A.card ∧
    productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) Aᶜ <
      productCompressionLoss (steered A j rho) (productResponse corner (steered A j rho)) A := by
  refine ⟨steered_is_top A j hj rho (by linarith),?_⟩
  have hc : (0:ℝ)<A.card := by exact_mod_cast card_pos.mpr hne
  have hp : 0 < (A.card:ℝ)*(2-rho) := mul_pos hc (by linarith)
  have he := steered_exchange_equality A j hj rho hr hbal hB
  linarith

#print axioms margin_two_sufficient
#print axioms steered_exchange_equality
#print axioms every_subthreshold_margin_fails
end
end CIGAMF.P13.D6SharpMarginThreshold
