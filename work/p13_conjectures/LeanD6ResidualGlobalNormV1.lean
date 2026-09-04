import Mathlib
import «LeanD6ResidualCentering»

/-!
# Product residual centering from global normalization

The older residual API uses row normalization
`∀ i, ∑ u, q i u = 1`.  For the actual finite product weights used by the
D6 headline, the weaker global normalization
`∑ c, jointWeight q c = 1` is already sufficient.  The key algebra is a
weight-preserving swap of one coordinate between two full product worlds.

This module proves the first bridge in that direction: the product average of
each first-order response is the product baseline under `hNorm` alone.  It
does not modify P12 or replace the older API.
-/

namespace CIGAMF.P13.D6ResidualGlobalNorm

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ResidualCentering

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Swap the `i`-th coordinates of two full worlds. -/
noncomputable def coordinatePairSwap {n : ℕ} (i : Fin (n + 1)) :
    ((Fin (n + 1) → U) × (Fin (n + 1) → U)) ≃
      ((Fin (n + 1) → U) × (Fin (n + 1) → U)) where
  toFun z :=
    (Function.update z.2 i (z.1 i), Function.update z.1 i (z.2 i))
  invFun z :=
    (Function.update z.2 i (z.1 i), Function.update z.1 i (z.2 i))
  left_inv z := by
    rcases z with ⟨x, c⟩
    simp [Function.update_idem, Function.update_eq_self]
  right_inv z := by
    rcases z with ⟨x, c⟩
    simp [Function.update_idem, Function.update_eq_self]

/-- Swapping one coordinate between two worlds preserves the product of their
joint weights.  No row normalization is used. -/
private theorem jointWeight_coordinatePairSwap {n : ℕ}
    (q : Fin (n + 1) → U → ℝ) (i : Fin (n + 1))
    (x c : Fin (n + 1) → U) :
    jointWeight q x * jointWeight q c =
      jointWeight q (Function.update c i (x i)) *
        jointWeight q (Function.update x i (c i)) := by
  classical
  unfold jointWeight
  rw [← Finset.prod_erase_mul Finset.univ (fun j ↦ q j (x j))
      (Finset.mem_univ i),
    ← Finset.prod_erase_mul Finset.univ (fun j ↦ q j (c j))
      (Finset.mem_univ i),
    ← Finset.prod_erase_mul Finset.univ
      (fun j ↦ q j ((Function.update c i (x i)) j))
      (Finset.mem_univ i),
    ← Finset.prod_erase_mul Finset.univ
      (fun j ↦ q j ((Function.update x i (c i)) j))
      (Finset.mem_univ i)]
  simp only [Function.update_self]
  have hx :
      (∏ j ∈ Finset.univ.erase i,
        q j ((Function.update x i (c i)) j)) =
        ∏ j ∈ Finset.univ.erase i, q j (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  have hc :
      (∏ j ∈ Finset.univ.erase i,
        q j ((Function.update c i (x i)) j)) =
        ∏ j ∈ Finset.univ.erase i, q j (c j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [hx, hc]
  ring

/-- Under global product normalization, averaging the `i`-th response back
over a full product world recovers the baseline.  This is the exact place
where the former `hRow` proof artifact is removed. -/
theorem productResponse_global_mean {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1))
    (hNorm : ∑ c, jointWeight q c = 1) :
    productExpectation q (fun x ↦ productResponse q F i (x i)) =
      productB q F := by
  classical
  unfold productExpectation productResponse productB
  simp only [productExpectation]
  rw [show
      (∑ x, jointWeight q x *
        (∑ c, jointWeight q c * F (Function.update c i (x i)))) =
        ∑ z : (Fin (n + 1) → U) × (Fin (n + 1) → U),
          jointWeight q z.1 * jointWeight q z.2 *
            F (Function.update z.2 i (z.1 i)) by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      ring]
  have hswap :
      (∑ z : (Fin (n + 1) → U) × (Fin (n + 1) → U),
        jointWeight q z.1 * jointWeight q z.2 *
          F (Function.update z.2 i (z.1 i))) =
        ∑ z : (Fin (n + 1) → U) × (Fin (n + 1) → U),
          jointWeight q z.1 * jointWeight q z.2 * F z.1 := by
    apply Fintype.sum_equiv (coordinatePairSwap i)
    intro z
    rcases z with ⟨x, c⟩
    change jointWeight q x * jointWeight q c *
        F (Function.update c i (x i)) =
      jointWeight q (Function.update c i (x i)) *
        jointWeight q (Function.update x i (c i)) *
          F (Function.update c i (x i))
    rw [jointWeight_coordinatePairSwap]
  rw [hswap, Fintype.sum_prod_type]
  change
      (∑ x : Fin (n + 1) → U,
        ∑ c : Fin (n + 1) → U,
          jointWeight q x * jointWeight q c * F x) =
        ∑ x, jointWeight q x * F x
  rw [show
      (∑ x : Fin (n + 1) → U,
        ∑ c : Fin (n + 1) → U,
          jointWeight q x * jointWeight q c * F x) =
        (∑ c, jointWeight q c) *
          (∑ x, jointWeight q x * F x) by
      calc
        _ = ∑ x : Fin (n + 1) → U,
            (jointWeight q x * F x) * (∑ c, jointWeight q c) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          ring
        _ = _ := by
          rw [← Finset.sum_mul]
          ring]
  rw [hNorm, one_mul]

end CIGAMF.P13.D6ResidualGlobalNorm
