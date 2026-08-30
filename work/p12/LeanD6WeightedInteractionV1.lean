import Mathlib
import «LeanProductMixedDifferenceV4»

/-! q-sensitive refinements of the D6 telescoping proof.

The `hybrid` argument is essential: averaging a differently indexed mixed
difference is not silently substituted for the identity proved in V4. -/

namespace CIGAMF.V7.D6WeightedInteraction

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

variable {U : Type*} [Fintype U] [Nonempty U]

theorem Q1_coordinate_specific_pointwise_bound {n : ℕ}
    (F : (Fin (n + 1) → U) → ℝ) (delta : Fin (n + 1) → ℝ)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta i)
    (x c : Fin (n + 1) → U) :
    |F x - (∑ i : Fin (n + 1), F (Function.update c i (x i))) +
        (n : ℝ) * F c| ≤ ∑ i : Fin n, delta i.castSucc := by
  rw [pointwise_residual_eq_sum_mixed]
  calc
    |∑ i : Fin n, mixedDifference F i.castSucc (hybrid x c i.val) c| ≤
        ∑ i : Fin n, |mixedDifference F i.castSucc (hybrid x c i.val) c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, delta i.castSucc := by
      apply Finset.sum_le_sum
      intro i hi
      exact hdelta i.castSucc (hybrid x c i.val) c

theorem Q1_product_coordinate_specific_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : Fin (n + 1) → ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta i)
    (x : Fin (n + 1) → U) :
    |F x - productA q F x| ≤ ∑ i : Fin n, delta i.castSucc := by
  rw [product_residual_eq_expectation q F hNorm x]
  unfold productExpectation
  calc
    |∑ c, jointWeight q c *
      (F x - (∑ i, F (Function.update c i (x i))) + (n : ℝ) * F c)| ≤
        ∑ c, |jointWeight q c *
          (F x - (∑ i, F (Function.update c i (x i))) + (n : ℝ) * F c)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, jointWeight q c *
          |F x - (∑ i, F (Function.update c i (x i))) + (n : ℝ) * F c| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [abs_mul, abs_of_nonneg (hWeight c)]
    _ ≤ ∑ c, jointWeight q c * (∑ i : Fin n, delta i.castSucc) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (Q1_coordinate_specific_pointwise_bound F delta hdelta x c) (hWeight c)
    _ = ∑ i : Fin n, delta i.castSucc := by
      rw [← Finset.sum_mul, hNorm, one_mul]

noncomputable def qAbsTelescopingTerm {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin n) (x : Fin (n + 1) → U) : ℝ :=
  productExpectation q (fun c =>
    |mixedDifference F i.castSucc (hybrid x c i.val) c|)

noncomputable def qSignedTelescopingTerm {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin n) (x : Fin (n + 1) → U) : ℝ :=
  productExpectation q (fun c =>
    mixedDifference F i.castSucc (hybrid x c i.val) c)

theorem residual_eq_sum_signed_telescoping {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (x : Fin (n + 1) → U) :
    F x - productA q F x =
      ∑ i : Fin n, qSignedTelescopingTerm q F i x := by
  rw [product_residual_eq_expectation q F hNorm x]
  unfold qSignedTelescopingTerm productExpectation
  simp_rw [pointwise_residual_eq_sum_mixed]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

theorem Q2_q_averaged_absolute_uniform_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (x : Fin (n + 1) → U) :
    |F x - productA q F x| ≤
      ∑ i : Fin n, qAbsTelescopingTerm q F i x := by
  rw [product_residual_eq_expectation q F hNorm x]
  unfold productExpectation qAbsTelescopingTerm
  simp_rw [pointwise_residual_eq_sum_mixed]
  calc
    |∑ c, jointWeight q c *
        (∑ i : Fin n, mixedDifference F i.castSucc (hybrid x c i.val) c)| ≤
      ∑ c, |jointWeight q c *
        (∑ i : Fin n, mixedDifference F i.castSucc (hybrid x c i.val) c)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, jointWeight q c *
        |∑ i : Fin n, mixedDifference F i.castSucc (hybrid x c i.val) c| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [abs_mul, abs_of_nonneg (hWeight c)]
    _ ≤ ∑ c, jointWeight q c *
        (∑ i : Fin n, |mixedDifference F i.castSucc (hybrid x c i.val) c|) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
        (hWeight c)
    _ = ∑ i : Fin n, ∑ c, jointWeight q c *
        |mixedDifference F i.castSucc (hybrid x c i.val) c| := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

noncomputable def qAbsUniformModulus {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin n) : ℝ :=
  maxVal (qAbsTelescopingTerm q F i)

theorem Q2_q_averaged_absolute_scalar_uniform_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (x : Fin (n + 1) → U) :
    |F x - productA q F x| ≤
      ∑ i : Fin n, qAbsUniformModulus q F i := by
  calc
    |F x - productA q F x| ≤
        ∑ i : Fin n, qAbsTelescopingTerm q F i x :=
      Q2_q_averaged_absolute_uniform_bound q F hWeight hNorm x
    _ ≤ ∑ i : Fin n, qAbsUniformModulus q F i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_maxVal (qAbsTelescopingTerm q F i) x

theorem Q3_signed_average_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (x : Fin (n + 1) → U) :
    |F x - productA q F x| ≤
      ∑ i : Fin n, |qSignedTelescopingTerm q F i x| := by
  rw [residual_eq_sum_signed_telescoping q F hNorm x]
  exact Finset.abs_sum_le_sum_abs _ _

theorem signed_le_absolute_telescoping {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (i : Fin n) (x : Fin (n + 1) → U) :
    |qSignedTelescopingTerm q F i x| ≤ qAbsTelescopingTerm q F i x := by
  unfold qSignedTelescopingTerm qAbsTelescopingTerm productExpectation
  calc
    |∑ c, jointWeight q c *
        mixedDifference F i.castSucc (hybrid x c i.val) c| ≤
      ∑ c, |jointWeight q c *
        mixedDifference F i.castSucc (hybrid x c i.val) c| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, jointWeight q c *
        |mixedDifference F i.castSucc (hybrid x c i.val) c| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [abs_mul, abs_of_nonneg (hWeight c)]

noncomputable def qMeanAbsoluteResidual {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F A : (Fin (n + 1) → U) → ℝ) : ℝ :=
  productExpectation q (fun x => |F x - A x|)

theorem Q4_distributional_residual_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1) :
    qMeanAbsoluteResidual q F (productA q F) ≤
      productExpectation q (fun x =>
        ∑ i : Fin n, qAbsTelescopingTerm q F i x) := by
  unfold qMeanAbsoluteResidual productExpectation
  apply Finset.sum_le_sum
  intro x hx
  exact mul_le_mul_of_nonneg_left
    (Q2_q_averaged_absolute_uniform_bound q F hWeight hNorm x) (hWeight x)

noncomputable def qL1CompressionLoss {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (H : (Fin (n + 1) → U) → ℝ)
    (Q : Fin (n + 1) → U → ℝ)
    (selected : Finset (Fin (n + 1))) : ℝ :=
  productExpectation q (fun x =>
    |H x - selected.sum (fun j => Q j (x j))|)

theorem qL1CompressionLoss_transfer {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F A : (Fin (n + 1) → U) → ℝ)
    (Q : Fin (n + 1) → U → ℝ)
    (selected : Finset (Fin (n + 1)))
    (hWeight : ∀ c, 0 ≤ jointWeight q c) :
    |qL1CompressionLoss q F Q selected - qL1CompressionLoss q A Q selected| ≤
      qMeanAbsoluteResidual q F A := by
  unfold qL1CompressionLoss qMeanAbsoluteResidual productExpectation
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x, (jointWeight q x *
        |F x - selected.sum (fun j => Q j (x j))| -
      jointWeight q x *
        |A x - selected.sum (fun j => Q j (x j))|)| ≤
      ∑ x, |(jointWeight q x *
        |F x - selected.sum (fun j => Q j (x j))| -
      jointWeight q x *
        |A x - selected.sum (fun j => Q j (x j))|)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, jointWeight q x * |F x - A x| := by
      apply Finset.sum_le_sum
      intro x hx
      rw [← mul_sub, abs_mul, abs_of_nonneg (hWeight x)]
      apply mul_le_mul_of_nonneg_left _ (hWeight x)
      simpa only [sub_sub_sub_cancel_right] using
        abs_abs_sub_abs_le
          (F x - selected.sum (fun j => Q j (x j)))
          (A x - selected.sum (fun j => Q j (x j)))

theorem Q5_distributional_decision_regret {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected optimum : Finset (Fin (n + 1)))
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hSurrogateOptimal :
      qL1CompressionLoss q (productA q F) (productResponse q F) selected ≤
      qL1CompressionLoss q (productA q F) (productResponse q F) optimum) :
    qL1CompressionLoss q F (productResponse q F) selected ≤
      qL1CompressionLoss q F (productResponse q F) optimum +
        2 * qMeanAbsoluteResidual q F (productA q F) := by
  have hs := abs_le.mp (qL1CompressionLoss_transfer q F (productA q F)
    (productResponse q F) selected hWeight)
  have ho := abs_le.mp (qL1CompressionLoss_transfer q F (productA q F)
    (productResponse q F) optimum hWeight)
  linarith

end CIGAMF.V7.D6WeightedInteraction
