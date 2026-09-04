import Mathlib
import «LeanD6ResidualCentering»

/-!
# Product-reference residual orthogonality

For normalized finite product-reference rows, the ANOVA residual
`e = F - A_q` has zero product expectation and zero first-order product
responses.  Both conclusions are derived from the literal P12 definitions;
they are not assumed as centering hypotheses.
-/

namespace CIGAMF.P13.D6ResidualOrthogonality

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6ResidualCentering

variable {U : Type*} [Fintype U] [Nonempty U]

private lemma product_modified_at_coordinate {n : ℕ}
    (q : Fin (n + 1) → U → ℝ) (i : Fin (n + 1))
    (g : U → ℝ) (c : Fin (n + 1) → U) :
    (∏ j, if j = i then q j (c j) * g (c j) else q j (c j)) =
      jointWeight q c * g (c i) := by
  classical
  unfold jointWeight
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j ↦ if j = i then q j (c j) * g (c j) else q j (c j))
    (Finset.mem_univ i)]
  rw [← Finset.prod_erase_mul Finset.univ (fun j ↦ q j (c j))
    (Finset.mem_univ i)]
  simp only [if_pos]
  have hsame :
      (∏ x ∈ Finset.univ.erase i,
        if x = i then q x (c x) * g (c x) else q x (c x)) =
      ∏ x ∈ Finset.univ.erase i, q x (c x) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [hji]
  rw [hsame]
  ring

theorem productExpectation_coordinate {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1)
    (i : Fin (n + 1)) (g : U → ℝ) :
    productExpectation q (fun c ↦ g (c i)) = ∑ u, q i u * g u := by
  classical
  unfold productExpectation
  rw [show (∑ c, jointWeight q c * g (c i)) =
      ∑ (c : Fin (n + 1) → U),
        ∏ j, if j = i then q j (c j) * g (c j) else q j (c j) by
    apply Finset.sum_congr rfl
    intro c hc
    exact (product_modified_at_coordinate q i g c).symm]
  rw [← Fintype.piFinset_univ]
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset U)
    (fun j u ↦ if j = i then q j u * g u else q j u)]
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j ↦ ∑ u, if j = i then q j u * g u else q j u)
    (Finset.mem_univ i)]
  simp only [if_pos]
  have hrest :
      (∏ j ∈ Finset.univ.erase i,
        ∑ u, if j = i then q j u * g u else q j u) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [hji, hRow j]
  rw [hrest]
  ring

noncomputable def coordinateSwap {n : ℕ} (i : Fin (n + 1)) :
    (U × (Fin (n + 1) → U)) ≃ (U × (Fin (n + 1) → U)) where
  toFun z := (z.2 i, Function.update z.2 i z.1)
  invFun z := (z.2 i, Function.update z.2 i z.1)
  left_inv z := by
    rcases z with ⟨u, c⟩
    simp [Function.update_idem, Function.update_eq_self]
  right_inv z := by
    rcases z with ⟨u, c⟩
    simp [Function.update_idem, Function.update_eq_self]

private lemma coordinateSwap_weight {n : ℕ}
    (q : Fin (n + 1) → U → ℝ) (i : Fin (n + 1))
    (u : U) (c : Fin (n + 1) → U) :
    q i (c i) * jointWeight q (Function.update c i u) =
      q i u * jointWeight q c := by
  classical
  unfold jointWeight
  rw [← Finset.prod_erase_mul Finset.univ
    (fun j ↦ q j ((Function.update c i u) j)) (Finset.mem_univ i)]
  rw [← Finset.prod_erase_mul Finset.univ (fun j ↦ q j (c j))
    (Finset.mem_univ i)]
  simp
  have hsame :
      (∏ x ∈ Finset.univ.erase i, q x ((Function.update c i u) x)) =
      ∏ x ∈ Finset.univ.erase i, q x (c x) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by simpa using hj
    simp [Function.update, hji]
  rw [hsame]
  ring

theorem productResponse_average {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1)
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) :
    (∑ u, q i u * productResponse q F i u) = productB q F := by
  classical
  unfold productResponse productB productExpectation
  have hswap :
      (∑ z : U × (Fin (n + 1) → U),
        q i z.1 * jointWeight q z.2 * F (Function.update z.2 i z.1)) =
      ∑ z : U × (Fin (n + 1) → U),
        q i z.1 * jointWeight q z.2 * F z.2 := by
    apply Fintype.sum_equiv (coordinateSwap i)
    intro z
    rcases z with ⟨u, c⟩
    change q i u * jointWeight q c * F (Function.update c i u) =
      q i (c i) * jointWeight q (Function.update c i u) *
        F (Function.update c i u)
    rw [coordinateSwap_weight]
  rw [show (∑ u, q i u *
      ∑ c, jointWeight q c * F (Function.update c i u)) =
      ∑ z : U × (Fin (n + 1) → U),
        q i z.1 * jointWeight q z.2 * F (Function.update z.2 i z.1) by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    ring]
  rw [hswap, Fintype.sum_prod_type]
  rw [show (∑ x : U, ∑ y, q i x * jointWeight q y * F y) =
      (∑ x : U, q i x) * (∑ y, jointWeight q y * F y) by
    calc
      _ = ∑ x : U, q i x * (∑ y, jointWeight q y * F y) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = _ := by rw [Finset.sum_mul]]
  rw [hRow]
  simp

theorem jointWeight_normalized {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1) :
    ∑ c, jointWeight q c = 1 := by
  classical
  unfold jointWeight
  rw [← Fintype.piFinset_univ]
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset U) q]
  simp [hRow]

private lemma weighted_sum_surrogate_expand {n : ℕ}
    (q : Fin (n + 1) → U → ℝ) (Q : Fin (n + 1) → U → ℝ)
    (b : ℝ) :
    (∑ c, jointWeight q c *
      ((∑ j, Q j (c j)) - ((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b)) =
    (∑ j, ∑ c, jointWeight q c * Q j (c j)) -
      ((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b *
        (∑ c, jointWeight q c) := by
  calc
    _ = ∑ c, (jointWeight q c * (∑ j, Q j (c j)) -
        jointWeight q c * (((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b)) := by
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = (∑ c, jointWeight q c * (∑ j, Q j (c j))) -
        ∑ c, jointWeight q c *
          (((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [show (∑ c, jointWeight q c * (∑ j, Q j (c j))) =
          ∑ j, ∑ c, jointWeight q c * Q j (c j) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]]
      rw [← Finset.sum_mul]
      ring

theorem productA_expectation_eq_productB {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1)
    (F : (Fin (n + 1) → U) → ℝ) :
    productExpectation q (productA q F) = productB q F := by
  classical
  have hJoint := jointWeight_normalized q hRow
  have hQmean : ∀ j : Fin (n + 1),
      (∑ c, jointWeight q c * productResponse q F j (c j)) =
        productB q F := by
    intro j
    change productExpectation q (fun c ↦ productResponse q F j (c j)) =
      productB q F
    rw [productExpectation_coordinate q hRow]
    exact productResponse_average q hRow F j
  unfold productExpectation productA surrogate
  rw [weighted_sum_surrogate_expand]
  simp_rw [hQmean]
  rw [hJoint]
  simp
  ring

theorem R0_productResidual_expectation_zero {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1)
    (F : (Fin (n + 1) → U) → ℝ) :
    productExpectation q (productResidual q F) = 0 := by
  classical
  unfold productExpectation productResidual
  rw [show (∑ c, jointWeight q c * (F c - productA q F c)) =
      (∑ c, jointWeight q c * F c) -
        (∑ c, jointWeight q c * productA q F c) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    ring]
  change productB q F - productExpectation q (productA q F) = 0
  rw [productA_expectation_eq_productB q hRow F]
  ring

private lemma weighted_sum_updated_surrogate_expand {n : ℕ}
    (q : Fin (n + 1) → U → ℝ) (Q : Fin (n + 1) → U → ℝ)
    (b : ℝ) (i : Fin (n + 1)) (u : U) :
    (∑ c, jointWeight q c *
      ((∑ j, Q j ((Function.update c i u) j)) -
        ((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b)) =
    (∑ j, ∑ c, jointWeight q c * Q j ((Function.update c i u) j)) -
      ((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b *
        (∑ c, jointWeight q c) := by
  calc
    _ = ∑ c, (jointWeight q c *
        (∑ j, Q j ((Function.update c i u) j)) -
        jointWeight q c * (((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b)) := by
      apply Finset.sum_congr rfl
      intro c hc
      ring
    _ = (∑ c, jointWeight q c *
        (∑ j, Q j ((Function.update c i u) j))) -
        ∑ c, jointWeight q c *
          (((Fintype.card (Fin (n + 1)) : ℝ) - 1) * b) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [show (∑ c, jointWeight q c *
          (∑ j, Q j ((Function.update c i u) j))) =
          ∑ j, ∑ c, jointWeight q c *
            Q j ((Function.update c i u) j) by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]]
      rw [← Finset.sum_mul]
      ring

theorem productA_response_eq_original {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1)
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u : U) :
    productResponse q (productA q F) i u = productResponse q F i u := by
  classical
  have hJoint := jointWeight_normalized q hRow
  have hQmean : ∀ j : Fin (n + 1),
      (∑ c, jointWeight q c * productResponse q F j (c j)) =
        productB q F := by
    intro j
    change productExpectation q (fun c ↦ productResponse q F j (c j)) =
      productB q F
    rw [productExpectation_coordinate q hRow]
    exact productResponse_average q hRow F j
  have hTerm : ∀ j : Fin (n + 1),
      (∑ c, jointWeight q c *
        productResponse q F j ((Function.update c i u) j)) =
      if j = i then productResponse q F i u else productB q F := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [Function.update]
      rw [← Finset.sum_mul, hJoint, one_mul]
    · simpa [Function.update, hji] using hQmean j
  rw [show productResponse q (productA q F) i u =
      productExpectation q (fun c ↦ productA q F (Function.update c i u)) by
    rfl]
  unfold productExpectation productA surrogate
  rw [weighted_sum_updated_surrogate_expand]
  simp_rw [hTerm]
  rw [hJoint]
  have hite :
      (∑ j : Fin (n + 1),
        if j = i then productResponse q F i u else productB q F) =
      productResponse q F i u + (n : ℝ) * productB q F := by
    have hrest :
        (∑ j ∈ Finset.univ.erase i,
          if j = i then productResponse q F i u else productB q F) =
        (n : ℝ) * productB q F := by
      rw [show (∑ j ∈ Finset.univ.erase i,
          if j = i then productResponse q F i u else productB q F) =
          ∑ j ∈ Finset.univ.erase i, productB q F by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := by simpa using hj
        simp [hji]]
      simp
    calc
      _ = (∑ j ∈ Finset.univ.erase i,
          if j = i then productResponse q F i u else productB q F) +
          (if i = i then productResponse q F i u else productB q F) := by
            symm
            exact Finset.sum_erase_add _ _ (Finset.mem_univ i)
      _ = _ := by rw [hrest]; simp; ring
  rw [hite]
  simp

theorem R1_productResidual_response_zero {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (hRow : ∀ i, ∑ u, q i u = 1)
    (F : (Fin (n + 1) → U) → ℝ) (i : Fin (n + 1)) (u : U) :
    productResponse q (productResidual q F) i u = 0 := by
  classical
  rw [show productResponse q (productResidual q F) i u =
      productExpectation q (fun c ↦
        F (Function.update c i u) -
          productA q F (Function.update c i u)) by rfl]
  unfold productExpectation
  rw [show (∑ c, jointWeight q c *
      (F (Function.update c i u) - productA q F (Function.update c i u))) =
      (∑ c, jointWeight q c * F (Function.update c i u)) -
        (∑ c, jointWeight q c *
          productA q F (Function.update c i u)) by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    ring]
  change productResponse q F i u - productResponse q (productA q F) i u = 0
  rw [productA_response_eq_original q hRow F i u]
  ring

end CIGAMF.P13.D6ResidualOrthogonality
