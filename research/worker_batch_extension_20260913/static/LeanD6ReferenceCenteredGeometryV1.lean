import «LeanD6ReferenceCenteredCompensatedV1»

/-! The centered same-response construction remains in the actual mixed-bound
model: the unit bound is attained, and the installed response capacities are
exactly the visible target. This is independent of the residual sign regime. -/
namespace CIGAMF.P13.D6ReferenceCenteredGeometry
open scoped BigOperators
open Finset
open CIGAMF.P13.D6Threshold CIGAMF.P13.D6ReferenceBridge
open CIGAMF.P13.D6ReferenceCenteredCompensated
open CIGAMF.V4.ProductSurrogate CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry
noncomputable section
variable {n : ℕ}

theorem original_mixed_eq_gate (A : Finset (I n)) (j : I n) (mu : ℝ)
    (i : I n) (x c : I n → Bool) :
    mixedDifference (world A j mu) i x c=mixedDifference (gate A j) i x c := by
  have hx := linear_difference (coeff A j mu) x i (x i) (c i)
  have hc := linear_difference (coeff A j mu) c i (x i) (c i)
  rw [Function.update_eq_self] at hx
  rw [Function.update_eq_self] at hc
  unfold mixedDifference world
  linarith

theorem centered_mixed_bound (t : ℝ) (A T : Finset (I n)) (j : I n) (rho : ℝ)
    (i : I n) (x c : I n → Bool) :
    |mixedDifference (centeredWorld A T j rho t) i x c| ≤ 1 := by
  rw [mixed_unchanged,← original_mixed_eq_gate A j 0 i x c]
  exact mixed_bound A j 0 i x c

theorem centered_mixed_attained (t : ℝ) (A T : Finset (I n)) (j : I n) (hjA : j ∉ A)
    (rho : ℝ) (i : I n) (hi : i ∈ A) :
    ∃ x c : I n → Bool,mixedDifference (centeredWorld A T j rho t) i x c=1 := by
  obtain ⟨x,c,h⟩ := mixed_bound_attained A j hjA 0 i hi
  refine ⟨x,c,?_⟩
  rw [mixed_unchanged,← original_mixed_eq_gate A j 0 i x c]
  exact h

theorem centered_response_capacity (t : ℝ) (A T : Finset (I n)) (j : I n)
    (hjA : j ∉ A) (hB2 : 2 ≤ (others A j).card) (rho : ℝ) (hr : 0 ≤ rho) (i : I n) :
    osc (productResponse (bern t) (centeredWorld A T j rho t) i) = target T rho i := by
  have ht : 0 ≤ target T rho i := by unfold target; split <;> positivity
  have he : productResponse (bern t) (centeredWorld A T j rho t) i =
      (fun u => target T rho i*bit u+(-(target T rho i)*t)) := by
    funext u
    rw [centered_response t A T j hjA hB2 rho i u]
    ring
  rw [he,osc_add_const,osc_bit_nonneg _ ht]

/-- Interior product references have positive mass at every actual cube point. -/
theorem reference_full_support (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (x : I n → Bool) : 0 < jointWeight (bern t) x := by
  unfold jointWeight
  apply Finset.prod_pos
  intro i _
  cases h : x i <;> simp [bern,h] <;> linarith

#print axioms original_mixed_eq_gate
#print axioms centered_mixed_bound
#print axioms centered_mixed_attained
#print axioms centered_response_capacity
#print axioms reference_full_support
end
end CIGAMF.P13.D6ReferenceCenteredGeometry
