import Mathlib
import «LeanProductMixedDifferenceV4»

/-!
# Exact rational sharpness witness for the D6 half-factor target

This P13 extension does not modify the certified P12 baseline.  It gives a
three-coordinate binary product world in which a valid (tied) Top-C singleton
has true compression regret exactly `(m - 1) * delta / 2`.  Consequently, if
the half-factor upper bound is proved, its constant is already worst-case
sharp under the current non-strict `IsTopKByScore` semantics.
-/

namespace CIGAMF.P13.D6HalfFactorSharpness

open scoped BigOperators Matrix
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

def anchor3 : Fin 3 → Fin 2 := ![1, 1, 0]

def pointMassAnchor3 (i : Fin 3) (u : Fin 2) : ℝ :=
  if u = anchor3 i then 1 else 0

/- Values in lexicographic action order `000, ..., 111` are
   `0, 0, 2, 2, 0, 0, 1, 2`. -/
def sharpWorld3 (x : Fin 3 → Fin 2) : ℝ :=
  if x 1 = 0 then 0
  else if x 0 = 0 then 2
  else if x 2 = 0 then 1
  else 2

def action3 (a b c : Fin 2) : Fin 3 → Fin 2 := ![a, b, c]

private theorem fin2_zero_or_one (u : Fin 2) : u = 0 ∨ u = 1 := by
  fin_cases u <;> simp

theorem pointMassAnchor3_jointWeight (c : Fin 3 → Fin 2) :
    jointWeight pointMassAnchor3 c = if c = anchor3 then 1 else 0 := by
  classical
  by_cases h : c = anchor3
  · subst c
    norm_num [jointWeight, pointMassAnchor3, anchor3, Fin.prod_univ_three]
  · have hc : c 0 ≠ anchor3 0 ∨ c 1 ≠ anchor3 1 ∨
        c 2 ≠ anchor3 2 := by
      by_contra hn
      push_neg at hn
      apply h
      funext i
      fin_cases i <;> simp [hn.1, hn.2.1, hn.2.2]
    rcases hc with hc | hc | hc <;>
      simp [jointWeight, pointMassAnchor3, Fin.prod_univ_three, hc, h]

theorem pointMassAnchor3_expectation (G : (Fin 3 → Fin 2) → ℝ) :
    productExpectation pointMassAnchor3 G = G anchor3 := by
  classical
  unfold productExpectation
  simp_rw [pointMassAnchor3_jointWeight]
  rw [Finset.sum_eq_single anchor3]
  · simp
  · intro b hb hne
    simp [hne]
  · simp

@[simp] theorem sharp_response_zero (j : Fin 3) :
    productResponse pointMassAnchor3 sharpWorld3 j 0 =
      ![(2 : ℝ), 0, 1] j := by
  unfold productResponse
  rw [pointMassAnchor3_expectation]
  fin_cases j <;>
    simp [sharpWorld3, anchor3, Function.update]

@[simp] theorem sharp_response_one (j : Fin 3) :
    productResponse pointMassAnchor3 sharpWorld3 j 1 =
      ![(1 : ℝ), 1, 2] j := by
  unfold productResponse
  rw [pointMassAnchor3_expectation]
  fin_cases j <;>
    simp [sharpWorld3, anchor3, Function.update]

theorem sharp_response_span (j : Fin 3) :
    osc (productResponse pointMassAnchor3 sharpWorld3 j) = 1 := by
  have hmax : maxVal (productResponse pointMassAnchor3 sharpWorld3 j) =
      ![(2 : ℝ), 1, 2] j := by
    apply le_antisymm
    · apply maxVal_le
      intro u
      fin_cases j <;> fin_cases u <;> norm_num
    · fin_cases j
      · simpa using le_maxVal
          (productResponse pointMassAnchor3 sharpWorld3 0) (0 : Fin 2)
      · simpa using le_maxVal
          (productResponse pointMassAnchor3 sharpWorld3 1) (1 : Fin 2)
      · simpa using le_maxVal
          (productResponse pointMassAnchor3 sharpWorld3 2) (1 : Fin 2)
  have hmin : minVal (productResponse pointMassAnchor3 sharpWorld3 j) =
      ![(1 : ℝ), 0, 1] j := by
    apply le_antisymm
    · fin_cases j
      · simpa using minVal_le
          (productResponse pointMassAnchor3 sharpWorld3 0) (1 : Fin 2)
      · simpa using minVal_le
          (productResponse pointMassAnchor3 sharpWorld3 1) (0 : Fin 2)
      · simpa using minVal_le
          (productResponse pointMassAnchor3 sharpWorld3 2) (0 : Fin 2)
    · apply le_minVal
      intro u
      fin_cases j <;> fin_cases u <;> norm_num
  rw [osc, hmax, hmin]
  fin_cases j <;> norm_num

theorem selectedTwo_is_topC :
    IsTopKByScore
      (fun j ↦ osc (productResponse pointMassAnchor3 sharpWorld3 j))
      ({2} : Finset (Fin 3)) 1 := by
  constructor
  · simp
  · intro candidate hcard
    simp_rw [sharp_response_span]
    simp [hcard]

private theorem residual_selectedTwo_bounds (x : Fin 3 → Fin 2) :
    -2 ≤ sharpWorld3 x -
        ({2} : Finset (Fin 3)).sum
          (fun j ↦ productResponse pointMassAnchor3 sharpWorld3 j (x j)) ∧
    sharpWorld3 x -
        ({2} : Finset (Fin 3)).sum
          (fun j ↦ productResponse pointMassAnchor3 sharpWorld3 j (x j)) ≤ 1 := by
  simp only [Finset.sum_singleton]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    simp [sharpWorld3, h0, h1, h2] <;> norm_num

private theorem residual_selectedOne_bounds (x : Fin 3 → Fin 2) :
    0 ≤ sharpWorld3 x -
        ({1} : Finset (Fin 3)).sum
          (fun j ↦ productResponse pointMassAnchor3 sharpWorld3 j (x j)) ∧
    sharpWorld3 x -
        ({1} : Finset (Fin 3)).sum
          (fun j ↦ productResponse pointMassAnchor3 sharpWorld3 j (x j)) ≤ 1 := by
  simp only [Finset.sum_singleton]
  rcases fin2_zero_or_one (x 0) with h0 | h0 <;>
    rcases fin2_zero_or_one (x 1) with h1 | h1 <;>
    rcases fin2_zero_or_one (x 2) with h2 | h2 <;>
    simp [sharpWorld3, h0, h1, h2] <;> norm_num

theorem sharp_selectedTwo_loss :
    productCompressionLoss sharpWorld3
      (productResponse pointMassAnchor3 sharpWorld3) ({2} : Finset (Fin 3)) =
        3 / 2 := by
  let r : (Fin 3 → Fin 2) → ℝ := fun x ↦ sharpWorld3 x -
    ({2} : Finset (Fin 3)).sum
      (fun j ↦ productResponse pointMassAnchor3 sharpWorld3 j (x j))
  have hmax : maxVal r = 1 := by
    apply le_antisymm
    · apply maxVal_le
      intro x
      exact (residual_selectedTwo_bounds x).2
    · have h := le_maxVal r (action3 0 1 0)
      have hw : r (action3 0 1 0) = 1 := by
        norm_num [r, action3, sharpWorld3]
      rw [hw] at h
      exact h
  have hmin : minVal r = -2 := by
    apply le_antisymm
    · have h := minVal_le r (action3 0 0 1)
      have hw : r (action3 0 0 1) = -2 := by
        norm_num [r, action3, sharpWorld3]
      rw [hw] at h
      exact h
    · apply le_minVal
      intro x
      exact (residual_selectedTwo_bounds x).1
  norm_num [productCompressionLoss, r, osc, hmax, hmin]

theorem sharp_selectedOne_loss :
    productCompressionLoss sharpWorld3
      (productResponse pointMassAnchor3 sharpWorld3) ({1} : Finset (Fin 3)) =
        1 / 2 := by
  let r : (Fin 3 → Fin 2) → ℝ := fun x ↦ sharpWorld3 x -
    ({1} : Finset (Fin 3)).sum
      (fun j ↦ productResponse pointMassAnchor3 sharpWorld3 j (x j))
  have hmax : maxVal r = 1 := by
    apply le_antisymm
    · apply maxVal_le
      intro x
      exact (residual_selectedOne_bounds x).2
    · have h := le_maxVal r (action3 0 1 0)
      have hw : r (action3 0 1 0) = 1 := by
        norm_num [r, action3, sharpWorld3]
      rw [hw] at h
      exact h
  have hmin : minVal r = 0 := by
    apply le_antisymm
    · have h := minVal_le r (action3 0 0 0)
      have hw : r (action3 0 0 0) = 0 := by
        norm_num [r, action3, sharpWorld3]
      rw [hw] at h
      exact h
    · apply le_minVal
      intro x
      exact (residual_selectedOne_bounds x).1
  norm_num [productCompressionLoss, r, osc, hmax, hmin]

theorem sharp_mixed_difference_bound
    (i : Fin 3) (x c : Fin 3 → Fin 2) :
    |mixedDifference sharpWorld3 i x c| ≤ 1 := by
  fin_cases i <;>
    rcases fin2_zero_or_one (x 0) with hx0 | hx0 <;>
    rcases fin2_zero_or_one (x 1) with hx1 | hx1 <;>
    rcases fin2_zero_or_one (x 2) with hx2 | hx2 <;>
    rcases fin2_zero_or_one (c 0) with hc0 | hc0 <;>
    rcases fin2_zero_or_one (c 1) with hc1 | hc1 <;>
    rcases fin2_zero_or_one (c 2) with hc2 | hc2 <;>
    simp [mixedDifference, sharpWorld3, hx0, hx1, hx2,
      hc0, hc1, hc2, Function.update] <;> norm_num

theorem D6_half_factor_exact_rational_sharpness :
    let selected : Finset (Fin 3) := {2}
    let competitor : Finset (Fin 3) := {1}
    IsTopKByScore
      (fun j ↦ osc (productResponse pointMassAnchor3 sharpWorld3 j))
      selected 1 ∧
    (∀ i x c, |mixedDifference sharpWorld3 i x c| ≤ (1 : ℝ)) ∧
    productCompressionLoss sharpWorld3
        (productResponse pointMassAnchor3 sharpWorld3) selected -
      productCompressionLoss sharpWorld3
        (productResponse pointMassAnchor3 sharpWorld3) competitor =
      ((2 : ℝ) * 1) / 2 := by
  dsimp
  exact ⟨selectedTwo_is_topC, sharp_mixed_difference_bound, by
    rw [sharp_selectedTwo_loss, sharp_selectedOne_loss]
    norm_num⟩

end CIGAMF.P13.D6HalfFactorSharpness
