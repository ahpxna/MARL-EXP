import Mathlib
import «LeanProductMixedDifferenceV4»

/-!
# D6 H3 exchange route

This P13 module develops the signed local ingredient needed by H3-old.  It
keeps the pointwise sign of a coordinate contrast and shows that subtracting
the product response makes the retained coordinate `delta`-insensitive.
Unlike the active D4 route, no separate absolute world-transfer bound is used.
-/

namespace CIGAMF.P13.D6H3Exchange

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.V4.SupportGeometry

variable {U : Type*} [Fintype U] [Nonempty U]

/-! `IsTopKByScore` is stated as a cardinality-constrained sum optimum.  The
exchange proof needs its elementary but important pointwise consequence: no
rejected coordinate can have a larger score than a selected coordinate. -/
theorem topK_pairwise_score_order {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (C : ι → ℝ) (selected : Finset ι) (k : ℕ)
    (hTop : IsTopKByScore C selected k)
    {i j : ι} (hi : i ∈ selected) (hj : j ∉ selected) :
    C j ≤ C i := by
  classical
  let candidate := insert j (selected.erase i)
  have hjErase : j ∉ selected.erase i := by
    simp [hj]
  have hcard : candidate.card = k := by
    have hkpos : 0 < k := by
      rw [← hTop.1]
      exact Finset.card_pos.mpr ⟨i, hi⟩
    calc
      candidate.card = (selected.erase i).card + 1 :=
        Finset.card_insert_of_notMem hjErase
      _ = selected.card - 1 + 1 := by rw [Finset.card_erase_of_mem hi]
      _ = k := by rw [hTop.1]; omega
  have hsum := hTop.2 candidate hcard
  have hcandidate : candidate.sum C = C j + (selected.erase i).sum C := by
    simp [candidate, hjErase]
  have hselected : selected.sum C = C i + (selected.erase i).sum C := by
    have h := Finset.sum_erase_add selected C hi
    linarith
  rw [hcandidate, hselected] at hsum
  linarith

theorem productResponse_sub_eq_expectation_contrast {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (i : Fin (n + 1)) (u v : U) :
    productResponse q F i u - productResponse q F i v =
      productExpectation q (fun c ↦
        F (Function.update c i u) - F (Function.update c i v)) := by
  unfold productResponse productExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem coordinate_contrast_error_eq_expectation_mixed {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (hNorm : ∑ c, jointWeight q c = 1)
    (i : Fin (n + 1)) (u v : U) (z : Fin (n + 1) → U) :
    (F (Function.update z i u) - F (Function.update z i v)) -
        (productResponse q F i u - productResponse q F i v) =
      productExpectation q (fun c ↦
        mixedDifference F i (Function.update z i u)
          (Function.update c i v)) := by
  rw [productResponse_sub_eq_expectation_contrast]
  unfold productExpectation
  have hfirst :
      F (Function.update z i u) - F (Function.update z i v) =
        ∑ c, jointWeight q c *
          (F (Function.update z i u) - F (Function.update z i v)) := by
    rw [← Finset.sum_mul, hNorm, one_mul]
  rw [hfirst, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  simp only [mixedDifference]
  simp
  ring

theorem coordinate_contrast_error_le_delta {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (i : Fin (n + 1)) (u v : U) (z : Fin (n + 1) → U) :
    |(F (Function.update z i u) - F (Function.update z i v)) -
        (productResponse q F i u - productResponse q F i v)| ≤ delta := by
  rw [coordinate_contrast_error_eq_expectation_mixed q F hNorm i u v z]
  unfold productExpectation
  calc
    |∑ c, jointWeight q c *
        mixedDifference F i (Function.update z i u) (Function.update c i v)| ≤
        ∑ c, |jointWeight q c *
          mixedDifference F i (Function.update z i u) (Function.update c i v)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, jointWeight q c *
        |mixedDifference F i (Function.update z i u) (Function.update c i v)| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [abs_mul, abs_of_nonneg (hWeight c)]
    _ ≤ ∑ c, jointWeight q c * delta := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (hdelta i (Function.update z i u) (Function.update c i v))
        (hWeight c)
    _ = delta := by
      rw [← Finset.sum_mul, hNorm, one_mul]

theorem retained_coordinate_is_delta_insensitive {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (i : Fin (n + 1)) (u v : U) (z : Fin (n + 1) → U) :
    |(F (Function.update z i u) - productResponse q F i u) -
      (F (Function.update z i v) - productResponse q F i v)| ≤ delta := by
  simpa [sub_sub_sub_comm] using
    coordinate_contrast_error_le_delta q F delta hWeight hNorm hdelta i u v z

noncomputable def retainedResidual {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1)))
    (x : Fin (n + 1) → U) : ℝ :=
  F x - selected.sum (fun j ↦ productResponse q F j (x j))

theorem retainedResidual_coordinate_is_delta_insensitive {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ selected)
    (u v : U) (z : Fin (n + 1) → U) :
    |retainedResidual q F selected (Function.update z i u) -
      retainedResidual q F selected (Function.update z i v)| ≤ delta := by
  have hsum :
      selected.sum (fun j ↦
          productResponse q F j ((Function.update z i u) j)) -
        selected.sum (fun j ↦
          productResponse q F j ((Function.update z i v) j)) =
        productResponse q F i u - productResponse q F i v := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Function.update, hji]
    · intro hnot
      exact (hnot hi).elim
  have hlocal := retained_coordinate_is_delta_insensitive q F delta hWeight
    hNorm hdelta i u v z
  unfold retainedResidual
  rw [show
      F (Function.update z i u) -
          selected.sum (fun j ↦ productResponse q F j ((Function.update z i u) j)) -
        (F (Function.update z i v) -
          selected.sum (fun j ↦ productResponse q F j ((Function.update z i v) j))) =
      (F (Function.update z i u) - F (Function.update z i v)) -
        (selected.sum (fun j ↦ productResponse q F j ((Function.update z i u) j)) -
          selected.sum (fun j ↦ productResponse q F j ((Function.update z i v) j))) by
        ring]
  rw [hsum]
  simpa [sub_sub_sub_comm] using hlocal

def patchCoordinates {n : ℕ}
    (x y : Fin (n + 1) → U) (coordinates : Finset (Fin (n + 1)))
    (j : Fin (n + 1)) : U :=
  if j ∈ coordinates then y j else x j

@[simp] theorem patchCoordinates_empty {n : ℕ}
    (x y : Fin (n + 1) → U) :
    patchCoordinates x y ∅ = x := by
  funext j
  simp [patchCoordinates]

theorem patchCoordinates_insert {n : ℕ}
    (x y : Fin (n + 1) → U) (coordinates : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∉ coordinates) :
    patchCoordinates x y (insert i coordinates) =
      Function.update (patchCoordinates x y coordinates) i (y i) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [patchCoordinates]
  · by_cases hj : j ∈ coordinates <;>
      simp [patchCoordinates, hji, hj]

theorem patchCoordinates_restore_insert {n : ℕ}
    (x y : Fin (n + 1) → U) (coordinates : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∉ coordinates) :
    Function.update (patchCoordinates x y coordinates) i (x i) =
      patchCoordinates x y coordinates := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [patchCoordinates, hi]
  · simp [Function.update, hji]

theorem retainedResidual_patch_bound {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hDeltaNonneg : 0 ≤ delta)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (selected coordinates : Finset (Fin (n + 1)))
    (hsub : coordinates ⊆ selected)
    (x y : Fin (n + 1) → U) :
    |retainedResidual q F selected (patchCoordinates x y coordinates) -
      retainedResidual q F selected x| ≤ coordinates.card * delta := by
  classical
  induction coordinates using Finset.induction_on with
  | empty => simp
  | @insert i coordinates hi ih =>
      have hiSelected : i ∈ selected := hsub (by simp)
      have hsub' : coordinates ⊆ selected := by
        intro j hj
        exact hsub (by simp [hj])
      have hstep := retainedResidual_coordinate_is_delta_insensitive q F delta
        hWeight hNorm hdelta selected i hiSelected (y i) (x i)
        (patchCoordinates x y coordinates)
      rw [← patchCoordinates_insert x y coordinates i hi,
        patchCoordinates_restore_insert x y coordinates i hi] at hstep
      have hind := ih hsub'
      have htriangle :
          |retainedResidual q F selected (patchCoordinates x y (insert i coordinates)) -
              retainedResidual q F selected x| ≤
            |retainedResidual q F selected (patchCoordinates x y (insert i coordinates)) -
              retainedResidual q F selected (patchCoordinates x y coordinates)| +
            |retainedResidual q F selected (patchCoordinates x y coordinates) -
              retainedResidual q F selected x| := by
        exact abs_sub_le _ _ _
      rw [Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
      nlinarith

end CIGAMF.P13.D6H3Exchange
