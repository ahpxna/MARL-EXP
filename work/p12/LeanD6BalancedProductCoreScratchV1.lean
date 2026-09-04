import Mathlib
import «LeanD6ProductCyclePathV1»

/-!
# D6 balanced-complement product-path core (scratch)

This file records the strongest currently justified product-reference bridge
for the remaining balanced-complement case of the D6 half-factor conjecture.

For an arbitrary ordered patch through selected coordinates, the retained
residual change is *exactly* a finite product-weighted sum of actual
`cycleFunctional` atoms.  Applying this to both active endpoints gives an
exact signed two-path cycle expansion.  Thus the old `2 d` patch budget is
not merely an absolute-value artefact: it is a genuine product-cycle filling
of mass `2 d`.

What this module deliberately does **not** claim is the missing one-free-unit
splice.  In the balanced complement case, obtaining mass `2 d - 1` requires
an additional signed aggregate identity between the two paths (or an
equivalent PAEC construction).  Neither global `hNorm` nor Top-C alone
currently supplies that identity in this file.

The constructions below use only the current product-weight assumptions and
the selected-coordinate path condition.  They do not use the stronger row
normalization premise from the older residual-centering API.
-/

namespace CIGAMF.P13.D6BalancedProductCoreScratch

open scoped BigOperators
open CIGAMF.V4.ProductSurrogate
open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6H3Exchange
open CIGAMF.P13.D6CycleDual
open CIGAMF.P13.D6ProductCyclePath

variable {U : Type*} [Fintype U] [Nonempty U]

/-- Apply the actions from `y` along an ordered coordinate list.  The tail is
patched first, so the recursive step is literally a selected-coordinate
`Function.update`, matching `retainedResidual_step_eq_cycle_average`. -/
def patchAlong {n : ℕ}
    (x y : Fin (n + 1) → U) : List (Fin (n + 1)) → Fin (n + 1) → U
  | [] => x
  | i :: is => Function.update (patchAlong x y is) i (y i)

/-- The product-weighted cycle expansion associated with `patchAlong`. -/
noncomputable def patchCycleAverage {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (x y : Fin (n + 1) → U) : List (Fin (n + 1)) → ℝ
  | [] => 0
  | i :: is =>
      productExpectation q (fun c ↦
        cycleFunctional i
          (Function.update (patchAlong x y is) i (y i))
          (Function.update c i ((patchAlong x y is) i)) F) +
        patchCycleAverage q F x y is

/-- A duplicate-free ordered patch has the literal coordinatewise form one
expects: `y` on its listed coordinates and `x` elsewhere. -/
theorem patchAlong_apply_of_nodup {n : ℕ}
    (x y : Fin (n + 1) → U)
    (order : List (Fin (n + 1)))
    (hNodup : order.Nodup) (j : Fin (n + 1)) :
    patchAlong x y order j = if j ∈ order then y j else x j := by
  induction order with
  | nil => simp [patchAlong]
  | cons i is ih =>
      simp only [List.nodup_cons] at hNodup
      have hi : i ∉ is := hNodup.1
      have htail : is.Nodup := hNodup.2
      by_cases hji : j = i
      · subst j
        simp [patchAlong, hi]
      · have hrec := ih htail
        simp [patchAlong, hji, hrec]

/-- An ordered list representing a finset gives the ordinary finset patch. -/
theorem patchAlong_eq_patchCoordinates_of_toFinset {n : ℕ}
    (x y : Fin (n + 1) → U)
    (order : List (Fin (n + 1)))
    (coordinates : Finset (Fin (n + 1)))
    (hNodup : order.Nodup)
    (hOrder : order.toFinset = coordinates) :
    patchAlong x y order = patchCoordinates x y coordinates := by
  funext j
  rw [patchAlong_apply_of_nodup x y order hNodup j]
  have hmem : j ∈ order ↔ j ∈ coordinates := by
    have h := congrArg (fun A : Finset (Fin (n + 1)) ↦ j ∈ A) hOrder
    simpa using h
  by_cases hj : j ∈ order
  · simp [patchCoordinates, hj, hmem.mp hj]
  · simp [patchCoordinates, hj, hmem.not.mp hj]

/-- Canonical sorting provides an always-available duplicate-free patch order
for a finite coordinate set. -/
noncomputable def canonicalPatchOrder {n : ℕ}
    (coordinates : Finset (Fin (n + 1))) : List (Fin (n + 1)) :=
  coordinates.sort (fun a b : Fin (n + 1) ↦ a ≤ b)

theorem canonicalPatchOrder_nodup {n : ℕ}
    (coordinates : Finset (Fin (n + 1))) :
    (canonicalPatchOrder coordinates).Nodup := by
  classical
  exact Finset.sort_nodup coordinates
    (fun a b : Fin (n + 1) ↦ a ≤ b)

theorem canonicalPatchOrder_toFinset {n : ℕ}
    (coordinates : Finset (Fin (n + 1))) :
    (canonicalPatchOrder coordinates).toFinset = coordinates := by
  classical
  exact Finset.sort_toFinset coordinates
    (fun a b : Fin (n + 1) ↦ a ≤ b)

theorem patchAlong_canonical_eq_patchCoordinates {n : ℕ}
    (x y : Fin (n + 1) → U)
    (coordinates : Finset (Fin (n + 1))) :
    patchAlong x y (canonicalPatchOrder coordinates) =
      patchCoordinates x y coordinates := by
  classical
  exact patchAlong_eq_patchCoordinates_of_toFinset x y
    (canonicalPatchOrder coordinates) coordinates
    (canonicalPatchOrder_nodup coordinates)
    (canonicalPatchOrder_toFinset coordinates)

/-- Exact product-reference expansion of one arbitrary selected-coordinate
patch path.  This is the reusable bridge from a path of residual updates to
actual D6 cycle atoms. -/
theorem retainedResidual_patchAlong_eq_cycleAverage {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1)))
    (x y : Fin (n + 1) → U)
    (order : List (Fin (n + 1)))
    (hSelected : ∀ i, i ∈ order → i ∈ selected)
    (hNorm : ∑ c, jointWeight q c = 1) :
    retainedResidual q F selected (patchAlong x y order) -
        retainedResidual q F selected x =
      patchCycleAverage q F x y order := by
  induction order with
  | nil => simp [patchAlong, patchCycleAverage]
  | cons i is ih =>
      have hi : i ∈ selected := hSelected i (by simp)
      have hTail : ∀ j, j ∈ is → j ∈ selected := by
        intro j hj
        exact hSelected j (by simp [hj])
      have hStep := retainedResidual_step_eq_cycle_average q F selected i hi
        (patchAlong x y is) (y i) hNorm
      have hInd := ih hTail
      change
        retainedResidual q F selected
            (Function.update (patchAlong x y is) i (y i)) -
            retainedResidual q F selected x =
          productExpectation q (fun c ↦
            cycleFunctional i
              (Function.update (patchAlong x y is) i (y i))
              (Function.update c i ((patchAlong x y is) i)) F) +
            patchCycleAverage q F x y is
      linarith

/-- The corresponding canonical-finset version.  No active-extremum or
Top-C assumption is needed for this exact identity. -/
theorem retainedResidual_patchCoordinates_eq_canonical_cycleAverage {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected coordinates : Finset (Fin (n + 1)))
    (hsub : coordinates ⊆ selected)
    (x y : Fin (n + 1) → U)
    (hNorm : ∑ c, jointWeight q c = 1) :
    retainedResidual q F selected (patchCoordinates x y coordinates) -
        retainedResidual q F selected x =
      patchCycleAverage q F x y (canonicalPatchOrder coordinates) := by
  classical
  rw [← patchAlong_canonical_eq_patchCoordinates x y coordinates]
  apply retainedResidual_patchAlong_eq_cycleAverage q F selected x y
    (canonicalPatchOrder coordinates)
  · intro i hi
    apply hsub
    have : i ∈ (canonicalPatchOrder coordinates).toFinset := by simpa using hi
    simpa [canonicalPatchOrder_toFinset] using this
  · exact hNorm

/-- One product-weighted actual cycle average has the expected `delta` bound.
Unlike the older residual API, this uses only the global product normalization
in addition to nonnegative weights. -/
theorem product_cycle_average_abs_le_delta {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta)
    (i : Fin (n + 1)) (z : Fin (n + 1) → U) (u : U) :
    |productExpectation q (fun c ↦
        cycleFunctional i (Function.update z i u)
          (Function.update c i (z i)) F)| ≤ delta := by
  unfold productExpectation
  calc
    |∑ c, jointWeight q c *
        cycleFunctional i (Function.update z i u)
          (Function.update c i (z i)) F| ≤
        ∑ c, |jointWeight q c *
          cycleFunctional i (Function.update z i u)
            (Function.update c i (z i)) F| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, jointWeight q c *
        |mixedDifference F i (Function.update z i u)
          (Function.update c i (z i))| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [abs_mul, cycleFunctional_eq_mixedDifference,
        abs_of_nonneg (hWeight c)]
    _ ≤ ∑ c, jointWeight q c * delta := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left
        (hdelta i (Function.update z i u)
          (Function.update c i (z i))) (hWeight c)
    _ = delta := by
      rw [← Finset.sum_mul, hNorm, one_mul]

/-- Absolute bound for an ordered selected-coordinate path, now derived from
its actual product-cycle expansion rather than supplied as a black-box patch
estimate. -/
theorem patchCycleAverage_abs_le_length_mul_delta {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (x y : Fin (n + 1) → U)
    (order : List (Fin (n + 1)))
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta) :
    |patchCycleAverage q F x y order| ≤ (order.length : ℝ) * delta := by
  induction order with
  | nil => simp [patchCycleAverage]
  | cons i is ih =>
      have hHead := product_cycle_average_abs_le_delta q F delta hWeight
        hNorm hdelta i (patchAlong x y is) (y i)
      have hTail := ih
      rw [patchCycleAverage]
      calc
        |productExpectation q (fun c ↦
            cycleFunctional i
              (Function.update (patchAlong x y is) i (y i))
              (Function.update c i ((patchAlong x y is) i)) F) +
            patchCycleAverage q F x y is| ≤
            |productExpectation q (fun c ↦
              cycleFunctional i
                (Function.update (patchAlong x y is) i (y i))
                (Function.update c i ((patchAlong x y is) i)) F)| +
              |patchCycleAverage q F x y is| := abs_add_le _ _
        _ ≤ delta + (is.length : ℝ) * delta := add_le_add hHead hTail
        _ = ((i :: is).length : ℝ) * delta := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring

/-- Signed two-endpoint product-cycle expansion.  This is the exact object
whose crude norm is `2 * |A| * delta` in the balanced-complement proof.
The upper path is reversed, hence its cycle average has a negative sign. -/
noncomputable def pairedEndpointCycleAverage {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (xplus p xminus m : Fin (n + 1) → U)
    (order : List (Fin (n + 1))) : ℝ :=
  -patchCycleAverage q F xplus p order +
    patchCycleAverage q F xminus m order

/-- Exact two-endpoint path identity.  In the intended balanced use,
`xplus`/`xminus` are active retained-residual extrema and `p`/`m` are
coordinatewise response extrema, but those facts are deliberately not needed
for the product-cycle algebra itself. -/
theorem pairedEndpointPatch_eq_pairedEndpointCycleAverage {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected : Finset (Fin (n + 1)))
    (xplus p xminus m : Fin (n + 1) → U)
    (order : List (Fin (n + 1)))
    (hSelected : ∀ i, i ∈ order → i ∈ selected)
    (hNorm : ∑ c, jointWeight q c = 1) :
    (retainedResidual q F selected xplus -
        retainedResidual q F selected (patchAlong xplus p order)) +
      (retainedResidual q F selected (patchAlong xminus m order) -
        retainedResidual q F selected xminus) =
      pairedEndpointCycleAverage q F xplus p xminus m order := by
  have hUpper := retainedResidual_patchAlong_eq_cycleAverage q F selected
    xplus p order hSelected hNorm
  have hLower := retainedResidual_patchAlong_eq_cycleAverage q F selected
    xminus m order hSelected hNorm
  unfold pairedEndpointCycleAverage
  linarith

/-- The exact two-path cycle expansion has the crude `2 * length * delta`
norm bound.  This is the certified product-reference version of the two
endpoint patch budget.  A sharp balanced proof must improve this *aggregate*
bound by one unit; it cannot obtain that improvement merely by applying this
lemma coordinate-by-coordinate. -/
theorem pairedEndpointCycleAverage_abs_le_two_length_mul_delta {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (xplus p xminus m : Fin (n + 1) → U)
    (order : List (Fin (n + 1)))
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta) :
    |pairedEndpointCycleAverage q F xplus p xminus m order| ≤
      2 * (order.length : ℝ) * delta := by
  have hUpper := patchCycleAverage_abs_le_length_mul_delta q F delta
    xplus p order hWeight hNorm hdelta
  have hLower := patchCycleAverage_abs_le_length_mul_delta q F delta
    xminus m order hWeight hNorm hdelta
  unfold pairedEndpointCycleAverage
  calc
    |-patchCycleAverage q F xplus p order +
        patchCycleAverage q F xminus m order| ≤
        |-patchCycleAverage q F xplus p order| +
          |patchCycleAverage q F xminus m order| := abs_add_le _ _
    _ = |patchCycleAverage q F xplus p order| +
          |patchCycleAverage q F xminus m order| := by rw [abs_neg]
    _ ≤ (order.length : ℝ) * delta + (order.length : ℝ) * delta :=
      add_le_add hUpper hLower
    _ = 2 * (order.length : ℝ) * delta := by ring

/-- Canonical finite-set form of the exact two-endpoint bridge.  This is the
form used by the active-extrema construction with
`coordinates = selected \\ competitor`. -/
theorem pairedEndpointPatch_eq_canonical_cycleAverage {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ)
    (selected coordinates : Finset (Fin (n + 1)))
    (hsub : coordinates ⊆ selected)
    (xplus p xminus m : Fin (n + 1) → U)
    (hNorm : ∑ c, jointWeight q c = 1) :
    (retainedResidual q F selected xplus -
        retainedResidual q F selected
          (patchCoordinates xplus p coordinates)) +
      (retainedResidual q F selected
          (patchCoordinates xminus m coordinates) -
        retainedResidual q F selected xminus) =
      pairedEndpointCycleAverage q F xplus p xminus m
        (canonicalPatchOrder coordinates) := by
  rw [← patchAlong_canonical_eq_patchCoordinates xplus p coordinates,
    ← patchAlong_canonical_eq_patchCoordinates xminus m coordinates]
  apply pairedEndpointPatch_eq_pairedEndpointCycleAverage q F selected
    xplus p xminus m (canonicalPatchOrder coordinates)
  · intro i hi
    apply hsub
    have : i ∈ (canonicalPatchOrder coordinates).toFinset := by simpa using hi
    simpa [canonicalPatchOrder_toFinset] using this
  · exact hNorm

/-- The canonical finset two-endpoint path has mass at most twice the number
of patched coordinates.  In a balanced complement comparison this is the
literal `2d` product-cycle budget whose missing reduction to `2d-1` is OFU. -/
theorem pairedEndpointPatch_canonical_abs_le_two_card_mul_delta {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (coordinates : Finset (Fin (n + 1)))
    (xplus p xminus m : Fin (n + 1) → U)
    (hWeight : ∀ c, 0 ≤ jointWeight q c)
    (hNorm : ∑ c, jointWeight q c = 1)
    (hdelta : ∀ (i : Fin (n + 1)) (x c : Fin (n + 1) → U),
      |mixedDifference F i x c| ≤ delta) :
    |pairedEndpointCycleAverage q F xplus p xminus m
        (canonicalPatchOrder coordinates)| ≤
      2 * (coordinates.card : ℝ) * delta := by
  have h := pairedEndpointCycleAverage_abs_le_two_length_mul_delta q F delta
    xplus p xminus m (canonicalPatchOrder coordinates) hWeight hNorm hdelta
  rw [show (canonicalPatchOrder coordinates).length = coordinates.card by
    exact Finset.length_sort (s := coordinates)
      (fun a b : Fin (n + 1) ↦ a ≤ b)] at h
  exact h

/-- Explicit statement of the remaining balanced product-reference gap.  A
proof of this predicate from active extrema, Top-C, and product consistency
would be the desired one-free-unit splice; this file does not assume it in
any headline theorem. -/
def OneFreeProductCycleSplice {n : ℕ}
    (q : Fin (n + 1) → U → ℝ)
    (F : (Fin (n + 1) → U) → ℝ) (delta : ℝ)
    (coordinates : Finset (Fin (n + 1)))
    (xplus p xminus m : Fin (n + 1) → U) : Prop :=
  pairedEndpointCycleAverage q F xplus p xminus m
      (canonicalPatchOrder coordinates) ≤
    (2 * (coordinates.card : ℝ) - 1) * delta

end CIGAMF.P13.D6BalancedProductCoreScratch
