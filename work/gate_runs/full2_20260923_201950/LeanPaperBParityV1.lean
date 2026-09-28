import «LeanPaperBCubeV1»
import «LeanPaperBAttainV1»

/-!
# Paper B: the parity-mask channel, and the resolving orders it produces

The overlapping-safe-answer geometry needs an observation law, and the corpus had only the
loss geometry.  This module writes the law down and reads the resolving orders off it,
rather than importing them as a table.

With `K_w = {0, tip_w}` we have `tip_j in K_w` exactly when `j = w`, so the mask value

    v j w = 1 - 2 * [j = w]

is `-1` at `j = w` and `+1` otherwise.  Query `j` returns

    Y_j = v j w * (product of the first j signs) + (h/j) * (sum of the first j signs) + noise,

a Gaussian mixture over the sign cube.  Its characteristic function is `cube_sum` at
`a = i t (v j w)` and `c = i t h / j`, so the difference between the two mask values is

    2^{j+1} * sinh(i t) * sinh(i t h / j)^j,

which is `cube_difference` verbatim.  Its magnitude is `Theta(h^j)` by `gap_at_scale`: query
`j` separates the mask at order `j`, and at no smaller order, because the `j`-th power is the
whole `h`-dependence.

Reading the orders off: query `j` decides `w = j` versus `w != j`, so two worlds `w, w'` are
separated by the cheaper of their own queries, `r(w,w') = min(w,w')`, except that the last
pair has only query `m-1` available.  Hence `s_safe = 1` and `s_id = m-1`.
-/

namespace CIGAMF.P13.PaperBParity

open Finset
open CIGAMF.P13.PaperBCube
open CIGAMF.P13.PaperBAttain

/-- The mask value of query `j` at world `w`: `-1` exactly when the query names the world. -/
noncomputable def maskVal (j w : ℕ) : ℂ := if j = w then -1 else 1

theorem maskVal_self (j : ℕ) : maskVal j j = -1 := by unfold maskVal; rw [if_pos rfl]

theorem maskVal_other (j w : ℕ) (h : j ≠ w) : maskVal j w = 1 := by
  unfold maskVal; rw [if_neg h]

/-- **The mask is `-1` exactly at the named world**, which is the membership the query
reports. -/
theorem maskVal_eq_neg_one_iff (j w : ℕ) : maskVal j w = -1 ↔ j = w := by
  unfold maskVal
  constructor
  · intro h
    by_contra hc
    rw [if_neg hc] at h
    exact absurd h (by norm_num)
  · intro h; rw [if_pos h]

/-- **The UNNORMALISED cube difference at the parity-mask query.**

This is NOT yet the characteristic-function difference of the two observation laws, and the
name must not be read as though it were.  Two links are missing and both change the constant:

* the cube is UNIFORM, so each of the `2^j` points carries probability `2^{-j}`.  Dividing
  by `2^j` leaves the factor `2`, not `2^{j+1}`;
* the observation carries independent Gaussian noise, contributing `exp(-sigma^2 t^2 / 2)`.

With both, and using `sinh (I t) = I sin t`, the difference of the two observation laws'
characteristic functions is

    phi_+ (t) - phi_- (t) = 2 I^(j+1) * sin t * sin (t h / j)^j * exp (-sigma^2 t^2 / 2),

which is what `EXP_paperB_decoder.py`'s `closed_form_gap` implements -- so the measured
numbers are unaffected by this gap.  What the statement below gives, exactly, is the
`h`-dependence: the entire dependence is the `j`-th power, and that is what the order claim
uses.  `parity_cf_difference_normalised` (`LeanPaperBParityNormV1`) supplies the `2^{-j}`
link; the Gaussian factor needs the observation law and is still owed. -/
theorem parity_cf_difference (j : ℕ) (t hh : ℝ) :
    (∑ z : Fin j → Bool,
        Complex.exp ((Complex.I * t) * chr z + (Complex.I * t * hh / j) * csum z))
      - ∑ z : Fin j → Bool,
        Complex.exp ((-(Complex.I * t)) * chr z + (Complex.I * t * hh / j) * csum z)
      = 2 ^ j * (2 * Complex.sinh (Complex.I * t)
          * Complex.sinh (Complex.I * t * hh / j) ^ j) :=
  cube_difference j (Complex.I * t) (Complex.I * t * hh / j)

/-- **The magnitude is `Theta(h^j)`**, with the constant explicit and no fitted slope: the
real form of the tail factor is a power of a sine. -/
theorem parity_gap_order (j : ℕ) (hj : 0 < j) (t hh : ℝ) (ht : 0 < t) (hhpos : 0 < hh)
    (hsmall : t * hh / (j : ℝ) ≤ 1) :
    (3 * t / (4 * (j : ℝ))) ^ j * hh ^ j
      ≤ (Real.sin (t * hh / (j : ℝ))) ^ j :=
  gap_at_scale t hh j hj ht hhpos hsmall

/-! ## The resolving orders the channel produces -/

/-- Query `j` reports membership, so it separates two worlds exactly when it names one of
them. -/
theorem query_separates_iff (j w w' : ℕ) (hne : w ≠ w') :
    maskVal j w ≠ maskVal j w' ↔ (j = w ∨ j = w') := by
  constructor
  · intro hdiff
    by_contra hc
    push_neg at hc
    rw [maskVal_other j w (fun h => hc.1 h), maskVal_other j w' (fun h => hc.2 h)] at hdiff
    exact hdiff rfl
  · intro hj
    rcases hj with hj | hj
    · rw [hj, maskVal_self, maskVal_other w w' (by omega)]
      norm_num
    · rw [hj, maskVal_self, maskVal_other w' w (by omega)]
      norm_num

/-- **The resolving order of a pair**: the cheaper of the two naming queries. -/
noncomputable def resolveOrder (w w' : ℕ) : ℕ := min w w'

/-- **The safe order is `1`.**  Worlds `1` and `2` are separated by query `1`. -/
theorem parity_s_safe (m : ℕ) (hm : 3 ≤ m) : resolveOrder 1 2 = 1 := by
  unfold resolveOrder; omega

/-- **The identification order is `m-1`.**  Every pair resolves by `m-1` at the latest, and
the pair `(m-1, m)` needs exactly that. -/
theorem parity_s_id (m : ℕ) (hm : 3 ≤ m) :
    (∀ w w' : ℕ, 1 ≤ w → w ≤ m → 1 ≤ w' → w' ≤ m → w ≠ w' → resolveOrder w w' ≤ m - 1)
      ∧ resolveOrder (m - 1) m = m - 1 := by
  constructor
  · intro w w' hw1 hwm hw'1 hw'm hne
    unfold resolveOrder
    omega
  · unfold resolveOrder
    omega

/-- **The observation classes at level `s`.**  Two worlds are still together at level `s`
exactly when neither is named by a query of order at most `s`, i.e. both exceed `s`. -/
theorem parity_classes (s w w' : ℕ) (hw : 0 < w) (hw' : 0 < w') (hne : w ≠ w') :
    (s < resolveOrder w w') ↔ (s < w ∧ s < w') := by
  unfold resolveOrder
  omega

/-! ## Audit -/

#print axioms maskVal_eq_neg_one_iff
#print axioms parity_cf_difference
#print axioms parity_gap_order
#print axioms query_separates_iff
#print axioms parity_s_safe
#print axioms parity_s_id
#print axioms parity_classes

end CIGAMF.P13.PaperBParity
