import Mathlib

/-!
# The price of uniform retention survives relaxation of the marginal constraint.

## WHY THIS MODULE EXISTS

The corpus proves an exact value for the constrained optimum `V_avg^unif` when the
retained marginals are EXACTLY uniform, and the odd-size price over the free optimum
grows linearly in `m`.  A natural objection is that this is an artefact of an exact
constraint: real retention rules are only approximately uniform, and an exact equality
constraint can be arbitrarily expensive without that expense meaning anything.

This file answers the objection.  Relax the constraint to a band,

    |Pr(i in the first k) - k/m| <= eta/m   for every labelled item i and every k,

and the lower bound degrades only LINEARLY in `eta`:

    V_avg^(eta) >= (m + 3 - (m+1) eta) / (m (m+4))      (m odd).

At `eta = 0` this is the proved uniform value, and for any fixed `eta < 1` the numerator
is still `Theta(m)`, so `V^(eta) = Omega(1/m)` against the free `Theta(1/m^2)`: the
linear-in-`m` price is not an artefact of exactness.

## THE ARGUMENT

Only the budget `k = m-1` is used, where the parity correction vanishes.  There the loss
is determined by which item is LAST, and the band constraint at `k = m-1` says exactly
that the last-position distribution lies within `eta/m` of uniform.  So the whole problem
reduces to: minimise `sum_i pi_i c_i` over a distribution `pi` in a band around uniform.

The bound is then a CENTRING argument, and the centre matters.  Because `sum_i (pi_i -
1/m) = 0`, the deviation term may be measured against any constant, and choosing the
constant `2` makes the total absolute deviation of the coefficients exactly `m+1` --
smaller than against `0`, which would give the weaker `m+3`.

## WHAT IS PROVED

* `band_expectation_lower_bound` -- the centring bound, for an arbitrary coefficient
  vector, an arbitrary band and an arbitrary centre.  This is the reusable content.
* `coef_eq` -- the last-position loss coefficients are `|total - weight|`, DERIVED from
  the family's weights rather than tabulated.
* `total_eq_neg_one` -- the family sums to `-1` when `p = q+1`, i.e. for odd `m`.
* `sum_coef` -- `sum_i c_i = m+3`.
* `sum_abs_coef_sub_two` -- `sum_i |c_i - 2| = m+1`: the centring constant that makes the
  bound as strong as it is.
* `relaxed_expected_defect_lower_bound` -- the two combined: the expected defect at budget
  `m-1` is at least `(m + 3 - (m+1) eta)/m`.
* `relaxed_value_lower_bound` -- divided by `D = m+4`, the stated bound on `V_avg^(eta)`.
* `relaxed_bound_is_linear_in_m` -- for `eta <= eta0 < 1` the bound is at least
  `(1 - eta0)/(m+4)`, which is the `Omega(1/m)` claim.

## WHAT THIS DOES NOT ESTABLISH

- **This is a lower bound only.**  The matching construction is the exactly-uniform one,
  which is feasible for every `eta >= 0`, so the frontier is pinned between this bound and
  `V^unif`; nothing here computes the frontier itself.
- **The bound is NOT tight near its own zero.**  It degrades to zero at
  `eta = (m+3)/(m+1) > 1`, but the LP frontier computed in
  `scripts/EXP_unified_structural_frontier.py` shows the separation actually dies earlier
  and at an exactly reproducible place: the optimum meets the free value at `eta = 1` for
  odd `m` (checked at `m = 5,7,9,11`) and at `(m-2)/(2(m-1))` for even `m` (checked at
  `m = 6,8,10`).  Those breakpoints are EMPIRICAL -- solved, not proved -- and this module
  proves neither of them.  In particular `eta = 1` must not be read off this bound as a
  sharp threshold; the bound is still positive there.
- Odd `m` only.  The even case has a different coefficient profile and is not treated.
- The reduction to budget `m-1` discards every other budget, so the bound is not claimed
  to be the best obtainable from the full constraint system.
-/

set_option maxHeartbeats 1000000

namespace CIGAMF.P13.UnifiedStructuralRelaxed

open Finset

/-! ### The centring bound -/

/-- **A distribution confined to a band around uniform cannot push its expectation far
below the uniform value.**  The deviation is measured against an arbitrary centre, which
is legitimate because the deviations sum to zero, and the centre is what makes the bound
sharp in the application. -/
theorem band_expectation_lower_bound {I : Type*} [Fintype I]
    (c pi : I → ℝ) (m eta center : ℝ) (hm : 0 < m)
    (hsum : ∑ i, pi i = 1)
    (hband : ∀ i, |pi i - 1 / m| ≤ eta / m)
    (hcard : (Fintype.card I : ℝ) = m) :
    (∑ i, c i) / m - (eta / m) * (∑ i, |c i - center|) ≤ ∑ i, pi i * c i := by
  classical
  have hmne : m ≠ 0 := ne_of_gt hm
  -- the deviations sum to zero
  have hdev : ∑ i, (pi i - 1 / m) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      hcard]
    field_simp
    norm_num
  -- so the expectation may be re-centred at will
  have hexp : ∑ i, (pi i - 1 / m) * (c i - center)
      = (∑ i, pi i * c i) - (1 / m) * (∑ i, c i)
        - center * ∑ i, (pi i - 1 / m) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsplit : (∑ i, pi i * c i) - (∑ i, c i) / m
      = ∑ i, (pi i - 1 / m) * (c i - center) := by
    rw [hexp, hdev, mul_zero, sub_zero, one_div_mul_eq_div]
  -- and each term is controlled by the band
  have hterm : ∀ i : I,
      -((eta / m) * |c i - center|) ≤ (pi i - 1 / m) * (c i - center) := by
    intro i
    have h1 : |(pi i - 1 / m) * (c i - center)| ≤ (eta / m) * |c i - center| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hband i) (abs_nonneg _)
    have h2 := neg_abs_le ((pi i - 1 / m) * (c i - center))
    linarith
  have hsumterm : -((eta / m) * ∑ i, |c i - center|)
      ≤ ∑ i, (pi i - 1 / m) * (c i - center) := by
    have hneg : -((eta / m) * ∑ i, |c i - center|)
        = ∑ i, -((eta / m) * |c i - center|) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hneg]
    exact Finset.sum_le_sum fun i _ => hterm i
  linarith [hsplit, hsumterm]

/-! ### The structural family at odd size -/

/-- The items of the family: one of weight `-3`, `p` of weight `-1`, `q` of weight `+1`,
one of weight `+3`.  The size is `m = 2 + p + q`, and odd `m` is `p = q + 1`. -/
abbrev Item (p q : ℕ) : Type := Unit ⊕ (Fin p ⊕ (Fin q ⊕ Unit))

/-- The weight of an item. -/
def weight {p q : ℕ} : Item p q → ℝ
  | Sum.inl _ => -3
  | Sum.inr (Sum.inl _) => -1
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

/-- The total weight of the family. -/
noncomputable def total (p q : ℕ) : ℝ := ∑ i : Item p q, weight i

theorem card_item (p q : ℕ) : (Fintype.card (Item p q) : ℝ) = 2 + p + q := by
  simp [Item, Fintype.card_sum]; ring

/-- **The family sums to `-1` exactly when `p = q + 1`**, which is the odd-size case. -/
theorem total_eq_neg_one {p q : ℕ} (hpq : p = q + 1) : total p q = -1 := by
  subst hpq; simp [total, Fintype.sum_sum_type, weight]

/-- The last-position loss coefficient.  At budget `m-1`, which is even for odd `m`, the
parity correction vanishes and the retained sum is the total minus the last item's weight,
so the defect is `|total - weight|`.  This is DERIVED from the weights; no table of
coefficients is assumed anywhere. -/
noncomputable def coef {p q : ℕ} (i : Item p q) : ℝ := |total p q - weight i|

/-- The four coefficient values: `2` for the `-3` item, `0` for each `-1` item, `2` for
each `+1` item, `4` for the `+3` item. -/
theorem coef_values {p q : ℕ} (hpq : p = q + 1) :
    (coef (p := p) (q := q) (Sum.inl ()) = 2)
    ∧ (∀ a : Fin p, coef (p := p) (q := q) (Sum.inr (Sum.inl a)) = 0)
    ∧ (∀ b : Fin q, coef (p := p) (q := q) (Sum.inr (Sum.inr (Sum.inl b))) = 2)
    ∧ (coef (p := p) (q := q) (Sum.inr (Sum.inr (Sum.inr ()))) = 4) := by
  refine ⟨?_, fun a => ?_, fun b => ?_, ?_⟩ <;>
    simp [coef, total_eq_neg_one hpq, weight] <;> norm_num

/-- **The coefficients sum to `m + 3`.** -/
theorem sum_coef {p q : ℕ} (hpq : p = q + 1) :
    ∑ i : Item p q, coef i = (2 + (p : ℝ) + q) + 3 := by
  unfold coef
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [total_eq_neg_one hpq, weight]
  subst hpq; push_cast; ring

/-- **Centred at `2`, the total absolute deviation is `m + 1`.**  Centring at `0` would
give `m + 3`, a strictly weaker bound; this choice is where the strength comes from. -/
theorem sum_abs_coef_sub_two {p q : ℕ} (hpq : p = q + 1) :
    ∑ i : Item p q, |coef i - 2| = (2 + (p : ℝ) + q) + 1 := by
  unfold coef
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [total_eq_neg_one hpq, weight]
  subst hpq; push_cast; ring

/-! ### The relaxed bound -/

/-- **The expected defect at the last budget, under a relaxed marginal band.** -/
theorem relaxed_expected_defect_lower_bound {p q : ℕ} (hpq : p = q + 1)
    (eta : ℝ) (pi : Item p q → ℝ)
    (hsum : ∑ i, pi i = 1)
    (hband : ∀ i, |pi i - 1 / (2 + (p : ℝ) + q)| ≤ eta / (2 + (p : ℝ) + q)) :
    ((2 + (p : ℝ) + q) + 3 - ((2 + (p : ℝ) + q) + 1) * eta) / (2 + (p : ℝ) + q)
      ≤ ∑ i, pi i * coef i := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hmpos : (0 : ℝ) < 2 + (p : ℝ) + q := by linarith
  have h := band_expectation_lower_bound (I := Item p q) coef pi
    (2 + (p : ℝ) + q) eta 2 hmpos hsum hband (card_item p q)
  rw [sum_coef hpq, sum_abs_coef_sub_two hpq] at h
  have hrw : ((2 + (p : ℝ) + q) + 3 - ((2 + (p : ℝ) + q) + 1) * eta) / (2 + (p : ℝ) + q)
      = ((2 + (p : ℝ) + q) + 3) / (2 + (p : ℝ) + q)
        - (eta / (2 + (p : ℝ) + q)) * ((2 + (p : ℝ) + q) + 1) := by
    field_simp
  rw [hrw]
  exact h

/-- **The bound on the constrained value**, after normalising by `D = m + 4`. -/
theorem relaxed_value_lower_bound {p q : ℕ} (hpq : p = q + 1)
    (eta : ℝ) (pi : Item p q → ℝ)
    (hsum : ∑ i, pi i = 1)
    (hband : ∀ i, |pi i - 1 / (2 + (p : ℝ) + q)| ≤ eta / (2 + (p : ℝ) + q)) :
    ((2 + (p : ℝ) + q) + 3 - ((2 + (p : ℝ) + q) + 1) * eta)
        / ((2 + (p : ℝ) + q) * ((2 + (p : ℝ) + q) + 4))
      ≤ (∑ i, pi i * coef i) / ((2 + (p : ℝ) + q) + 4) := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  have hq : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hmpos : (0 : ℝ) < 2 + (p : ℝ) + q := by linarith
  have hD : (0 : ℝ) < (2 + (p : ℝ) + q) + 4 := by linarith
  have h := relaxed_expected_defect_lower_bound hpq eta pi hsum hband
  have hrw : ((2 + (p : ℝ) + q) + 3 - ((2 + (p : ℝ) + q) + 1) * eta)
        / ((2 + (p : ℝ) + q) * ((2 + (p : ℝ) + q) + 4))
      = (((2 + (p : ℝ) + q) + 3 - ((2 + (p : ℝ) + q) + 1) * eta) / (2 + (p : ℝ) + q))
        / ((2 + (p : ℝ) + q) + 4) := by
    field_simp
  rw [hrw]
  gcongr

/-- **At any fixed band below one, the bound is still of order `1/m`.**  The free optimum
is of order `1/m^2`, so the linear-in-`m` price is not an artefact of exactness. -/
theorem relaxed_bound_is_linear_in_m (m eta eta0 : ℝ)
    (hm : 0 < m) (heta : 0 ≤ eta) (hle : eta ≤ eta0) (hlt : eta0 < 1) :
    (1 - eta0) / (m + 4) ≤ (m + 3 - (m + 1) * eta) / (m * (m + 4)) := by
  have hD : (0 : ℝ) < m + 4 := by linarith
  have hpos : (0 : ℝ) < m * (m + 4) := by positivity
  have hnum : 0 ≤ m + 3 - (m + 1) * eta - m * (1 - eta0) := by
    nlinarith [mul_le_mul_of_nonneg_left hle (by linarith : (0:ℝ) ≤ m + 1)]
  have key : (m + 3 - (m + 1) * eta) / (m * (m + 4)) - (1 - eta0) / (m + 4)
      = (m + 3 - (m + 1) * eta - m * (1 - eta0)) / (m * (m + 4)) := by
    field_simp
  have hdiv : 0 ≤ (m + 3 - (m + 1) * eta - m * (1 - eta0)) / (m * (m + 4)) :=
    div_nonneg hnum (le_of_lt hpos)
  linarith [key, hdiv]

#print axioms band_expectation_lower_bound
#print axioms total_eq_neg_one
#print axioms coef_values
#print axioms sum_coef
#print axioms sum_abs_coef_sub_two
#print axioms relaxed_expected_defect_lower_bound
#print axioms relaxed_value_lower_bound
#print axioms relaxed_bound_is_linear_in_m

end CIGAMF.P13.UnifiedStructuralRelaxed
