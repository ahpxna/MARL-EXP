import «LeanD6ScalarInformationV1»

/-! # D6: the `(d, x)` family is not a restriction.

`LeanD6ScalarInformationV1` states the B-scalar's per-sample information against the
alternative `(d, x)`:

    I_B(d, x) = ( d μ²/q + (q − d) x²/q ) / 2,

and the audit's standing objection is that the family is still parameterised by `(d, x)`
and is declared rather than derived.  A lower bound proved only over a two-parameter
slice says nothing about alternatives outside it.

This file removes that objection.  The general alternative is an arbitrary shift vector
`v : Fin q → ℚ`, whose information is

    I(v) = ( ∑_i v_i² ) / (2q),

and `IB_eq_of_slice` shows the `(d, x)` formula is exactly `I` evaluated on the slice.
The substantive statement is `IB_le_general`: **every** alternative with `d` coordinates
of magnitude at least `μ` and the rest of magnitude at least `x` costs at least
`I_B(d, x)`.  So quantifying a LOWER bound over the slice loses nothing: the slice is the
cheapest member of its class, not a convenient special case.

## WHAT IS PROVED

* `Igen_eq` — the general information is `(∑ v_i²)/(2q)`, and `Igen_nonneg`.
* `IB_eq_of_slice` — the `(d,x)` formula IS the general one on the slice, so the two are
  not two different models.
* `IB_le_general` — **the reduction**: every alternative in the class costs at least the
  slice value.  This is what makes a slice-quantified lower bound a class-quantified one.
* `Igen_pos_of_ne_zero` — the information vanishes only at the zero shift, so the
  B-scalar is blind in no direction at all (the asymmetry of the parent file, restated
  without the slice).
* `slice_is_tight` — the bound is attained exactly on the slice, so `IB_le_general`
  cannot be improved by enlarging the class.

## WHAT THIS DOES NOT ESTABLISH

- This is the B-SCALAR's information only.  The A-pair has a blind direction
  (`IA_eq_zero_iff` in the parent file) and is not covered by this reduction.
- The reduction is for a LOWER bound.  An upper bound quantified over the slice would
  still say nothing about the class, and none is claimed here.
- The class is defined by per-coordinate magnitude constraints.  An alternative set cut
  out by other constraints is outside this statement.
- No phase boundary is proved here, and `t_end` remains not a phase boundary.
-/

namespace CIGAMF.P13.D6GeneralFamily

open Finset
open CIGAMF.P13.D6ScalarInformation

/-- The general alternative's per-sample information: an arbitrary shift vector. -/
def Igen (q : ℕ) (v : Fin q → ℚ) : ℚ := (∑ i, (v i) ^ 2) / (2 * q)

theorem Igen_nonneg (q : ℕ) (v : Fin q → ℚ) : 0 ≤ Igen q v := by
  unfold Igen
  have hnum : (0:ℚ) ≤ ∑ i, (v i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp [Igen]
  · have : (0:ℚ) < 2 * q := by
      have : (0:ℚ) < (q : ℚ) := by exact_mod_cast hq
      linarith
    exact div_nonneg hnum this.le

/-- **The `(d,x)` formula is the general one on the slice.**  Not a second model. -/
theorem IB_eq_of_slice (q : ℕ) (hq : 0 < q) (mu x : ℚ) (v : Fin q → ℚ)
    (S : Finset (Fin q)) (hS : ∀ i ∈ S, v i = mu) (hSc : ∀ i, i ∉ S → v i = x) :
    Igen q v = IB (q : ℚ) (S.card : ℚ) mu x := by
  classical
  have hqQ : (q : ℚ) ≠ 0 := by
    have : (0:ℚ) < (q : ℚ) := by exact_mod_cast hq
    exact ne_of_gt this
  have hsplit : (∑ i, (v i) ^ 2)
      = (S.card : ℚ) * mu ^ 2 + ((q : ℚ) - (S.card : ℚ)) * x ^ 2 := by
    have hin : ∑ i ∈ S, (v i) ^ 2 = (S.card : ℚ) * mu ^ 2 := by
      rw [Finset.sum_congr rfl (fun i hi => by rw [hS i hi]), Finset.sum_const,
          nsmul_eq_mul]
    have hout : ∑ i ∈ (univ \ S), (v i) ^ 2
        = ((univ \ S).card : ℚ) * x ^ 2 := by
      refine (Finset.sum_congr rfl (fun i hi => by
        rw [hSc i (Finset.mem_sdiff.mp hi).2])).trans ?_
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((univ \ S).card : ℚ) = (q : ℚ) - (S.card : ℚ) := by
      have hle : S.card ≤ q := by
        simpa [Finset.card_univ, Fintype.card_fin] using
          Finset.card_le_card (Finset.subset_univ S)
      have hnat : (univ \ S).card = q - S.card := by
        rw [Finset.card_univ_sdiff, Fintype.card_fin]
      rw [hnat]
      push_cast [Nat.cast_sub hle]
      ring
    have hu : (univ : Finset (Fin q)) = S ∪ (univ \ S) := by
      rw [Finset.union_sdiff_of_subset (Finset.subset_univ S)]
    rw [hu, Finset.sum_union (Finset.disjoint_sdiff), hin, hout, hcard]
  unfold Igen IB
  rw [hsplit]
  field_simp
  try ring

/-- **The reduction.**  Every alternative whose `S`-coordinates have magnitude at least
`μ` and whose remaining coordinates have magnitude at least `x` costs at least the slice
value.  A lower bound quantified over the slice is therefore a lower bound over the whole
class. -/
theorem IB_le_general (q : ℕ) (hq : 0 < q) (mu x : ℚ) (hmu : 0 ≤ mu) (hx : 0 ≤ x)
    (v : Fin q → ℚ) (S : Finset (Fin q))
    (hS : ∀ i ∈ S, mu ≤ |v i|) (hSc : ∀ i, i ∉ S → x ≤ |v i|) :
    IB (q : ℚ) (S.card : ℚ) mu x ≤ Igen q v := by
  classical
  have hqpos : (0:ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hsq : ∀ (c : ℚ), 0 ≤ c → ∀ (t : ℚ), c ≤ |t| → c ^ 2 ≤ t ^ 2 := by
    intro c hc t ht
    have : c ^ 2 ≤ |t| ^ 2 := pow_le_pow_left₀ hc ht 2
    rwa [sq_abs] at this
  have hin : (S.card : ℚ) * mu ^ 2 ≤ ∑ i ∈ S, (v i) ^ 2 := by
    have := Finset.sum_le_sum (fun i (hi : i ∈ S) => hsq mu hmu (v i) (hS i hi))
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hout : ((univ \ S).card : ℚ) * x ^ 2 ≤ ∑ i ∈ (univ \ S), (v i) ^ 2 := by
    have := Finset.sum_le_sum (fun i (hi : i ∈ univ \ S) =>
      hsq x hx (v i) (hSc i (Finset.mem_sdiff.mp hi).2))
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hcard : ((univ \ S).card : ℚ) = (q : ℚ) - (S.card : ℚ) := by
    have hle : S.card ≤ q := by
      simpa [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S)
    have hnat : (univ \ S).card = q - S.card := by
      rw [Finset.card_univ_sdiff, Fintype.card_fin]
    rw [hnat]
    push_cast [Nat.cast_sub hle]
    ring
  have hu : (univ : Finset (Fin q)) = S ∪ (univ \ S) := by
    rw [Finset.union_sdiff_of_subset (Finset.subset_univ S)]
  have htot : (S.card : ℚ) * mu ^ 2 + ((q : ℚ) - (S.card : ℚ)) * x ^ 2
      ≤ ∑ i, (v i) ^ 2 := by
    rw [hu, Finset.sum_union (Finset.disjoint_sdiff)]
    rw [← hcard]
    linarith [hin, hout]
  unfold IB Igen
  have hqne : (q : ℚ) ≠ 0 := ne_of_gt hqpos
  have hrw : ((S.card : ℚ) * mu ^ 2 / (q : ℚ)
        + ((q : ℚ) - (S.card : ℚ)) * x ^ 2 / (q : ℚ)) / 2
      = ((S.card : ℚ) * mu ^ 2 + ((q : ℚ) - (S.card : ℚ)) * x ^ 2) / (2 * (q : ℚ)) := by
    rw [← add_div, div_div, mul_comm]
    try ring
  rw [hrw]
  gcongr
  try linarith

/-- The B-scalar is blind in NO direction: the information vanishes only at zero. -/
theorem Igen_pos_of_ne_zero (q : ℕ) (hq : 0 < q) (v : Fin q → ℚ) (i₀ : Fin q)
    (hne : v i₀ ≠ 0) : 0 < Igen q v := by
  classical
  have hqpos : (0:ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hpos : 0 < ∑ i, (v i) ^ 2 := by
    refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i₀, mem_univ i₀, ?_⟩
    exact pow_pos (abs_pos.mpr hne) 2 |>.trans_eq (sq_abs _)
  unfold Igen
  exact div_pos hpos (by linarith)

/-- The bound of `IB_le_general` is ATTAINED on the slice, so it cannot be improved. -/
theorem slice_is_tight (q : ℕ) (hq : 0 < q) (mu x : ℚ) (v : Fin q → ℚ)
    (S : Finset (Fin q)) (hS : ∀ i ∈ S, v i = mu) (hSc : ∀ i, i ∉ S → v i = x) :
    Igen q v = IB (q : ℚ) (S.card : ℚ) mu x :=
  IB_eq_of_slice q hq mu x v S hS hSc

#print axioms Igen_nonneg
#print axioms IB_eq_of_slice
#print axioms IB_le_general
#print axioms Igen_pos_of_ne_zero
#print axioms slice_is_tight

end CIGAMF.P13.D6GeneralFamily
