import «LeanPaperCRearrangeV1»

/-!
# Paper C: the insertion mixture's marginals, and the breakpoints they attain

The attainment side of the breakpoint needs the mixture's retained marginals, and they are a
counting computation, not an assumption.

Insert the heavy pair `(+3, -3)` at position `p+1` of an alternating ordinary sequence, with
`p` uniform on `{0, ..., m-2}`.  Then `+3` sits at position `p+1` and `-3` at `p+2`, so

    Pr(+3 in prefix_k) = #{p : p < k}/(m-1)     = k/(m-1),
    Pr(-3 in prefix_k) = #{p : p < k-1}/(m-1)   = (k-1)/(m-1).

**Odd `m`.**  Both deviations from `k/m` are at most `1/m`, so the band holds at `eta = 1`
and nowhere tighter --- `eta_* = 1`.

**Even `m`.**  Mixing with the sign flip at ratio `1/2` averages the two, giving retained
probability `(2k-1)/(2(m-1))` for each heavy item.  Its deviation is `|2k-m|/(2m(m-1))`,
largest at the two end budgets, where it equals `(m-2)/(2m(m-1))` --- that is `eta_*/m` with
`eta_* = (m-2)/(2(m-1))`.

The two `eta_*` of the breakpoint theorem are therefore attained by an exhibited mixture,
budget by budget.
-/

namespace CIGAMF.P13.PaperCAttain

open Finset
open CIGAMF.P13.PaperCRearrange

/-- The real-valued count of insertion positions inside a prefix. -/
theorem count_lt_real (b M : ℕ) (h : b ≤ M) :
    ∑ j ∈ Finset.range M, (if j < b then (1 : ℝ) else 0) = (b : ℝ) := by
  have hM : b + (M - b) = M := by omega
  have hs := Finset.sum_range_add (fun j => if j < b then (1 : ℝ) else 0) b (M - b)
  rw [hM] at hs
  rw [hs]
  have h1 : ∑ j ∈ Finset.range b, (if j < b then (1 : ℝ) else 0) = (b : ℝ) := by
    rw [Finset.sum_congr rfl (fun j hj => if_pos (by rw [Finset.mem_range] at hj; omega)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have h2 : ∑ i ∈ Finset.range (M - b), (if b + i < b then (1 : ℝ) else 0) = 0 :=
    Finset.sum_eq_zero (fun i _ => if_neg (by omega))
  rw [h1, h2, add_zero]

/-- **The `+3` marginal.**  Position `p+1` lies in the prefix of length `k` exactly when
`p < k`. -/
theorem plus_marginal (m k : ℕ) (hm : 2 ≤ m) (hk : k ≤ m - 1) :
    ∑ p ∈ Finset.range (m - 1), (1 / ((m : ℝ) - 1)) * (if p < k then (1 : ℝ) else 0)
      = (k : ℝ) / ((m : ℝ) - 1) := by
  rw [← Finset.mul_sum, count_lt_real k (m - 1) hk]
  ring

/-- **The `-3` marginal.**  Position `p+2` lies in the prefix of length `k` exactly when
`p < k-1`. -/
theorem minus_marginal (m k : ℕ) (hm : 2 ≤ m) (hk : k ≤ m - 1) :
    ∑ p ∈ Finset.range (m - 1), (1 / ((m : ℝ) - 1)) * (if p < k - 1 then (1 : ℝ) else 0)
      = ((k : ℕ) - 1 : ℕ) / ((m : ℝ) - 1) := by
  rw [← Finset.mul_sum, count_lt_real (k - 1) (m - 1) (by omega)]
  ring

/-- **The odd-`m` deviation is at most `1/m`**, for the `+3` item. -/
theorem plus_deviation (mR kR : ℝ) (hm : 2 ≤ mR) (hk0 : 0 ≤ kR) (hk : kR ≤ mR - 1) :
    |kR / (mR - 1) - kR / mR| ≤ 1 / mR := by
  have hm0 : (0 : ℝ) < mR := by linarith
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  have hid : kR / (mR - 1) - kR / mR = kR / (mR * (mR - 1)) := by
    field_simp
    ring
  rw [hid, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hm0]
  nlinarith [hk, hk0, hm1]

/-- **And at most `1/m` for the `-3` item too.** -/
theorem minus_deviation (mR kR : ℝ) (hm : 2 ≤ mR) (hk1 : 1 ≤ kR) (hk : kR ≤ mR - 1) :
    |(kR - 1) / (mR - 1) - kR / mR| ≤ 1 / mR := by
  have hm0 : (0 : ℝ) < mR := by linarith
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  have hid : (kR - 1) / (mR - 1) - kR / mR = (kR - mR) / (mR * (mR - 1)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ mR * (mR - 1))]
  rw [div_le_div_iff₀ (by positivity) hm0]
  have habs : |kR - mR| = mR - kR := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [habs]
  nlinarith [hk1, hk, hm1]

/-- **The even-`m` mixture's heavy marginal**, after the sign flip at ratio `1/2`. -/
theorem flip_marginal (mR kR : ℝ) (hm : 2 ≤ mR) :
    (1 / 2) * (kR / (mR - 1)) + (1 / 2) * ((kR - 1) / (mR - 1))
      = (2 * kR - 1) / (2 * (mR - 1)) := by
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  field_simp
  ring

/-- **Its deviation is `|2k-m|/(2m(m-1))`**, which is the exact shape the even breakpoint
uses. -/
theorem flip_deviation (mR kR : ℝ) (hm : 2 ≤ mR) :
    (2 * kR - 1) / (2 * (mR - 1)) - kR / mR
      = (2 * kR - mR) / (2 * mR * (mR - 1)) := by
  have hm0 : (0 : ℝ) < mR := by linarith
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  field_simp
  ring

/-- **The largest deviation is at the end budgets**, and equals `eta_*/m` with
`eta_* = (m-2)/(2(m-1))`. -/
theorem flip_deviation_max (mR kR : ℝ) (hm : 3 ≤ mR) (hk1 : 1 ≤ kR) (hk : kR ≤ mR - 1) :
    |(2 * kR - mR) / (2 * mR * (mR - 1))|
      ≤ ((mR - 2) / (2 * (mR - 1))) / mR := by
  have hm0 : (0 : ℝ) < mR := by linarith
  have hm1 : (0 : ℝ) < mR - 1 := by linarith
  have hbound : |2 * kR - mR| ≤ mR - 2 := by
    rw [abs_le]
    constructor <;> linarith
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * mR * (mR - 1))]
  rw [div_le_div_iff₀ (by positivity) hm0]
  have hrw : (mR - 2) / (2 * (mR - 1)) * (2 * mR * (mR - 1)) = (mR - 2) * mR := by
    field_simp
  rw [hrw]
  nlinarith [hbound, hm0]

/-! ## Audit -/

#print axioms count_lt_real
#print axioms plus_marginal
#print axioms minus_marginal
#print axioms plus_deviation
#print axioms minus_deviation
#print axioms flip_marginal
#print axioms flip_deviation
#print axioms flip_deviation_max

end CIGAMF.P13.PaperCAttain
