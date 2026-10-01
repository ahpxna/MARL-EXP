import «LeanPaperCWindowV1»
import «LeanPaperCRankingV1»

/-!
# Paper C: from the window sums to the odd family's value

`LeanPaperCWindowV1` gives the raw circular window sums; the value is those sums divided by
the number of rotations, less the per-budget baseline.  The baseline is `b_k = k mod 2`, and
the step that matters for an upper bound is its LOWER side: every weight of the family is an
odd integer, so a length-`k` prefix sum has the parity of `k` and cannot be smaller in
absolute value than `k mod 2`.  `baseline_le_abs_prefix` proves exactly that from
`prefixSum_parity`, which already existed and is not re-proved here.

That direction is the one an upper bound needs.  If the true per-budget optimum were LARGER
than `k mod 2`, using `k mod 2` would overstate the regret and the bound would still hold;
if it were smaller, the bound would be invalid.  Parity rules the second case out.

The arithmetic then inverts which budget is worst, which is the point of stating it.  The
odd budgets carry the LARGER raw sum --- `m+4` against `k+4 <= m+3` --- and the SMALLER
value, because `b_k = 1` there removes exactly `m/m`.  Reading the raw sums as the value
would put the maximum at the odd budgets; it is at `k = m-1`, and there only.
-/

namespace CIGAMF.P13.PaperCValue

open Finset
open CIGAMF.P13.PaperCWindow

/-- **The baseline is a genuine lower bound.**  With every weight an odd integer, a
length-`k` prefix sum has the parity of `k`, so its absolute value is at least `k mod 2`. -/
theorem baseline_le_abs_prefix {m : ℕ} (π : CIGAMF.P13.PaperCRanking.Ranking m)
    (hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3) (k : ℕ) (hk : k ≤ m) :
    ((k % 2 : ℕ) : ℝ) ≤ |CIGAMF.P13.PaperCRanking.prefixSum π k| := by
  obtain ⟨j, hj⟩ := CIGAMF.P13.PaperCRanking.prefixSum_parity π hw k hk
  rcases Nat.even_or_odd k with he | ho
  · have h0 : k % 2 = 0 := Nat.even_iff.mp he
    rw [h0]
    simpa using abs_nonneg (CIGAMF.P13.PaperCRanking.prefixSum π k)
  · have h1 : k % 2 = 1 := Nat.odd_iff.mp ho
    rw [h1, hj, h1]
    push_cast
    by_cases hjn : (0 : ℝ) ≤ (j : ℝ)
    · rw [abs_of_nonneg (by linarith)]
      have : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith
      linarith
    · have hjneg : (j : ℝ) < 0 := by linarith [not_le.mp hjn]
      have hjle : (j : ℝ) ≤ -1 := by
        have hz : j < 0 := by exact_mod_cast hjneg
        have : j ≤ -1 := by omega
        exact_mod_cast this
      rw [abs_of_nonpos (by linarith)]
      linarith

/-- The value the rotation mixture pays at budget `k`: the mean absolute window, less the
parity baseline. -/
noncomputable def winValue (m k : ℕ) : ℝ :=
  (∑ a ∈ Finset.range m, |win m a k|) / (m : ℝ) - ((k % 2 : ℕ) : ℝ)

/-- **At an odd budget the value is `4/m`** --- the raw sum is the larger of the two, and
the baseline takes exactly `m/m` of it away. -/
theorem winValue_odd (m k : ℕ) (hm3 : 3 ≤ m) (hmodd : m % 2 = 1)
    (hk0 : 0 < k) (hkodd : k % 2 = 1) (hkm : k < m) :
    winValue m k = 4 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast this
  unfold winValue
  rw [win_abs_sum_odd m k hm3 hmodd hk0 hkodd hkm, hkodd]
  field_simp
  push_cast
  ring

/-- **At an even budget the value is `(k+4)/m`** --- the baseline is zero there. -/
theorem winValue_even (m k : ℕ) (hm3 : 3 ≤ m) (hmodd : m % 2 = 1)
    (hk0 : 0 < k) (hkeven : k % 2 = 0) (hkm : k < m) :
    winValue m k = ((k : ℝ) + 4) / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast this
  unfold winValue
  rw [win_abs_sum_even m k hm3 hmodd hk0 hkeven hkm, hkeven]
  simp

/-- **The maximum over budgets is `(m+3)/m`.** -/
theorem winValue_le (m k : ℕ) (hm3 : 3 ≤ m) (hmodd : m % 2 = 1)
    (hk0 : 0 < k) (hkm : k < m) :
    winValue m k ≤ ((m : ℝ) + 3) / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (0 : ℕ) < m := by omega
    exact_mod_cast this
  rcases Nat.even_or_odd k with he | ho
  · have hp : k % 2 = 0 := Nat.even_iff.mp he
    rw [winValue_even m k hm3 hmodd hk0 hp hkm]
    have hkR : (k : ℝ) + 4 ≤ (m : ℝ) + 3 := by
      have : (k : ℝ) ≤ (m : ℝ) - 1 := by
        have h1 : k + 1 ≤ m := by omega
        have : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
        push_cast at this; linarith
      linarith
    rw [div_le_div_iff_of_pos_right hmR]
    linarith
  · have hp : k % 2 = 1 := Nat.odd_iff.mp ho
    rw [winValue_odd m k hm3 hmodd hk0 hp hkm]
    have h4 : (4 : ℝ) ≤ (m : ℝ) + 3 := by
      have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
      linarith
    rw [div_le_div_iff_of_pos_right hmR]
    linarith

/-- **And it is attained at `k = m-1`, the largest even budget.** -/
theorem winValue_at_last (m : ℕ) (hm3 : 3 ≤ m) (hmodd : m % 2 = 1) :
    winValue m (m - 1) = ((m : ℝ) + 3) / (m : ℝ) := by
  have hkm : m - 1 < m := by omega
  have hk0 : 0 < m - 1 := by omega
  have hkeven : (m - 1) % 2 = 0 := by omega
  rw [winValue_even m (m - 1) hm3 hmodd hk0 hkeven hkm]
  congr 1
  have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ m := by omega
    push_cast [Nat.cast_sub h1]
    ring
  rw [this]; ring

/-! ## Audit -/

#print axioms baseline_le_abs_prefix
#print axioms winValue_odd
#print axioms winValue_even
#print axioms winValue_le
#print axioms winValue_at_last

end CIGAMF.P13.PaperCValue
