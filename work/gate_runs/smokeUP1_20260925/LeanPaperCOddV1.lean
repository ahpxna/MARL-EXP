import «LeanPaperCRankingV1»

/-!
# Paper C: the odd family's prefix sequence takes only three values

The odd construction's remaining budgets need the sums of circular windows, and a census
over windows is the expensive way to get them.  It is unnecessary: the base sequence's
prefix sequence is completely regular.  With

    base = ( +3, -3, -1, +1, -1, +1, ..., -1 ),      m odd,

the prefixes are

    P_0 = 0,   P_1 = 3,   and for j >= 2:   P_j = 0 if j is even,  -1 if j is odd,

so `P_m = -1`, which is the total.  Only THREE values occur.  Since a circular window
`[a, a+k)` has sum `P_{a+k} - P_a` when `a + k <= m` and `total - P_a + P_{a+k-m}`
otherwise, the classification the remaining budgets need becomes finite arithmetic on
`{0, 3, -1}` indexed by a parity, rather than a combinatorial census over windows.

`prefixSum_succ` and `prefixSum_zero` of `LeanPaperCRankingV1` do the work; nothing is
re-proved.

WHAT THIS IS NOT.  The pattern, not the window sums.  Assembling it into
`sum over rotations of |window| = 4 + m` at odd budgets and `= k + 4` at even ones, and
hence the odd family's per-budget value, is the step that remains.  The critical budget
`k = m-1` is already closed without any of this (`sum_rot_abs_prefix`, `LeanPaperCOmitV1`).
-/

namespace CIGAMF.P13.PaperCOdd

open Finset
open CIGAMF.P13.PaperCRanking

/-- The odd family's weights: `+3`, `-3`, then `-1` and `+1` alternating. -/
noncomputable def oddBase (m : ℕ) : Ranking m := fun i =>
  if (i : ℕ) = 0 then 3
  else if (i : ℕ) = 1 then -3
  else if (i : ℕ) % 2 = 0 then -1 else 1

theorem oddBase_zero (m : ℕ) (hm : 0 < m) : oddBase m ⟨0, hm⟩ = 3 := by
  simp [oddBase]

theorem oddBase_one (m : ℕ) (hm : 1 < m) : oddBase m ⟨1, hm⟩ = -3 := by
  simp [oddBase]

theorem oddBase_even (m j : ℕ) (hj : j < m) (h2 : 2 ≤ j) (hpar : j % 2 = 0) :
    oddBase m ⟨j, hj⟩ = -1 := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  simp [oddBase, h0, h1, hpar]

theorem oddBase_odd (m j : ℕ) (hj : j < m) (h2 : 2 ≤ j) (hpar : j % 2 = 1) :
    oddBase m ⟨j, hj⟩ = 1 := by
  have h0 : j ≠ 0 := by omega
  have h1 : j ≠ 1 := by omega
  have hne : j % 2 ≠ 0 := by omega
  simp [oddBase, h0, h1, hne]

/-- **The prefix sequence takes only three values, in a regular pattern.** -/
theorem oddPrefix_pattern (m : ℕ) (hm : 1 < m) :
    ∀ j, 2 ≤ j → j ≤ m →
      prefixSum (oddBase m) j = if j % 2 = 0 then 0 else -1 := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ n ih =>
    intro h2 hle
    rcases Nat.lt_or_ge n 2 with hn | hn
    · -- n + 1 = 2, so n = 1: the first two weights cancel
      have hn1 : n = 1 := by omega
      subst hn1
      have h0 : (0 : ℕ) < m := by omega
      have h1 : (1 : ℕ) < m := hm
      rw [prefixSum_succ (oddBase m) 1 h1, prefixSum_one h0 (oddBase m),
          oddBase_zero m h0, oddBase_one m h1]
      norm_num
    · -- n >= 2: one more alternating weight flips between 0 and -1
      have hnm : n < m := by omega
      have hih := ih hn (by omega)
      rw [prefixSum_succ (oddBase m) n hnm, hih]
      rcases Nat.even_or_odd n with he | ho
      · have hpar : n % 2 = 0 := Nat.even_iff.mp he
        rw [if_pos hpar, oddBase_even m n hnm hn hpar, if_neg (by omega)]
        norm_num
      · have hpar : n % 2 = 1 := Nat.odd_iff.mp ho
        rw [if_neg (by omega), oddBase_odd m n hnm hn hpar, if_pos (by omega)]
        norm_num

/-- **Only three values occur**, which is what turns the window classification into finite
arithmetic. -/
theorem oddPrefix_three_values (m : ℕ) (hm : 1 < m) (j : ℕ) (hj : j ≤ m) :
    prefixSum (oddBase m) j = 0 ∨ prefixSum (oddBase m) j = 3
      ∨ prefixSum (oddBase m) j = -1 := by
  rcases Nat.lt_or_ge j 2 with hlt | hge
  · interval_cases j
    · rw [prefixSum_zero]; exact Or.inl rfl
    · rw [prefixSum_one (by omega) (oddBase m), oddBase_zero m (by omega)]
      exact Or.inr (Or.inl rfl)
  · rw [oddPrefix_pattern m hm j hge hj]
    by_cases hpar : j % 2 = 0
    · rw [if_pos hpar]; exact Or.inl rfl
    · rw [if_neg hpar]; exact Or.inr (Or.inr rfl)

/-- **The total is `-1`**, a corollary of the pattern at `j = m` for odd `m`. -/
theorem oddBase_total (m : ℕ) (hm : 1 < m) (hpar : m % 2 = 1) :
    prefixSum (oddBase m) m = -1 := by
  rw [oddPrefix_pattern m hm m (by omega) le_rfl, if_neg (by omega)]

/-! ## Audit -/

#print axioms oddPrefix_pattern
#print axioms oddPrefix_three_values
#print axioms oddBase_total

end CIGAMF.P13.PaperCOdd
