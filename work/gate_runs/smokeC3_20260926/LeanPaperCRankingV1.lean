import Mathlib

/-!
# Paper C: rankings of the signed-prefix family, and the even two-budget identity

`LeanPaperCBreakpointV1` proves the ARITHMETIC of the breakpoint law: given the two
combinatorial facts (L1) and (L2) about rankings, the law follows for every real `m`.  It
could not state those facts, because that module has no model of a ranking at all -- its
`LayeredFlow` is a flow on a DAG and `PathDecompositionDebt` is an explicitly named debt.

This module supplies the model and discharges BOTH, for every size.

    (L1)  r_1 + r_{m-1}  =  (2/D) * ( [first item heavy] + [last item heavy] ),

where *heavy* means weight `+-3`.  The proof is short once the model is there, and it is
worth saying why the statement is true: for even `m` the family's weights sum to ZERO, so
the prefix of length `m-1` is the negative of the last item, exactly as the prefix of length
one is the first item.  Both excesses therefore read off an END position, and each is `2`
when that end is heavy and `0` when it is not.  Nothing in between matters.

The baseline value `b_1 = b_{m-1} = 1` is not assumed: `baseline_first` and `baseline_last`
prove it is the MINIMUM over family rankings, with the lower bound holding on every ranking
and the value attained by an explicit ranking at every even size `>= 4`.

(L2) is the odd case,

    sum_{k=1}^{m-1} ( |S_k| - b_k )  >=  2 + 2 * [ the last item is positive ],

and it needs one extra ingredient: PARITY.  Every weight is an odd integer, so `S_k` has the
parity of `k`, an odd budget cannot have prefix sum zero, and `b_k = k mod 2` is therefore a
baseline rather than a guess.  With that, the mechanism is the `+3` step: if
`S_{k+1} = S_k + 3` then `|S_k| + |S_{k+1}| >= 3` while the two baselines sum to one, so the
two budgets straddling the heavy positive item already carry excess two.  The case analysis
only keeps those budgets in range.

`EXP_paperC_general_m.py` verified both lemmas by exhaustive enumeration for `m <= 10`
before either was proved; that enumeration is now a cross-check on the statements rather
than the evidence for them.
-/

namespace CIGAMF.P13.PaperCRanking

open scoped BigOperators

variable {m : ℕ}

/-- A ranking, as the weight it places at each position. -/
abbrev Ranking (m : ℕ) := Fin m → ℝ

/-- The signed prefix sum after `k` positions. -/
noncomputable def prefixSum (π : Ranking m) (k : ℕ) : ℝ :=
  ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => (i : ℕ) < k), π i

/-- Membership of the signed-prefix family in the EVEN case: every weight is one of the
four, and the total vanishes.  The vanishing total is exactly what distinguishes the even
sizes, and it is what the identity below uses. -/
structure IsEvenFamily (π : Ranking m) : Prop where
  weight : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3
  total : ∑ i, π i = 0

/-- The indicator that an item is one of the two heavy ones. -/
noncomputable def heavy (w : ℝ) : ℝ := if |w| = 3 then 1 else 0

theorem heavy_eq_zero_or_one (w : ℝ) : heavy w = 0 ∨ heavy w = 1 := by
  unfold heavy; split_ifs
  · right; rfl
  · left; rfl

theorem abs_weight (w : ℝ) (h : w = -3 ∨ w = -1 ∨ w = 1 ∨ w = 3) : |w| = 1 ∨ |w| = 3 := by
  rcases h with h | h | h | h <;> subst h <;> norm_num

theorem one_le_abs_weight (w : ℝ) (h : |w| = 1 ∨ |w| = 3) : 1 ≤ |w| := by
  rcases h with h | h <;> rw [h] <;> norm_num

/-- An item's excess over the baseline is `2` exactly when it is heavy. -/
theorem excess_eq_two_heavy (w : ℝ) (h : |w| = 1 ∨ |w| = 3) : |w| - 1 = 2 * heavy w := by
  unfold heavy
  rcases h with h | h <;> rw [h] <;> norm_num

/-! ## The two end budgets read off the two end items -/

theorem prefixSum_one (hm : 0 < m) (π : Ranking m) : prefixSum π 1 = π ⟨0, hm⟩ := by
  unfold prefixSum
  have hset : (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => (i : ℕ) < 1)
      = {(⟨0, hm⟩ : Fin m)} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.ext_iff]
    omega
  rw [hset, Finset.sum_singleton]

theorem prefixSum_pred (hm : 0 < m) (π : Ranking m) :
    prefixSum π (m - 1) = (∑ i, π i) - π ⟨m - 1, by omega⟩ := by
  unfold prefixSum
  have hset : (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => (i : ℕ) < m - 1)
      = (Finset.univ : Finset (Fin m)).erase ⟨m - 1, by omega⟩ := by
    ext i
    have hi := i.isLt
    have hv : ((⟨m - 1, by omega⟩ : Fin m) : ℕ) = m - 1 := rfl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
      Fin.val_ne_iff.symm, hv, and_true]
    omega
  rw [hset, Finset.sum_erase_eq_sub (Finset.mem_univ _)]

/-- **(L1), the even two-budget identity.**

The weights sum to zero, so the prefix of length `m-1` is minus the last item.  Both
excesses therefore depend only on an end position, and each is `2` exactly when that end is
heavy.  This is the hypothesis `hid` of `LeanPaperCBreakpointV1.breakpoint_lower_even`. -/
theorem two_budget_identity (hm : 1 < m) (π : Ranking m) (hfam : IsEvenFamily π) :
    (|prefixSum π 1| - 1) + (|prefixSum π (m - 1)| - 1)
      = 2 * (heavy (π ⟨0, by omega⟩) + heavy (π ⟨m - 1, by omega⟩)) := by
  have h1 : prefixSum π 1 = π ⟨0, by omega⟩ := prefixSum_one (by omega) π
  have h2 : prefixSum π (m - 1) = -π ⟨m - 1, by omega⟩ := by
    rw [prefixSum_pred (by omega) π, hfam.total]; ring
  rw [h1, h2, abs_neg]
  have e1 := excess_eq_two_heavy (π ⟨0, by omega⟩) (abs_weight _ (hfam.weight _))
  have e2 := excess_eq_two_heavy (π ⟨m - 1, by omega⟩) (abs_weight _ (hfam.weight _))
  linarith

/-- The same identity divided by `D`, i.e. in the `r_k` normalisation the breakpoint
argument uses. -/
theorem two_budget_identity_div (hm : 1 < m) (D : ℝ) (hD : D ≠ 0)
    (π : Ranking m) (hfam : IsEvenFamily π) :
    (|prefixSum π 1| - 1) / D + (|prefixSum π (m - 1)| - 1) / D
      = 2 / D * (heavy (π ⟨0, by omega⟩) + heavy (π ⟨m - 1, by omega⟩)) := by
  have h := two_budget_identity hm π hfam
  field_simp
  linarith [h]

/-! ## The baseline at the two end budgets really is `1` -/

theorem one_le_prefixSum_first (hm : 1 < m) (π : Ranking m) (hfam : IsEvenFamily π) :
    1 ≤ |prefixSum π 1| := by
  rw [prefixSum_one (by omega) π]
  exact one_le_abs_weight _ (abs_weight _ (hfam.weight _))

theorem one_le_prefixSum_last (hm : 1 < m) (π : Ranking m) (hfam : IsEvenFamily π) :
    1 ≤ |prefixSum π (m - 1)| := by
  have h2 : prefixSum π (m - 1) = -π ⟨m - 1, by omega⟩ := by
    rw [prefixSum_pred (by omega) π, hfam.total]; ring
  rw [h2, abs_neg]
  exact one_le_abs_weight _ (abs_weight _ (hfam.weight _))

/-! ## An explicit family ranking at every even size, attaining the baseline -/

/-- The alternating ranking with the two heavy items at the end. -/
noncomputable def altWeight (m i : ℕ) : ℝ :=
  if i = m - 2 then 3 else if i = m - 1 then -3 else (-1 : ℝ) ^ i

noncomputable def altFamily (m : ℕ) : Ranking m := fun i => altWeight m (i : ℕ)

theorem altWeight_lt (n i : ℕ) (hi : i < n) : altWeight (n + 2) i = (-1 : ℝ) ^ i := by
  unfold altWeight
  rw [if_neg (by omega), if_neg (by omega)]

theorem altWeight_heavy_pos (n : ℕ) : altWeight (n + 2) n = 3 := by
  unfold altWeight; rw [if_pos (by omega)]

theorem altWeight_heavy_neg (n : ℕ) : altWeight (n + 2) (n + 1) = -3 := by
  unfold altWeight; rw [if_neg (by omega), if_pos (by omega)]

theorem altFamily_isFamily (n : ℕ) (hn : Even n) : IsEvenFamily (altFamily (n + 2)) := by
  constructor
  · intro i
    have hi := i.isLt
    unfold altFamily altWeight
    split_ifs with h1 h2
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl rfl
    · rcases Nat.even_or_odd (i : ℕ) with he | ho
      · exact Or.inr (Or.inr (Or.inl he.neg_one_pow))
      · exact Or.inr (Or.inl ho.neg_one_pow)
  · have hconv : ∑ i : Fin (n + 2), altFamily (n + 2) i
        = ∑ i ∈ Finset.range (n + 2), altWeight (n + 2) i :=
      Fin.sum_univ_eq_sum_range (altWeight (n + 2)) (n + 2)
    rw [hconv, Finset.sum_range_succ, Finset.sum_range_succ,
        altWeight_heavy_pos n, altWeight_heavy_neg n]
    have hrest : ∑ i ∈ Finset.range n, altWeight (n + 2) i
        = ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i :=
      Finset.sum_congr rfl fun i hi => altWeight_lt n i (Finset.mem_range.mp hi)
    rw [hrest, neg_one_geom_sum, if_pos hn]
    ring

/-- The alternating ranking starts with a light item, so it attains the baseline `1` at the
first budget. -/
theorem altFamily_first (n : ℕ) (hn : 0 < n) :
    |prefixSum (altFamily (n + 2)) 1| = 1 := by
  rw [prefixSum_one (by omega) _]
  show |altWeight (n + 2) ((⟨0, by omega⟩ : Fin (n + 2)) : ℕ)| = 1
  rw [show ((⟨0, by omega⟩ : Fin (n + 2)) : ℕ) = 0 from rfl, altWeight_lt n 0 hn]
  norm_num

/-- And it attains the baseline at the last budget too: the final item is heavy, but the
prefix of length `m-1` is minus that item only after the total has been used, and here the
alternating part contributes the `+-1` that makes the value `1`. -/
theorem altFamily_last (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    |prefixSum (altFamily (n + 2)) (n + 2 - 1)| = 3 := by
  have h2 : prefixSum (altFamily (n + 2)) (n + 2 - 1)
      = -altFamily (n + 2) ⟨n + 2 - 1, by omega⟩ := by
    rw [prefixSum_pred (by omega) _, (altFamily_isFamily n hn).total]; ring
  rw [h2, abs_neg]
  show |altWeight (n + 2) ((⟨n + 1, by omega⟩ : Fin (n + 2)) : ℕ)| = 3
  rw [show ((⟨n + 1, by omega⟩ : Fin (n + 2)) : ℕ) = n + 1 from rfl,
      altWeight_heavy_neg n]
  norm_num

/-- **The baseline at the first budget is exactly `1`**: no family ranking beats it, and the
alternating ranking attains it.  So writing `b_1 = 1` in the breakpoint argument is a
computed value, not a convention. -/
theorem baseline_first (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    IsLeast {v : ℝ | ∃ π : Ranking (n + 2), IsEvenFamily π ∧ v = |prefixSum π 1|} 1 := by
  constructor
  · exact ⟨altFamily (n + 2), altFamily_isFamily n hn, (altFamily_first n hn0).symm⟩
  · rintro v ⟨π, hfam, rfl⟩
    exact one_le_prefixSum_first (by omega) π hfam

theorem baseline_last_lower (n : ℕ) (π : Ranking (n + 2)) (hfam : IsEvenFamily π) :
    1 ≤ |prefixSum π (n + 2 - 1)| :=
  one_le_prefixSum_last (by omega) π hfam

/-- The alternating ranking above ends with a HEAVY item, so it gives `3` at the last
budget, not `1`.  Recording that is the point: it does not attain the baseline there, and a
second witness is needed. -/
theorem altFamily_last_is_three (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    |prefixSum (altFamily (n + 2)) (n + 2 - 1)| = 3 := altFamily_last n hn hn0

/-- The witness that does attain it: the same alternating pattern with both heavy items
moved to the FRONT, so the last position carries a `+-1`. -/
noncomputable def altWeight2 (m i : ℕ) : ℝ :=
  if i = 0 then 3 else if i = 1 then -3 else (-1 : ℝ) ^ i

noncomputable def altFamily2 (m : ℕ) : Ranking m := fun i => altWeight2 m (i : ℕ)

/-- It differs from the plain alternating sequence at two positions only, by `+2` and `-2`,
which is what makes its total vanish. -/
theorem altWeight2_decomp (m i : ℕ) :
    altWeight2 m i
      = (-1 : ℝ) ^ i + (if i = 0 then 2 else 0) + (if i = 1 then -2 else 0) := by
  unfold altWeight2
  by_cases h0 : i = 0
  · subst h0; norm_num
  · by_cases h1 : i = 1
    · subst h1; norm_num
    · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1]; ring

theorem altFamily2_isFamily (n : ℕ) (hn : Even n) : IsEvenFamily (altFamily2 (n + 2)) := by
  constructor
  · intro i
    unfold altFamily2 altWeight2
    split_ifs with h1 h2
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl rfl
    · rcases Nat.even_or_odd (i : ℕ) with he | ho
      · exact Or.inr (Or.inr (Or.inl he.neg_one_pow))
      · exact Or.inr (Or.inl ho.neg_one_pow)
  · have hconv : ∑ i : Fin (n + 2), altFamily2 (n + 2) i
        = ∑ i ∈ Finset.range (n + 2), altWeight2 (n + 2) i :=
      Fin.sum_univ_eq_sum_range (altWeight2 (n + 2)) (n + 2)
    have hdec : ∑ i ∈ Finset.range (n + 2), altWeight2 (n + 2) i
        = ∑ i ∈ Finset.range (n + 2),
            ((-1 : ℝ) ^ i + (if i = 0 then 2 else 0) + (if i = 1 then -2 else 0)) :=
      Finset.sum_congr rfl fun i _ => altWeight2_decomp (n + 2) i
    have s1 : ∑ i ∈ Finset.range (n + 2), (if i = 0 then (2 : ℝ) else 0) = 2 := by
      rw [Finset.sum_ite_eq' (Finset.range (n + 2)) 0 (fun _ => (2 : ℝ))]
      rw [if_pos (Finset.mem_range.mpr (by omega))]
    have s2 : ∑ i ∈ Finset.range (n + 2), (if i = 1 then (-2 : ℝ) else 0) = -2 := by
      rw [Finset.sum_ite_eq' (Finset.range (n + 2)) 1 (fun _ => (-2 : ℝ))]
      rw [if_pos (Finset.mem_range.mpr (by omega))]
    rw [hconv, hdec, Finset.sum_add_distrib, Finset.sum_add_distrib, s1, s2,
        neg_one_geom_sum, if_pos (by simpa using hn.add (even_iff_two_dvd.mpr ⟨1, rfl⟩))]
    ring

/-- At `n = 0` the family is just `(3, -3)` and the last item IS heavy, so the hypothesis
`0 < n` is not decoration: it is exactly the range where a light item is available to put
last. -/
theorem altFamily2_last (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    |prefixSum (altFamily2 (n + 2)) (n + 2 - 1)| = 1 := by
  have h2 : prefixSum (altFamily2 (n + 2)) (n + 2 - 1)
      = -altFamily2 (n + 2) ⟨n + 2 - 1, by omega⟩ := by
    rw [prefixSum_pred (by omega) _, (altFamily2_isFamily n hn).total]; ring
  rw [h2, abs_neg]
  show |altWeight2 (n + 2) ((⟨n + 1, by omega⟩ : Fin (n + 2)) : ℕ)| = 1
  rw [show ((⟨n + 1, by omega⟩ : Fin (n + 2)) : ℕ) = n + 1 from rfl]
  unfold altWeight2
  obtain ⟨k, hk⟩ := hn
  subst hk
  have hk0 : 0 < k := by omega
  rw [if_neg (by omega), if_neg (by omega)]
  have : Odd (k + k + 1) := ⟨k, by ring⟩
  rw [this.neg_one_pow]
  norm_num

/-- **The baseline at the last budget is exactly `1`**, by the same two steps: no family
ranking beats it, and `altFamily2` attains it. -/
theorem baseline_last (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    IsLeast {v : ℝ | ∃ π : Ranking (n + 2), IsEvenFamily π ∧ v = |prefixSum π (n + 2 - 1)|}
      1 := by
  constructor
  · exact ⟨altFamily2 (n + 2), altFamily2_isFamily n hn, (altFamily2_last n hn hn0).symm⟩
  · rintro v ⟨π, hfam, rfl⟩
    exact baseline_last_lower n π hfam

/-! ## Non-vacuity, and the bridge to the arithmetic -/

/-- The family is inhabited at every even size at least four, so every statement above has
instances. -/
theorem evenFamily_nonempty (n : ℕ) (hn : Even n) (hn0 : 0 < n) :
    ∃ π : Ranking (n + 2), IsEvenFamily π :=
  ⟨altFamily (n + 2), altFamily_isFamily n hn⟩

/-- **(L1) in the exact shape `breakpoint_lower_even` consumes.**  A randomised ranking is a
law `P` on a finite index set together with the ranking each index names; the identity holds
pointwise, so it holds under the law. -/
theorem hid_for_breakpoint {R : Type*} [Fintype R] (hm : 1 < m)
    (rank : R → Ranking m) (hfam : ∀ x, IsEvenFamily (rank x)) (D : ℝ) (hD : D ≠ 0) :
    ∀ x : R,
      (|prefixSum (rank x) 1| - 1) / D + (|prefixSum (rank x) (m - 1)| - 1) / D
        = 2 / D * (heavy (rank x ⟨0, by omega⟩) + heavy (rank x ⟨m - 1, by omega⟩)) :=
  fun x => two_budget_identity_div hm D hD (rank x) (hfam x)

/-! ## The odd case: parity, and the excess a `+3` step forces

For odd `m` the family's weights sum to `-1`, not `0`, and the two-budget identity of the
even case is unavailable.  (L2) replaces it:

    sum_{k=1}^{m-1} ( |S_k| - b_k )  >=  2 + 2 * [ the last item is positive ],

with `b_k = k mod 2`.  Two ingredients, both proved here.

PARITY.  Every weight is an ODD integer, so `S_k` has the parity of `k`.  An odd budget
therefore cannot have prefix sum zero, which is what makes `b_k = k mod 2` a baseline and
what makes every excess nonnegative.

THE `+3` STEP.  If `S_{k+1} = S_k + 3` then `|S_k| + |S_{k+1}| >= 3` by the triangle
inequality, while `b_k + b_{k+1} = 1` because consecutive budgets have opposite parity.  So
the two budgets straddling the heavy positive item already carry excess `2`.  That is the
whole mechanism, and everything else is bookkeeping about where that item sits. -/

/-- The odd family: the same four weights, but the total is `-1`. -/
structure IsOddFamily (π : Ranking m) : Prop where
  weight : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3
  total : ∑ i, π i = -1

/-- Every weight of the family is an odd integer. -/
theorem weight_odd (w : ℝ) (h : w = -3 ∨ w = -1 ∨ w = 1 ∨ w = 3) :
    ∃ a : ℤ, w = 2 * (a : ℝ) + 1 := by
  rcases h with h | h | h | h <;> subst h
  · exact ⟨-2, by norm_num⟩
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨1, by norm_num⟩

theorem prefixSum_zero (π : Ranking m) : prefixSum π 0 = 0 := by
  unfold prefixSum
  have : (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => (i : ℕ) < 0) = ∅ := by
    ext i; simp
  rw [this, Finset.sum_empty]

theorem prefixSum_succ (π : Ranking m) (k : ℕ) (hk : k < m) :
    prefixSum π (k + 1) = prefixSum π k + π ⟨k, hk⟩ := by
  unfold prefixSum
  have hv : ((⟨k, hk⟩ : Fin m) : ℕ) = k := rfl
  have hnot : (⟨k, hk⟩ : Fin m)
      ∉ (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => (i : ℕ) < k) := by
    simp [hv]
  have hins : (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => (i : ℕ) < k + 1)
      = insert (⟨k, hk⟩ : Fin m)
          ((Finset.univ : Finset (Fin m)).filter (fun i : Fin m => (i : ℕ) < k)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.ext_iff, hv]
    omega
  rw [hins, Finset.sum_insert hnot, add_comm]

/-- **The prefix sum has the parity of the budget.**  Every weight is odd, so `k` of them
sum to something congruent to `k` modulo two. -/
theorem prefixSum_parity (π : Ranking m)
    (hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3) :
    ∀ k, k ≤ m → ∃ j : ℤ, prefixSum π k = 2 * (j : ℝ) + ((k % 2 : ℕ) : ℝ) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, by simp [prefixSum_zero]⟩
  | succ n ih =>
    intro hn
    have hnm : n < m := by omega
    obtain ⟨j, hj⟩ := ih (by omega)
    obtain ⟨a, ha⟩ := weight_odd (π ⟨n, hnm⟩) (hw _)
    rw [prefixSum_succ π n hnm, hj, ha]
    rcases Nat.even_or_odd n with he | ho
    · have h0 : n % 2 = 0 := Nat.even_iff.mp he
      have h1 : (n + 1) % 2 = 1 := by omega
      refine ⟨j + a, ?_⟩
      rw [h0, h1]
      push_cast
      ring
    · have h0 : n % 2 = 1 := Nat.odd_iff.mp ho
      have h1 : (n + 1) % 2 = 0 := by omega
      refine ⟨j + a + 1, ?_⟩
      rw [h0, h1]
      push_cast
      ring

/-- An odd budget has prefix sum at least one in absolute value: it cannot be zero. -/
theorem one_le_abs_prefixSum_of_odd (π : Ranking m)
    (hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3)
    (k : ℕ) (hk : k ≤ m) (hodd : k % 2 = 1) : 1 ≤ |prefixSum π k| := by
  obtain ⟨j, hj⟩ := prefixSum_parity π hw k hk
  rw [hodd] at hj
  rcases le_or_gt 0 j with h | h
  · have hj0 : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
    have : (1 : ℝ) ≤ prefixSum π k := by rw [hj]; push_cast; linarith
    calc (1 : ℝ) ≤ prefixSum π k := this
      _ ≤ |prefixSum π k| := le_abs_self _
  · have hjz : j ≤ -1 := by omega
    have hj1 : (j : ℝ) ≤ -1 := by exact_mod_cast hjz
    have : prefixSum π k ≤ -1 := by rw [hj]; push_cast; linarith
    calc (1 : ℝ) ≤ -prefixSum π k := by linarith
      _ ≤ |prefixSum π k| := neg_le_abs _

/-- The excess of a budget over its baseline. -/
noncomputable def excess (π : Ranking m) (k : ℕ) : ℝ :=
  |prefixSum π k| - ((k % 2 : ℕ) : ℝ)

/-- **Every excess is nonnegative**, which is what lets a bound on a few budgets bound the
whole sum.  For an even budget the baseline is zero; for an odd one it is one, and parity
supplies it. -/
theorem excess_nonneg (π : Ranking m)
    (hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3)
    (k : ℕ) (hk : k ≤ m) : 0 ≤ excess π k := by
  unfold excess
  rcases Nat.even_or_odd k with he | ho
  · rw [show k % 2 = 0 from Nat.even_iff.mp he]
    simpa using abs_nonneg (prefixSum π k)
  · rw [show k % 2 = 1 from Nat.odd_iff.mp ho]
    have := one_le_abs_prefixSum_of_odd π hw k hk (Nat.odd_iff.mp ho)
    push_cast
    linarith

/-- **The `+3` step forces excess two, across the two budgets that straddle it.**

`|S_k| + |S_{k+1}| >= |S_{k+1} - S_k| = 3` by the triangle inequality, and the two baselines
sum to one because consecutive budgets have opposite parity.  No case analysis on where the
item sits is needed for this step; that comes later, and only to keep the budgets in
range. -/
theorem jump_forces_excess (π : Ranking m) (k : ℕ) (hk : k < m)
    (hjump : π ⟨k, hk⟩ = 3) : 2 ≤ excess π k + excess π (k + 1) := by
  have hstep : prefixSum π (k + 1) = prefixSum π k + 3 := by
    rw [prefixSum_succ π k hk, hjump]
  have htri : 3 ≤ |prefixSum π k| + |prefixSum π (k + 1)| := by
    have h := abs_sub_abs_le_abs_sub (prefixSum π (k + 1)) (prefixSum π k)
    have h2 : |prefixSum π (k + 1) - prefixSum π k| = 3 := by
      rw [hstep]; norm_num
    have h3 := abs_nonneg (prefixSum π k)
    have h4 := abs_nonneg (prefixSum π (k + 1))
    have h5 : |prefixSum π (k + 1) - prefixSum π k|
        ≤ |prefixSum π (k + 1)| + |prefixSum π k| := abs_sub _ _
    rw [h2] at h5
    linarith
  have hbase : ((k % 2 : ℕ) : ℝ) + (((k + 1) % 2 : ℕ) : ℝ) = 1 := by
    rcases Nat.even_or_odd k with he | ho
    · have h0 : k % 2 = 0 := Nat.even_iff.mp he
      have h1 : (k + 1) % 2 = 1 := by omega
      rw [h0, h1]; norm_num
    · have h0 : k % 2 = 1 := Nat.odd_iff.mp ho
      have h1 : (k + 1) % 2 = 0 := by omega
      rw [h0, h1]; norm_num
  unfold excess
  linarith

/-! ### (L2), assembled

The pieces above are combined by a single bookkeeping lemma: because every excess is
nonnegative, a bound on ANY set of budgets bounds the total.  The cases then differ only in
which budgets to look at, and there are four.  The last item is `+3`, or `+1`, or negative;
in the last two the heavy positive item sits elsewhere, and either at the very front (where
budget one already carries excess two) or in the interior (where the straddling pair does).
The one case that needs its own computation is the heavy item immediately before the end,
because there the straddling pair overlaps the last budget. -/

/-- The total excess over the budgets `1, ..., m-1`. -/
noncomputable def totalExcess (π : Ranking m) : ℝ := ∑ k ∈ Finset.Ico 1 m, excess π k

/-- A bound on any set of budgets bounds the total, since no excess is negative. -/
theorem totalExcess_ge_of_subset (π : Ranking m)
    (hw : ∀ i, π i = -3 ∨ π i = -1 ∨ π i = 1 ∨ π i = 3)
    (B : Finset ℕ) (hB : B ⊆ Finset.Ico 1 m) (c : ℝ)
    (hc : c ≤ ∑ k ∈ B, excess π k) : c ≤ totalExcess π := by
  refine le_trans hc (Finset.sum_le_sum_of_subset_of_nonneg hB ?_)
  intro k hk _
  have := Finset.mem_Ico.mp hk
  exact excess_nonneg π hw k (by omega)

theorem prefixSum_last_odd (hm : 0 < m) (π : Ranking m) (hfam : IsOddFamily π) :
    prefixSum π (m - 1) = -1 - π ⟨m - 1, by omega⟩ := by
  rw [prefixSum_pred hm π, hfam.total]

theorem excess_last (hm : 0 < m) (hmo : m % 2 = 1) (π : Ranking m) (hfam : IsOddFamily π) :
    excess π (m - 1) = |(-1 : ℝ) - π ⟨m - 1, by omega⟩| := by
  unfold excess
  rw [prefixSum_last_odd hm π hfam, show (m - 1) % 2 = 0 by omega]
  norm_num

/-- **(L2), the odd total-excess inequality.**

For a family whose weights sum to `-1`, the excesses over budgets `1, ..., m-1` add up to at
least `2`, and to at least `4` when the last item is positive.  This is the hypothesis
`hineq` of `LeanPaperCBreakpointV1.breakpoint_lower_odd`, and with it the odd breakpoint
`eta_* = 1` follows for every `m`. -/
theorem odd_total_excess (hm : 2 < m) (hmo : m % 2 = 1) (π : Ranking m)
    (hfam : IsOddFamily π) (j : ℕ) (hj : j < m) (hj3 : π ⟨j, hj⟩ = 3) :
    2 + 2 * (if 0 < π ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) ≤ totalExcess π := by
  have hw := hfam.weight
  have hlastval := hfam.weight ⟨m - 1, by omega⟩
  have hex1 : excess π 1 = |π ⟨0, by omega⟩| - 1 := by
    unfold excess
    rw [prefixSum_one (by omega) π]
    norm_num
  have hpair : ∀ k : ℕ, ∀ hk : k < m, π ⟨k, hk⟩ = 3 → 2 ≤ excess π k + excess π (k + 1) :=
    fun k hk h => jump_forces_excess π k hk h
  -- the five budget sets the cases use, and their membership proofs
  have hB1 : ({1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  have hBlast : ({m - 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
    intro x hx
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  have hB1last : ({1, m - 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  have hBend : ({m - 2, m - 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_Ico]
    omega
  have hzero : ∀ _ : j = 0, (⟨0, by omega⟩ : Fin m) = ⟨j, hj⟩ := by
    intro hj0
    apply Fin.ext
    show (0 : ℕ) = j
    omega
  rcases hlastval with hL | hL | hL | hL
  -- ---------------------------------------------------------------- last item is -3
  · rw [if_neg (by rw [hL]; norm_num)]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · refine totalExcess_ge_of_subset π hw {1} hB1 _ ?_
      rw [Finset.sum_singleton, hex1, hzero hj0, hj3]
      norm_num
    · have hjlt : j + 1 < m := by
        rcases Nat.lt_or_ge (j + 1) m with h | h
        · exact h
        · exfalso
          have hjm : j = m - 1 := by omega
          have hid : (⟨j, hj⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
            apply Fin.ext
            show j = m - 1
            omega
          rw [hid, hL] at hj3
          norm_num at hj3
      have hBp : ({j, j + 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Ico]
        omega
      refine totalExcess_ge_of_subset π hw {j, j + 1} hBp _ ?_
      rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
          Finset.sum_singleton]
      linarith [hpair j hj hj3]
  -- ---------------------------------------------------------------- last item is -1
  · rw [if_neg (by rw [hL]; norm_num)]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · refine totalExcess_ge_of_subset π hw {1} hB1 _ ?_
      rw [Finset.sum_singleton, hex1, hzero hj0, hj3]
      norm_num
    · have hjlt : j + 1 < m := by
        rcases Nat.lt_or_ge (j + 1) m with h | h
        · exact h
        · exfalso
          have hid : (⟨j, hj⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
            apply Fin.ext
            show j = m - 1
            omega
          rw [hid, hL] at hj3
          norm_num at hj3
      have hBp : ({j, j + 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_Ico]
        omega
      refine totalExcess_ge_of_subset π hw {j, j + 1} hBp _ ?_
      rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
          Finset.sum_singleton]
      linarith [hpair j hj hj3]
  -- ---------------------------------------------------------------- last item is +1
  · rw [if_pos (by rw [hL]; norm_num)]
    have hlast2 : excess π (m - 1) = 2 := by
      rw [excess_last (by omega) hmo π hfam, hL]; norm_num
    have hjne : j ≠ m - 1 := by
      intro h
      have hid : (⟨j, hj⟩ : Fin m) = ⟨m - 1, by omega⟩ := by
        apply Fin.ext
        show j = m - 1
        omega
      rw [hid, hL] at hj3
      norm_num at hj3
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · refine totalExcess_ge_of_subset π hw {1, m - 1} hB1last _ ?_
      rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
          Finset.sum_singleton, hlast2, hex1, hzero hj0, hj3]
      norm_num
    · by_cases hjend : j = m - 2
      · have hstep : prefixSum π (m - 1) = prefixSum π (m - 2) + 3 := by
          have h1 : m - 2 + 1 = m - 1 := by omega
          have hs := prefixSum_succ π (m - 2) (by omega)
          rw [h1] at hs
          have hid : (⟨m - 2, by omega⟩ : Fin m) = ⟨j, hj⟩ := by
            apply Fin.ext
            show m - 2 = j
            omega
          rw [hs, hid, hj3]
        have hm1 : prefixSum π (m - 1) = -2 := by
          rw [prefixSum_last_odd (by omega) π hfam, hL]; norm_num
        have hm2 : prefixSum π (m - 2) = -5 := by rw [hm1] at hstep; linarith
        have hex2 : excess π (m - 2) = 4 := by
          unfold excess
          rw [hm2, show (m - 2) % 2 = 1 by omega]
          norm_num
        refine totalExcess_ge_of_subset π hw {m - 2, m - 1} hBend _ ?_
        rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
            Finset.sum_singleton, hex2, hlast2]
        norm_num
      · have hjlt : j + 1 < m - 1 := by omega
        have hBt : ({j, j + 1, m - 1} : Finset ℕ) ⊆ Finset.Ico 1 m := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          simp only [Finset.mem_Ico]
          omega
        refine totalExcess_ge_of_subset π hw {j, j + 1, m - 1} hBt _ ?_
        rw [Finset.sum_insert
              (by simp only [Finset.mem_insert, Finset.mem_singleton]; omega),
            Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
            Finset.sum_singleton, hlast2]
        linarith [hpair j hj hj3]
  -- ---------------------------------------------------------------- last item is +3
  · rw [if_pos (by rw [hL]; norm_num)]
    refine totalExcess_ge_of_subset π hw {m - 1} hBlast _ ?_
    rw [Finset.sum_singleton, excess_last (by omega) hmo π hfam, hL]
    norm_num

/-! ## (O1): the construction attains the free value at EVERY budget

The lower side of the breakpoint law is proved above.  Its upper side needs a distribution
over rankings that attains the unconstrained optimum `V^free_m = 2/(D(m-1))` at every
budget, and the construction is the one the experiment checks: take the alternating ordinary
sequence and insert the pair `(+3, -3)` at positions `a, a+1`, then mix uniformly over `a`.

The content is the EXCESS PROFILE: each `pi_a` has excess exactly `2` at budget `a+1` and
exactly `0` everywhere else.  Proved here by induction along `prefixSum_succ`, with four
cases -- before the pair, at the `+3`, at the `-3`, and after -- so no closed-form sum and
no `Nat` subtraction in an exponent is ever needed.

Averaging then gives `E r_k = 2/(D(m-1))` at every budget, which is (O1). -/

/-- The alternating sequence with the heavy pair inserted at positions `a` and `a+1`. -/
noncomputable def insWeight (a i : ℕ) : ℝ :=
  if i = a then 3 else if i = a + 1 then -3
  else if i < a then (-1 : ℝ) ^ (i + 1) else (-1 : ℝ) ^ (i - 1)

noncomputable def insRanking (m a : ℕ) : Ranking m := fun i => insWeight a (i : ℕ)

/-- **The prefix sum of the inserted ranking, at every budget.**

Away from the inserted pair it is the alternating pattern `0, -1, 0, -1, ...`; the `+3`
lifts it by three for exactly one budget, and the `-3` puts it back. -/
theorem insRanking_prefix (m a : ℕ) (ha : a + 1 < m) :
    ∀ k, k ≤ m → prefixSum (insRanking m a) k
      = if k = a + 1 then (if Even a then (3 : ℝ) else 2)
        else (if Even k then (0 : ℝ) else -1) := by
  intro k
  induction k with
  | zero =>
      intro _
      have h0 : Even 0 := even_iff_two_dvd.mpr ⟨0, rfl⟩
      rw [prefixSum_zero, if_neg (by omega), if_pos h0]
  | succ n ih =>
      intro hn
      have hnm : n < m := by omega
      have hstep : prefixSum (insRanking m a) (n + 1)
          = prefixSum (insRanking m a) n + insWeight a n := by
        rw [prefixSum_succ (insRanking m a) n hnm]
        rfl
      have hprev := ih (by omega)
      rw [hstep, hprev]
      rcases lt_trichotomy n a with hlt | heq | hgt
      -- before the pair
      · have h1 : n ≠ a := by omega
        have h2 : n ≠ a + 1 := by omega
        have hw : insWeight a n = (-1 : ℝ) ^ (n + 1) := by
          unfold insWeight
          rw [if_neg h1, if_neg h2, if_pos hlt]
        rw [hw, if_neg (by omega : n ≠ a + 1), if_neg (by omega : n + 1 ≠ a + 1)]
        rcases Nat.even_or_odd n with he | ho
        · rw [if_pos he, if_neg (by simpa using he.add_one : ¬ Even (n + 1)),
              (he.add_one : Odd (n + 1)).neg_one_pow]
          norm_num
        · rw [if_neg (by simpa using ho), if_pos (ho.add_one : Even (n + 1)),
              (ho.add_one : Even (n + 1)).neg_one_pow]
          norm_num
      -- at the `+3`
      · subst heq
        have hw : insWeight n n = 3 := by unfold insWeight; rw [if_pos rfl]
        rw [hw, if_neg (by omega : n ≠ n + 1), if_pos rfl]
        rcases Nat.even_or_odd n with he | ho
        · rw [if_pos he, if_pos he]; norm_num
        · rw [if_neg (by simpa using ho), if_neg (by simpa using ho)]; norm_num
      -- at the `-3`, and after it
      · rcases Nat.lt_or_ge a.succ n with hgt2 | hle2
        · -- strictly after the pair
          have h1 : n ≠ a := by omega
          have h2 : n ≠ a + 1 := by omega
          have hlt' : ¬ n < a := by omega
          have hw : insWeight a n = (-1 : ℝ) ^ (n - 1) := by
            unfold insWeight
            rw [if_neg h1, if_neg h2, if_neg hlt']
          obtain ⟨c, rfl⟩ : ∃ c, n = c + 1 := ⟨n - 1, by omega⟩
          rw [hw, if_neg (by omega : c + 1 ≠ a + 1),
              if_neg (by omega : c + 1 + 1 ≠ a + 1),
              show c + 1 - 1 = c from rfl]
          rcases Nat.even_or_odd c with he | ho
          · have h1e : ¬ Even (c + 1) := by simpa using he.add_one
            have h2e : Even (c + 1 + 1) := by
              simpa using (he.add_one : Odd (c + 1)).add_one
            rw [if_neg h1e, if_pos h2e, he.neg_one_pow]
            norm_num
          · have h1e : Even (c + 1) := ho.add_one
            have h2e : ¬ Even (c + 1 + 1) := by
              simpa using (h1e.add_one : Odd (c + 1 + 1))
            rw [if_pos h1e, if_neg h2e, ho.neg_one_pow]
            norm_num
        · -- exactly at the `-3`
          have hn1 : n = a + 1 := by omega
          subst hn1
          have hw : insWeight a (a + 1) = -3 := by
            unfold insWeight
            rw [if_neg (by omega), if_pos rfl]
          rw [hw, if_pos rfl, if_neg (by omega : a + 1 + 1 ≠ a + 1)]
          rcases Nat.even_or_odd a with he | ho
          · have : Even (a + 1 + 1) := by simpa using (he.add_one : Odd (a + 1)).add_one
            rw [if_pos he, if_pos this]; norm_num
          · have : ¬ Even (a + 1 + 1) := by
              simpa using ((ho.add_one : Even (a + 1)).add_one : Odd (a + 1 + 1))
            rw [if_neg (by simpa using ho), if_neg this]; norm_num

/-- **The excess profile: a single spike.**  Budget `a+1` carries excess exactly two, and
every other budget carries none. -/
theorem insRanking_excess (m a : ℕ) (ha : a + 1 < m) (k : ℕ) (hk : k ≤ m) :
    excess (insRanking m a) k = if k = a + 1 then (2 : ℝ) else 0 := by
  unfold excess
  rw [insRanking_prefix m a ha k hk]
  by_cases hka : k = a + 1
  · subst hka
    rw [if_pos rfl, if_pos rfl]
    rcases Nat.even_or_odd a with he | ho
    · have h0 : a % 2 = 0 := Nat.even_iff.mp he
      have h1 : (a + 1) % 2 = 1 := by omega
      rw [if_pos he, h1]
      norm_num
    · have h0 : a % 2 = 1 := Nat.odd_iff.mp ho
      have h1 : (a + 1) % 2 = 0 := by omega
      rw [if_neg (by simpa using ho), h1]
      norm_num
  · rw [if_neg hka, if_neg hka]
    rcases Nat.even_or_odd k with he | ho
    · have h0 : k % 2 = 0 := Nat.even_iff.mp he
      rw [if_pos he, h0]
      norm_num
    · have h0 : k % 2 = 1 := Nat.odd_iff.mp ho
      rw [if_neg (by simpa using ho), h0]
      norm_num

/-- **(O1), the attainment half: the mixture reaches the free value at EVERY budget.**

Averaging the single spike over `a` uniform on `{0, ..., m-2}` puts exactly
`2 / (D (m-1)) = V^free_m` at each budget `k` in range -- one `a` contributes `2/D` and the
rest contribute nothing.  So the unconstrained optimum is attained by a distribution over
genuine rankings, for every `m`, and not only at the sizes the solver reaches.

What this does NOT yet give is that the mixture satisfies the marginal band at `eta_*(m)`.
That is the remaining half of (O1); it is verified in exact rational arithmetic at
`m = 4, ..., 24` by `EXP_paperC_general_m.py`, with the worst band slack exactly zero at
`eta_*(m)`, and it is open for general `m`. -/
theorem insMixture_free_value (m : ℕ) (hm : 1 < m) (D : ℝ) (hD : D ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    ∑ a ∈ Finset.range (m - 1), (1 / ((m : ℝ) - 1)) * (excess (insRanking m a) k / D)
      = 2 / (D * ((m : ℝ) - 1)) := by
  classical
  have hmr : ((m : ℝ) - 1) ≠ 0 := by
    have h1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hterm : ∀ a ∈ Finset.range (m - 1),
      (1 / ((m : ℝ) - 1)) * (excess (insRanking m a) k / D)
        = if a = k - 1 then (1 / ((m : ℝ) - 1)) * (2 / D) else 0 := by
    intro a ha
    have hain := Finset.mem_range.mp ha
    have haa : a + 1 < m := by omega
    rw [insRanking_excess m a haa k (by omega)]
    by_cases h : a = k - 1
    · rw [if_pos h, if_pos (by omega : k = a + 1)]
    · rw [if_neg h, if_neg (by omega : k ≠ a + 1)]
      simp
  rw [Finset.sum_congr rfl hterm,
      Finset.sum_ite_eq' (Finset.range (m - 1)) (k - 1)
        (fun _ => (1 / ((m : ℝ) - 1)) * (2 / D)),
      if_pos (Finset.mem_range.mpr (by omega))]
  field_simp

/-- Every ranking in the mixture is one of the family's, so the mixture is a distribution
over genuine rankings and not over abstract paths. -/
theorem insRanking_weights (m a : ℕ) (ha : a + 1 < m) (i : Fin m) :
    insRanking m a i = -3 ∨ insRanking m a i = -1 ∨ insRanking m a i = 1
      ∨ insRanking m a i = 3 := by
  unfold insRanking insWeight
  split_ifs with h1 h2 h3
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl rfl
  · rcases Nat.even_or_odd ((i : ℕ) + 1) with he | ho
    · exact Or.inr (Or.inr (Or.inl he.neg_one_pow))
    · exact Or.inr (Or.inl ho.neg_one_pow)
  · rcases Nat.even_or_odd ((i : ℕ) - 1) with he | ho
    · exact Or.inr (Or.inr (Or.inl he.neg_one_pow))
    · exact Or.inr (Or.inl ho.neg_one_pow)

/-! ## (O1), the band half: what each budget sees of each type

The attainment above says the mixture reaches the free value.  Feasibility says it obeys the
marginal band at `eta_*(m)`.  The band is a statement about each item's chance of occupying
each prefix, and the relabelling of `LeanPaperCBreakpointV1` turns that into a statement
about the expected COUNT of each type in each prefix.  So what has to be computed is

    E[ #{ positions < k carrying weight w } ]   for w in {-3, -1, +1, +3}.

For the inserted ranking `pi_a` that count is elementary, because the construction says
exactly where everything is: the `+3` sits at `a`, the `-3` at `a+1`, and every other
position carries `-1` when its index is even and `+1` when it is odd -- the insertion shifts
later base indices by two, which does not change their parity.  That last observation is
what keeps the count free of case analysis on `a`. -/

/-- The number of positions below `k` carrying weight `w` in the inserted ranking, written
as a sum of indicators so that the identities below are sum manipulations rather than
cardinality arithmetic. -/
noncomputable def countIns (a : ℕ) (w : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (if insWeight a i = w then (1 : ℝ) else 0)

/-- How many of the first `k` positions are even. -/
noncomputable def evensBelow (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (if Even i then (1 : ℝ) else 0)

/-- How many of the first `k` positions are odd. -/
noncomputable def oddsBelow (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (if ¬ Even i then (1 : ℝ) else 0)

theorem evens_add_odds (k : ℕ) : evensBelow k + oddsBelow k = (k : ℝ) := by
  unfold evensBelow oddsBelow
  rw [← Finset.sum_add_distrib]
  have : ∀ i ∈ Finset.range k,
      (if Even i then (1 : ℝ) else 0) + (if ¬ Even i then (1 : ℝ) else 0) = 1 := by
    intro i _
    by_cases h : Even i
    · rw [if_pos h, if_neg (by simpa using h)]; ring
    · rw [if_neg h, if_pos h]; ring
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

theorem evensBelow_two (j : ℕ) : evensBelow (2 * j) = (j : ℝ) := by
  induction j with
  | zero => simp [evensBelow]
  | succ n ih =>
      have hstep : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
      unfold evensBelow at ih ⊢
      rw [hstep, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h1 : Even (2 * n) := ⟨n, by ring⟩
      have h2 : ¬ Even (2 * n + 1) := by simpa using (h1.add_one : Odd (2 * n + 1))
      rw [if_neg h2, if_pos h1]
      push_cast
      ring

theorem evensBelow_two_succ (j : ℕ) : evensBelow (2 * j + 1) = (j : ℝ) + 1 := by
  unfold evensBelow
  rw [Finset.sum_range_succ]
  have h1 : Even (2 * j) := ⟨j, by ring⟩
  rw [if_pos h1]
  have := evensBelow_two j
  unfold evensBelow at this
  rw [this]

theorem oddsBelow_two (j : ℕ) : oddsBelow (2 * j) = (j : ℝ) := by
  have h := evens_add_odds (2 * j)
  rw [evensBelow_two j] at h
  push_cast at h
  linarith

theorem oddsBelow_two_succ (j : ℕ) : oddsBelow (2 * j + 1) = (j : ℝ) := by
  have h := evens_add_odds (2 * j + 1)
  rw [evensBelow_two_succ j] at h
  push_cast at h
  linarith

theorem neg_one_pow_ne_three (j : ℕ) : (-1 : ℝ) ^ j ≠ 3 := by
  rcases Nat.even_or_odd j with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num

theorem neg_one_pow_ne_neg_three (j : ℕ) : (-1 : ℝ) ^ j ≠ -3 := by
  rcases Nat.even_or_odd j with he | ho
  · rw [he.neg_one_pow]; norm_num
  · rw [ho.neg_one_pow]; norm_num

theorem insWeight_eq_three_iff (a i : ℕ) : insWeight a i = 3 ↔ i = a := by
  constructor
  · intro h
    by_contra hne
    unfold insWeight at h
    rw [if_neg hne] at h
    by_cases h2 : i = a + 1
    · rw [if_pos h2] at h; norm_num at h
    · rw [if_neg h2] at h
      split_ifs at h
      · exact neg_one_pow_ne_three _ h
      · exact neg_one_pow_ne_three _ h
  · intro h
    subst h
    unfold insWeight
    rw [if_pos rfl]

theorem insWeight_eq_neg_three_iff (a i : ℕ) : insWeight a i = -3 ↔ i = a + 1 := by
  constructor
  · intro h
    by_contra hne
    unfold insWeight at h
    by_cases h1 : i = a
    · rw [if_pos h1] at h; norm_num at h
    · rw [if_neg h1, if_neg hne] at h
      split_ifs at h
      · exact neg_one_pow_ne_neg_three _ h
      · exact neg_one_pow_ne_neg_three _ h
  · intro h
    subst h
    unfold insWeight
    rw [if_neg (by omega), if_pos rfl]

/-- Away from the inserted pair the weight is `-1` exactly at the EVEN positions.  The
insertion shifts later base indices by two, so it does not move any parity -- which is what
keeps the count below free of a case analysis on `a`. -/
theorem insWeight_eq_neg_one_iff (a i : ℕ) :
    insWeight a i = -1 ↔ (i ≠ a ∧ i ≠ a + 1 ∧ Even i) := by
  unfold insWeight
  by_cases h1 : i = a
  · rw [if_pos h1]
    simp only [h1, ne_eq, not_true_eq_false, false_and]
    norm_num
  · by_cases h2 : i = a + 1
    · rw [if_neg h1, if_pos h2]
      simp only [h2, ne_eq, not_true_eq_false, false_and, and_false]
      norm_num
    · rw [if_neg h1, if_neg h2]
      by_cases h3 : i < a
      · rw [if_pos h3]
        constructor
        · intro h
          refine ⟨h1, h2, ?_⟩
          rcases Nat.even_or_odd i with he | ho
          · exact he
          · rw [(ho.add_one : Even (i + 1)).neg_one_pow] at h
            norm_num at h
        · rintro ⟨-, -, he⟩
          rw [(he.add_one : Odd (i + 1)).neg_one_pow]
      · rw [if_neg h3]
        obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by omega⟩
        rw [show c + 1 - 1 = c from rfl]
        constructor
        · intro h
          refine ⟨h1, h2, ?_⟩
          rcases Nat.even_or_odd c with he | ho
          · rw [he.neg_one_pow] at h
            norm_num at h
          · exact ho.add_one
        · rintro ⟨-, -, he⟩
          have hc : Odd c := by
            rcases Nat.even_or_odd c with h | h
            · exact absurd he (Nat.not_even_iff_odd.mpr h.add_one)
            · exact h
          rw [hc.neg_one_pow]

/-- And `+1` exactly at the odd positions away from the pair. -/
theorem insWeight_eq_one_iff (a i : ℕ) :
    insWeight a i = 1 ↔ (i ≠ a ∧ i ≠ a + 1 ∧ ¬ Even i) := by
  unfold insWeight
  by_cases h1 : i = a
  · rw [if_pos h1]
    simp only [h1, ne_eq, not_true_eq_false, false_and]
    norm_num
  · by_cases h2 : i = a + 1
    · rw [if_neg h1, if_pos h2]
      simp only [h2, ne_eq, not_true_eq_false, false_and, and_false]
      norm_num
    · rw [if_neg h1, if_neg h2]
      by_cases h3 : i < a
      · rw [if_pos h3]
        constructor
        · intro h
          refine ⟨h1, h2, ?_⟩
          rcases Nat.even_or_odd i with he | ho
          · rw [(he.add_one : Odd (i + 1)).neg_one_pow] at h
            norm_num at h
          · exact Nat.not_even_iff_odd.mpr ho
        · rintro ⟨-, -, he⟩
          rw [((Nat.not_even_iff_odd.mp he).add_one : Even (i + 1)).neg_one_pow]
      · rw [if_neg h3]
        obtain ⟨c, rfl⟩ : ∃ c, i = c + 1 := ⟨i - 1, by omega⟩
        rw [show c + 1 - 1 = c from rfl]
        constructor
        · intro h
          refine ⟨h1, h2, ?_⟩
          rcases Nat.even_or_odd c with he | ho
          · exact Nat.not_even_iff_odd.mpr he.add_one
          · rw [ho.neg_one_pow] at h
            norm_num at h
        · rintro ⟨-, -, he⟩
          have hc : Even c := by
            rcases Nat.even_or_odd c with h | h
            · exact h
            · exact absurd (h.add_one) (Nat.not_even_iff_odd.mp he |> fun hh => by
                simpa using hh)
          rw [hc.neg_one_pow]

/-! ### The four counts -/

theorem countIns_three (a k : ℕ) :
    countIns a 3 k = if a < k then (1 : ℝ) else 0 := by
  unfold countIns
  have hpt : ∀ i ∈ Finset.range k,
      (if insWeight a i = 3 then (1 : ℝ) else 0) = if i = a then (1 : ℝ) else 0 := by
    intro i _
    by_cases h : i = a
    · rw [if_pos ((insWeight_eq_three_iff a i).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((insWeight_eq_three_iff a i).mp hc)), if_neg h]
  rw [Finset.sum_congr rfl hpt,
      Finset.sum_ite_eq' (Finset.range k) a (fun _ => (1 : ℝ))]
  by_cases h : a < k
  · rw [if_pos (Finset.mem_range.mpr h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

theorem countIns_neg_three (a k : ℕ) :
    countIns a (-3) k = if a + 1 < k then (1 : ℝ) else 0 := by
  unfold countIns
  have hpt : ∀ i ∈ Finset.range k,
      (if insWeight a i = -3 then (1 : ℝ) else 0) = if i = a + 1 then (1 : ℝ) else 0 := by
    intro i _
    by_cases h : i = a + 1
    · rw [if_pos ((insWeight_eq_neg_three_iff a i).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((insWeight_eq_neg_three_iff a i).mp hc)), if_neg h]
  rw [Finset.sum_congr rfl hpt,
      Finset.sum_ite_eq' (Finset.range k) (a + 1) (fun _ => (1 : ℝ))]
  by_cases h : a + 1 < k
  · rw [if_pos (Finset.mem_range.mpr h), if_pos h]
  · rw [if_neg (by simpa using h), if_neg h]

theorem countIns_neg_one (a k : ℕ) :
    countIns a (-1) k = evensBelow k
      - (if a < k ∧ Even a then (1 : ℝ) else 0)
      - (if a + 1 < k ∧ Even (a + 1) then (1 : ℝ) else 0) := by
  unfold countIns evensBelow
  have hpt : ∀ i ∈ Finset.range k,
      (if insWeight a i = -1 then (1 : ℝ) else 0)
        = (if Even i then (1 : ℝ) else 0)
          - (if i = a ∧ Even a then (1 : ℝ) else 0)
          - (if i = a + 1 ∧ Even (a + 1) then (1 : ℝ) else 0) := by
    intro i _
    by_cases h1 : i = a
    · subst h1
      rw [(insWeight_eq_three_iff i i).mpr rfl,
          if_neg (by norm_num : ¬ ((3 : ℝ) = -1)),
          if_neg (fun hc : i = i + 1 ∧ Even (i + 1) => absurd hc.1 (by omega))]
      by_cases he : Even i
      · rw [if_pos he, if_pos (⟨rfl, he⟩ : i = i ∧ Even i)]; ring
      · rw [if_neg he, if_neg (fun hc : i = i ∧ Even i => he hc.2)]; ring
    · by_cases h2 : i = a + 1
      · subst h2
        rw [(insWeight_eq_neg_three_iff a (a + 1)).mpr rfl,
            if_neg (by norm_num : ¬ ((-3 : ℝ) = -1)),
            if_neg (fun hc : a + 1 = a ∧ Even a => h1 hc.1)]
        by_cases he : Even (a + 1)
        · rw [if_pos he, if_pos (⟨rfl, he⟩ : a + 1 = a + 1 ∧ Even (a + 1))]; ring
        · rw [if_neg he,
              if_neg (fun hc : a + 1 = a + 1 ∧ Even (a + 1) => he hc.2)]; ring
      · rw [if_neg (fun hc : i = a ∧ Even a => h1 hc.1),
            if_neg (fun hc : i = a + 1 ∧ Even (a + 1) => h2 hc.1)]
        by_cases he : Even i
        · rw [if_pos ((insWeight_eq_neg_one_iff a i).mpr ⟨h1, h2, he⟩), if_pos he]; ring
        · rw [if_neg (fun hc : insWeight a i = -1 =>
                he ((insWeight_eq_neg_one_iff a i).mp hc).2.2), if_neg he]
          ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hpick : ∀ b : ℕ, (∑ x ∈ Finset.range k, if x = b ∧ Even b then (1 : ℝ) else 0)
      = if b < k ∧ Even b then (1 : ℝ) else 0 := by
    intro b
    by_cases he : Even b
    · have hrw : ∀ x ∈ Finset.range k,
          (if x = b ∧ Even b then (1 : ℝ) else 0) = if x = b then (1 : ℝ) else 0 := by
        intro x _
        by_cases hx : x = b
        · rw [if_pos (⟨hx, he⟩ : x = b ∧ Even b), if_pos hx]
        · rw [if_neg (fun hc : x = b ∧ Even b => hx hc.1), if_neg hx]
      rw [Finset.sum_congr rfl hrw,
          Finset.sum_ite_eq' (Finset.range k) b (fun _ => (1 : ℝ))]
      by_cases h : b < k
      · rw [if_pos (Finset.mem_range.mpr h), if_pos (⟨h, he⟩ : b < k ∧ Even b)]
      · rw [if_neg (by simpa using h : b ∉ Finset.range k),
            if_neg (fun hc : b < k ∧ Even b => h hc.1)]
    · rw [Finset.sum_eq_zero (fun x _ => by
            rw [if_neg (fun hc : x = b ∧ Even b => he hc.2)]),
          if_neg (fun hc : b < k ∧ Even b => he hc.2)]
  rw [hpick a, hpick (a + 1)]

theorem countIns_one (a k : ℕ) :
    countIns a 1 k = oddsBelow k
      - (if a < k ∧ ¬ Even a then (1 : ℝ) else 0)
      - (if a + 1 < k ∧ ¬ Even (a + 1) then (1 : ℝ) else 0) := by
  unfold countIns oddsBelow
  have hpt : ∀ i ∈ Finset.range k,
      (if insWeight a i = 1 then (1 : ℝ) else 0)
        = (if ¬ Even i then (1 : ℝ) else 0)
          - (if i = a ∧ ¬ Even a then (1 : ℝ) else 0)
          - (if i = a + 1 ∧ ¬ Even (a + 1) then (1 : ℝ) else 0) := by
    intro i _
    by_cases h1 : i = a
    · subst h1
      rw [(insWeight_eq_three_iff i i).mpr rfl,
          if_neg (by norm_num : ¬ ((3 : ℝ) = 1)),
          if_neg (fun hc : i = i + 1 ∧ ¬ Even (i + 1) => absurd hc.1 (by omega))]
      by_cases he : Even i
      · rw [if_neg (by simpa using he), if_neg (fun hc : i = i ∧ ¬ Even i => hc.2 he)]
        ring
      · rw [if_pos he, if_pos (⟨rfl, he⟩ : i = i ∧ ¬ Even i)]; ring
    · by_cases h2 : i = a + 1
      · subst h2
        rw [(insWeight_eq_neg_three_iff a (a + 1)).mpr rfl,
            if_neg (by norm_num : ¬ ((-3 : ℝ) = 1)),
            if_neg (fun hc : a + 1 = a ∧ ¬ Even a => h1 hc.1)]
        by_cases he : Even (a + 1)
        · rw [if_neg (by simpa using he),
              if_neg (fun hc : a + 1 = a + 1 ∧ ¬ Even (a + 1) => hc.2 he)]
          ring
        · rw [if_pos he, if_pos (⟨rfl, he⟩ : a + 1 = a + 1 ∧ ¬ Even (a + 1))]; ring
      · rw [if_neg (fun hc : i = a ∧ ¬ Even a => h1 hc.1),
            if_neg (fun hc : i = a + 1 ∧ ¬ Even (a + 1) => h2 hc.1)]
        by_cases he : Even i
        · rw [if_neg (fun hc : insWeight a i = 1 =>
                ((insWeight_eq_one_iff a i).mp hc).2.2 he), if_neg (by simpa using he)]
          ring
        · rw [if_pos ((insWeight_eq_one_iff a i).mpr ⟨h1, h2, he⟩), if_pos he]; ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hpick : ∀ b : ℕ, (∑ x ∈ Finset.range k, if x = b ∧ ¬ Even b then (1 : ℝ) else 0)
      = if b < k ∧ ¬ Even b then (1 : ℝ) else 0 := by
    intro b
    by_cases he : Even b
    · rw [Finset.sum_eq_zero (fun x _ => by
            rw [if_neg (fun hc : x = b ∧ ¬ Even b => hc.2 he)]),
          if_neg (fun hc : b < k ∧ ¬ Even b => hc.2 he)]
    · have hrw : ∀ x ∈ Finset.range k,
          (if x = b ∧ ¬ Even b then (1 : ℝ) else 0) = if x = b then (1 : ℝ) else 0 := by
        intro x _
        by_cases hx : x = b
        · rw [if_pos (⟨hx, he⟩ : x = b ∧ ¬ Even b), if_pos hx]
        · rw [if_neg (fun hc : x = b ∧ ¬ Even b => hx hc.1), if_neg hx]
      rw [Finset.sum_congr rfl hrw,
          Finset.sum_ite_eq' (Finset.range k) b (fun _ => (1 : ℝ))]
      by_cases h : b < k
      · rw [if_pos (Finset.mem_range.mpr h), if_pos (⟨h, he⟩ : b < k ∧ ¬ Even b)]
      · rw [if_neg (by simpa using h : b ∉ Finset.range k),
            if_neg (fun hc : b < k ∧ ¬ Even b => h hc.1)]
  rw [hpick a, hpick (a + 1)]

/-! ### Averaging over the insertion point

The mixture is uniform over `a in {0, ..., m-2}`, so each expected count is an average of
the counts above.  All four come out in closed form, and none of them needs a case analysis
on `a` -- that was the point of the parity observation. -/

theorem sum_ind_lt (n k : ℕ) (hk : k ≤ n) :
    (∑ a ∈ Finset.range n, if a < k then (1 : ℝ) else 0) = (k : ℝ) := by
  have hset : (Finset.range n).filter (fun a => a < k) = Finset.range k := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [Finset.sum_boole, hset, Finset.card_range]

theorem sum_ind_lt_even (n k : ℕ) (hk : k ≤ n) :
    (∑ a ∈ Finset.range n, if a < k ∧ Even a then (1 : ℝ) else 0) = evensBelow k := by
  unfold evensBelow
  rw [Finset.sum_boole, Finset.sum_boole]
  norm_cast
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩

theorem sum_ind_lt_odd (n k : ℕ) (hk : k ≤ n) :
    (∑ a ∈ Finset.range n, if a < k ∧ ¬ Even a then (1 : ℝ) else 0) = oddsBelow k := by
  unfold oddsBelow
  rw [Finset.sum_boole, Finset.sum_boole]
  norm_cast
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩

/-- Shifting the insertion point by one: summing `g (a+1)` over `range n` is summing `g`
over `range (n+1)` with the `0` term removed. -/
theorem sum_shift (n : ℕ) (g : ℕ → ℝ) :
    (∑ a ∈ Finset.range n, g (a + 1)) = (∑ b ∈ Finset.range (n + 1), g b) - g 0 := by
  rw [Finset.sum_range_succ' g n]
  ring

/-- The expected count of weight `w` in the first `k` positions. -/
noncomputable def mixCount (m : ℕ) (w : ℝ) (k : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (m - 1), (1 / ((m : ℝ) - 1)) * countIns a w k

theorem mixCount_three (m k : ℕ) (hm : 1 < m) (hk : k ≤ m - 1) :
    mixCount m 3 k = (k : ℝ) / ((m : ℝ) - 1) := by
  unfold mixCount
  rw [← Finset.mul_sum, Finset.sum_congr rfl (fun a _ => countIns_three a k),
      sum_ind_lt (m - 1) k hk]
  ring

theorem mixCount_neg_three (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixCount m (-3) k = ((k : ℝ) - 1) / ((m : ℝ) - 1) := by
  unfold mixCount
  rw [← Finset.mul_sum, Finset.sum_congr rfl (fun a _ => countIns_neg_three a k)]
  have hrw : ∀ a : ℕ, (if a + 1 < k then (1 : ℝ) else 0) = (if a < k - 1 then (1 : ℝ) else 0) := by
    intro a
    by_cases h : a + 1 < k
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [Finset.sum_congr rfl (fun a _ => hrw a), sum_ind_lt (m - 1) (k - 1) (by omega)]
  have hkc : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    have : (1 : ℕ) ≤ k := hk1
    push_cast [Nat.cast_sub this]
    ring
  rw [hkc]
  ring

theorem mixCount_neg_one (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixCount m (-1) k
      = evensBelow k - (2 * evensBelow k - 1) / ((m : ℝ) - 1) := by
  unfold mixCount
  rw [← Finset.mul_sum, Finset.sum_congr rfl (fun a _ => countIns_neg_one a k)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      sum_ind_lt_even (m - 1) k hk]
  have hshift : (∑ a ∈ Finset.range (m - 1),
      if a + 1 < k ∧ Even (a + 1) then (1 : ℝ) else 0) = evensBelow k - 1 := by
    rw [sum_shift (m - 1) (fun b => if b < k ∧ Even b then (1 : ℝ) else 0)]
    have hmm : m - 1 + 1 = m := by omega
    rw [hmm, sum_ind_lt_even m k (by omega),
        if_pos (⟨by omega, (⟨0, rfl⟩ : Even 0)⟩ : 0 < k ∧ Even 0)]
  rw [hshift]
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hcard : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hcard]
  field_simp
  ring

theorem mixCount_one (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixCount m 1 k = oddsBelow k - 2 * oddsBelow k / ((m : ℝ) - 1) := by
  unfold mixCount
  rw [← Finset.mul_sum, Finset.sum_congr rfl (fun a _ => countIns_one a k)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      sum_ind_lt_odd (m - 1) k hk]
  have hshift : (∑ a ∈ Finset.range (m - 1),
      if a + 1 < k ∧ ¬ Even (a + 1) then (1 : ℝ) else 0) = oddsBelow k := by
    rw [sum_shift (m - 1) (fun b => if b < k ∧ ¬ Even b then (1 : ℝ) else 0)]
    have hmm : m - 1 + 1 = m := by omega
    rw [hmm, sum_ind_lt_odd m k (by omega),
        if_neg (fun hc : 0 < k ∧ ¬ Even 0 => hc.2 (⟨0, rfl⟩ : Even 0))]
    ring
  rw [hshift]
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hcard : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    have : (1 : ℕ) ≤ m := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hcard]
  field_simp
  ring

/-! ### The marginal band, at `eta_* = 1` for odd `m`

The band asks, for each type `tau` with `c_tau` items,

    | E[count_tau(k)] - c_tau * k / m |  <=  c_tau * eta / m.

For odd `m` the law says `eta_* = 1`, and here are the four inequalities at that value.
The heavy types are tight: the `+3` band holds with equality at `k = m-1`, which is what
pins `eta_*` at `1` and not below.  The light types have slack.

Together with `insMixture_free_value` this is (O1) for odd `m`: a distribution over genuine
rankings that attains the free value at every budget AND satisfies the band at `eta_* = 1`.
-/

/-- `k` and `m` as reals, with the facts the band arithmetic needs. -/
theorem band_setup (m k : ℕ) (hm : 3 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    (3 : ℝ) ≤ (m : ℝ) ∧ (1 : ℝ) ≤ (k : ℝ) ∧ (k : ℝ) ≤ (m : ℝ) - 1 := by
  refine ⟨by exact_mod_cast hm, by exact_mod_cast hk1, ?_⟩
  have h : (k : ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast hk
  have h1 : (1 : ℕ) ≤ m := by omega
  have hc : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by push_cast [Nat.cast_sub h1]; ring
  linarith [hc ▸ h]

theorem band_three (m k : ℕ) (hm : 3 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |mixCount m 3 k - 1 * ((k : ℝ) / (m : ℝ))| ≤ 1 * (1 / (m : ℝ)) := by
  obtain ⟨hmr, hkr1, hkrm⟩ := band_setup m k hm hk1 hk
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  rw [mixCount_three m k (by omega) hk, one_mul, one_mul]
  have hdiff : (k : ℝ) / ((m : ℝ) - 1) - (k : ℝ) / (m : ℝ)
      = (k : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
    field_simp
    ring
  rw [hdiff, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) hm0]
  nlinarith [hkrm, hm0, hm1]

theorem band_neg_three (m k : ℕ) (hm : 3 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |mixCount m (-3) k - 1 * ((k : ℝ) / (m : ℝ))| ≤ 1 * (1 / (m : ℝ)) := by
  obtain ⟨hmr, hkr1, hkrm⟩ := band_setup m k hm hk1 hk
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  rw [mixCount_neg_three m k (by omega) hk1 hk, one_mul, one_mul]
  have hdiff : ((k : ℝ) - 1) / ((m : ℝ) - 1) - (k : ℝ) / (m : ℝ)
      = -(((m : ℝ) - (k : ℝ)) / ((m : ℝ) * ((m : ℝ) - 1))) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ ((m : ℝ) - (k : ℝ)) / ((m : ℝ) * ((m : ℝ) - 1)) :=
    div_nonneg (by linarith) (by positivity)
  rw [hdiff, abs_neg, abs_of_nonneg hnn, div_le_div_iff₀ (by positivity) hm0]
  nlinarith [hkr1, hm0, hm1]

/-- The core estimate for the `+1` band: one inequality covering both parities of `k`. -/
theorem odds_band_core (m k : ℕ) (hm : 3 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |2 * (m : ℝ) * oddsBelow k - (k : ℝ) * ((m : ℝ) - 1)| ≤ (m : ℝ) - 1 := by
  obtain ⟨hmr, hkr1, hkrm⟩ := band_setup m k hm hk1 hk
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨j, hj⟩ := he
    have hk2 : k = 2 * j := by omega
    subst hk2
    rw [oddsBelow_two j]
    have hjr : (2 : ℝ) * (j : ℝ) ≤ (m : ℝ) - 1 := by push_cast at hkrm ⊢; linarith
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hval : 2 * (m : ℝ) * (j : ℝ) - ((2 * j : ℕ) : ℝ) * ((m : ℝ) - 1)
        = 2 * (j : ℝ) := by push_cast; ring
    rw [hval, abs_of_nonneg (by linarith)]
    linarith
  · obtain ⟨j, hj⟩ := ho
    have hk2 : k = 2 * j + 1 := by omega
    subst hk2
    rw [oddsBelow_two_succ j]
    have hval : 2 * (m : ℝ) * (j : ℝ) - ((2 * j + 1 : ℕ) : ℝ) * ((m : ℝ) - 1)
        = ((2 * j + 1 : ℕ) : ℝ) - (m : ℝ) := by push_cast; ring
    rw [hval, abs_of_nonpos (by linarith), neg_sub]
    linarith

/-- The core estimate for the `-1` band.  The even-`k` case uses `k >= 2`, and the odd-`k`
case uses that `m` is odd, so `k` cannot reach `m - 1`. -/
theorem evens_band_core (m k : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (hk1 : 1 ≤ k)
    (hk : k ≤ m - 1) :
    |2 * (m : ℝ) * ((m : ℝ) - 3) * evensBelow k + 2 * (m : ℝ)
        - (k : ℝ) * ((m : ℝ) - 1) ^ 2| ≤ ((m : ℝ) - 1) ^ 2 := by
  obtain ⟨hmr, hkr1, hkrm⟩ := band_setup m k hm hk1 hk
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨j, hj⟩ := he
    have hk2 : k = 2 * j := by omega
    subst hk2
    have hj1 : 1 ≤ j := by omega
    have hjr1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjr : (2 : ℝ) * (j : ℝ) ≤ (m : ℝ) - 1 := by push_cast at hkrm ⊢; linarith
    rw [evensBelow_two j]
    have hval : 2 * (m : ℝ) * ((m : ℝ) - 3) * (j : ℝ) + 2 * (m : ℝ)
        - ((2 * j : ℕ) : ℝ) * ((m : ℝ) - 1) ^ 2
        = -(2 * ((j : ℝ) * ((m : ℝ) + 1) - (m : ℝ))) := by push_cast; ring
    rw [hval, abs_neg, abs_of_nonneg (by nlinarith [hjr1, hmr])]
    nlinarith [hjr, hmr, hjr1]
  · obtain ⟨j, hj⟩ := ho
    have hk2 : k = 2 * j + 1 := by omega
    subst hk2
    have hjm : 2 * j ≤ m - 3 := by omega
    have hjr : (2 : ℝ) * (j : ℝ) ≤ (m : ℝ) - 3 := by
      have h : (2 * j : ℕ) ≤ m - 3 := hjm
      have hc : ((m - 3 : ℕ) : ℝ) = (m : ℝ) - 3 := by
        have h3 : (3 : ℕ) ≤ m := hm
        push_cast [Nat.cast_sub h3]; ring
      have := (Nat.cast_le (α := ℝ)).mpr h
      push_cast at this
      linarith [hc ▸ this]
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    rw [evensBelow_two_succ j]
    have hval : 2 * (m : ℝ) * ((m : ℝ) - 3) * ((j : ℝ) + 1) + 2 * (m : ℝ)
        - ((2 * j + 1 : ℕ) : ℝ) * ((m : ℝ) - 1) ^ 2
        = (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1 - 2 * (j : ℝ) * ((m : ℝ) + 1) := by
      push_cast; ring
    rw [hval, abs_le]
    constructor
    · nlinarith [hjr, hmr, hj0]
    · nlinarith [hj0, hmr]

theorem band_one (m k : ℕ) (hm : 3 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |mixCount m 1 k - (((m : ℝ) - 3) / 2) * ((k : ℝ) / (m : ℝ))|
      ≤ (((m : ℝ) - 3) / 2) * (1 / (m : ℝ)) := by
  obtain ⟨hmr, hkr1, hkrm⟩ := band_setup m k hm hk1 hk
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hfac : (0 : ℝ) ≤ ((m : ℝ) - 3) / (2 * (m : ℝ) * ((m : ℝ) - 1)) :=
    div_nonneg (by linarith) (by positivity)
  rw [mixCount_one m k (by omega) hk1 hk]
  have hid : (oddsBelow k - 2 * oddsBelow k / ((m : ℝ) - 1))
      - (((m : ℝ) - 3) / 2) * ((k : ℝ) / (m : ℝ))
      = ((m : ℝ) - 3) / (2 * (m : ℝ) * ((m : ℝ) - 1))
        * (2 * (m : ℝ) * oddsBelow k - (k : ℝ) * ((m : ℝ) - 1)) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_of_nonneg hfac]
  refine le_trans (mul_le_mul_of_nonneg_left (odds_band_core m k hm hk1 hk) hfac) ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  field_simp
  ring_nf
  nlinarith [hm0, hm1, hmr]

theorem band_neg_one (m k : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (hk1 : 1 ≤ k)
    (hk : k ≤ m - 1) :
    |mixCount m (-1) k - (((m : ℝ) - 1) / 2) * ((k : ℝ) / (m : ℝ))|
      ≤ (((m : ℝ) - 1) / 2) * (1 / (m : ℝ)) := by
  obtain ⟨hmr, hkr1, hkrm⟩ := band_setup m k hm hk1 hk
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hfac : (0 : ℝ) < 1 / (2 * (m : ℝ) * ((m : ℝ) - 1)) := by positivity
  rw [mixCount_neg_one m k (by omega) hk1 hk]
  have hid : (evensBelow k - (2 * evensBelow k - 1) / ((m : ℝ) - 1))
      - (((m : ℝ) - 1) / 2) * ((k : ℝ) / (m : ℝ))
      = 1 / (2 * (m : ℝ) * ((m : ℝ) - 1))
        * (2 * (m : ℝ) * ((m : ℝ) - 3) * evensBelow k + 2 * (m : ℝ)
            - (k : ℝ) * ((m : ℝ) - 1) ^ 2) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_of_nonneg hfac.le]
  refine le_trans
    (mul_le_mul_of_nonneg_left (evens_band_core m k hm hmo hk1 hk) hfac.le) ?_
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  field_simp
  ring_nf
  nlinarith [hm0, hm1, hmr]

/-! ### The even case: mixing with the sign flip

For even `m` the family has equally many `+1` and `-1`, so negating every weight is again a
ranking of the SAME family.  Mixing each `pi_a` half and half with its flip symmetrises the
two heavy items and the two light types, and the band then holds at the smaller value
`eta_*(m) = (m-2)/(2(m-1))`.

The flip costs nothing on the objective: `insRanking_excess` depends on the weights only
through `|S_k|`, and flipping every sign negates every prefix sum. -/

/-- The count under the sign-flipped ranking. -/
noncomputable def countInsFlip (a : ℕ) (w : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (if -(insWeight a i) = w then (1 : ℝ) else 0)

theorem countInsFlip_eq (a : ℕ) (w : ℝ) (k : ℕ) :
    countInsFlip a w k = countIns a (-w) k := by
  unfold countInsFlip countIns
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : insWeight a i = -w
  · rw [if_pos (by rw [h]; ring), if_pos h]
  · rw [if_neg (fun hc => h (by linarith)), if_neg h]

/-- The even mixture's expected count: the insertion mixture, averaged with its flip. -/
noncomputable def mixCountEven (m : ℕ) (w : ℝ) (k : ℕ) : ℝ :=
  (mixCount m w k + mixCount m (-w) k) / 2

theorem mixCountEven_three (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixCountEven m 3 k = (2 * (k : ℝ) - 1) / (2 * ((m : ℝ) - 1)) := by
  unfold mixCountEven
  rw [mixCount_three m k hm hk, show ((-3 : ℝ)) = -(3 : ℝ) from rfl]
  rw [mixCount_neg_three m k hm hk1 hk]
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  field_simp
  ring

theorem mixCountEven_one (m k : ℕ) (hm : 1 < m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    mixCountEven m 1 k = ((k : ℝ) * ((m : ℝ) - 3) + 1) / (2 * ((m : ℝ) - 1)) := by
  unfold mixCountEven
  rw [mixCount_one m k hm hk1 hk, show ((-1 : ℝ)) = -(1 : ℝ) from rfl]
  rw [mixCount_neg_one m k hm hk1 hk]
  have hm1 : ((m : ℝ) - 1) ≠ 0 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    linarith
  have hsum : evensBelow k + oddsBelow k = (k : ℝ) := evens_add_odds k
  field_simp
  nlinarith [hsum]

theorem band_even_three (m k : ℕ) (hm : 4 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |mixCountEven m 3 k - 1 * ((k : ℝ) / (m : ℝ))|
      ≤ 1 * ((((m : ℝ) - 2) / (2 * ((m : ℝ) - 1))) / (m : ℝ)) := by
  obtain ⟨hmr3, hkr1, hkrm⟩ := band_setup m k (by omega) hk1 hk
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  rw [mixCountEven_three m k (by omega) hk1 hk, one_mul, one_mul]
  have hid : (2 * (k : ℝ) - 1) / (2 * ((m : ℝ) - 1)) - (k : ℝ) / (m : ℝ)
      = (2 * (k : ℝ) - (m : ℝ)) / (2 * (m : ℝ) * ((m : ℝ) - 1)) := by
    field_simp
    ring
  rw [hid]
  have hrhs : (((m : ℝ) - 2) / (2 * ((m : ℝ) - 1))) / (m : ℝ)
      = ((m : ℝ) - 2) / (2 * (m : ℝ) * ((m : ℝ) - 1)) := by
    field_simp
  rw [hrhs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * (m:ℝ) * ((m:ℝ) - 1)),
      div_le_div_iff₀ (by positivity) (by positivity)]
  have habs : |2 * (k : ℝ) - (m : ℝ)| ≤ (m : ℝ) - 2 := by
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_mul_of_nonneg_right habs (by positivity)

theorem band_even_one (m k : ℕ) (hm : 4 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |mixCountEven m 1 k - (((m : ℝ) - 2) / 2) * ((k : ℝ) / (m : ℝ))|
      ≤ (((m : ℝ) - 2) / 2) * ((((m : ℝ) - 2) / (2 * ((m : ℝ) - 1))) / (m : ℝ)) := by
  obtain ⟨hmr3, hkr1, hkrm⟩ := band_setup m k (by omega) hk1 hk
  have hmr : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  rw [mixCountEven_one m k (by omega) hk1 hk]
  have hid : ((k : ℝ) * ((m : ℝ) - 3) + 1) / (2 * ((m : ℝ) - 1))
      - (((m : ℝ) - 2) / 2) * ((k : ℝ) / (m : ℝ))
      = ((m : ℝ) - 2 * (k : ℝ)) / (2 * (m : ℝ) * ((m : ℝ) - 1)) := by
    field_simp
    ring
  have hrhs : (((m : ℝ) - 2) / 2) * ((((m : ℝ) - 2) / (2 * ((m : ℝ) - 1))) / (m : ℝ))
      = ((m : ℝ) - 2) ^ 2 / (4 * (m : ℝ) * ((m : ℝ) - 1)) := by
    field_simp
    ring
  rw [hid, hrhs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * (m:ℝ) * ((m:ℝ) - 1)),
      div_le_div_iff₀ (by positivity) (by positivity)]
  have habs : |(m : ℝ) - 2 * (k : ℝ)| ≤ (m : ℝ) - 2 := by
    rw [abs_le]
    constructor <;> linarith
  have hstep : |(m : ℝ) - 2 * (k : ℝ)| * (4 * (m : ℝ) * ((m : ℝ) - 1))
      ≤ ((m : ℝ) - 2) * (4 * (m : ℝ) * ((m : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_right habs (by positivity)
  have hgap : ((m : ℝ) - 2) ^ 2 * (2 * (m : ℝ) * ((m : ℝ) - 1))
      - ((m : ℝ) - 2) * (4 * (m : ℝ) * ((m : ℝ) - 1))
      = 2 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 4) := by ring
  have hnn : (0 : ℝ) ≤ 2 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 4) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hm1.le) (by linarith)) (by linarith)
  linarith [hstep, hgap, hnn]

/-! ### (O1), assembled

Both halves in one statement, per parity: the mixture attains the free value at every
budget AND its expected count of every type sits inside the band at `eta_*(m)`.

Per-ITEM marginals are what the band is literally about; expected counts are what is
computed here.  The two are related by `marginal_eq_occupancy_div_card` of
`LeanPaperCBreakpointV1`, whose hypotheses are supplied by the uniform relabelling
constructed there (`relabelledLaw_invariant` gives the within-group constancy,
`group_total_eq_expected_count` gives the group total).  So the chain from a distribution
over genuine rankings to the band is closed; what is stated below is the arithmetic end of
it. -/

/-- **(O1) for odd `m`.**  At `eta_* = 1` the construction is feasible at every budget, and
the `+3` band is tight at `k = m-1` -- which is why the breakpoint sits at `1` and no
lower. -/
theorem O1_odd (m k : ℕ) (hm : 3 ≤ m) (hmo : m % 2 = 1) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |mixCount m 3 k - 1 * ((k : ℝ) / (m : ℝ))| ≤ 1 * (1 / (m : ℝ)) ∧
    |mixCount m (-3) k - 1 * ((k : ℝ) / (m : ℝ))| ≤ 1 * (1 / (m : ℝ)) ∧
    |mixCount m 1 k - (((m : ℝ) - 3) / 2) * ((k : ℝ) / (m : ℝ))|
      ≤ (((m : ℝ) - 3) / 2) * (1 / (m : ℝ)) ∧
    |mixCount m (-1) k - (((m : ℝ) - 1) / 2) * ((k : ℝ) / (m : ℝ))|
      ≤ (((m : ℝ) - 1) / 2) * (1 / (m : ℝ)) :=
  ⟨band_three m k hm hk1 hk, band_neg_three m k hm hk1 hk, band_one m k hm hk1 hk,
    band_neg_one m k hm hmo hk1 hk⟩

/-- **(O1) for even `m`.**  Mixing with the sign flip symmetrises the two heavy items and
the two light types, and the band then holds at `eta_*(m) = (m-2)/(2(m-1))`, which is below
`1/2` at every size. -/
theorem O1_even (m k : ℕ) (hm : 4 ≤ m) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    |mixCountEven m 3 k - 1 * ((k : ℝ) / (m : ℝ))|
      ≤ 1 * ((((m : ℝ) - 2) / (2 * ((m : ℝ) - 1))) / (m : ℝ)) ∧
    |mixCountEven m 1 k - (((m : ℝ) - 2) / 2) * ((k : ℝ) / (m : ℝ))|
      ≤ (((m : ℝ) - 2) / 2) * ((((m : ℝ) - 2) / (2 * ((m : ℝ) - 1))) / (m : ℝ)) :=
  ⟨band_even_three m k hm hk1 hk, band_even_one m k hm hk1 hk⟩

/-- The even mixture treats `+3` and `-3` alike, and `+1` and `-1` alike, so the two bands
above cover all four types. -/
theorem mixCountEven_symm (m : ℕ) (w : ℝ) (k : ℕ) :
    mixCountEven m w k = mixCountEven m (-w) k := by
  unfold mixCountEven
  rw [neg_neg]
  ring

/-! ## The two lemmas, in the shape the arithmetic consumes

`LeanPaperCBreakpointV1.breakpoint_lower_even` and `breakpoint_lower_odd` take the two
combinatorial facts as hypotheses `hid` and `hineq`.  These are those hypotheses, produced
from the model rather than assumed: a randomised ranking is a law on a finite index set
together with the ranking each index names, and both facts hold pointwise, so they hold
under any law. -/

/-- **(L2) in the shape `breakpoint_lower_odd` consumes.** -/
theorem hineq_for_breakpoint {R : Type*} [Fintype R] (hm : 2 < m) (hmo : m % 2 = 1)
    (rank : R → Ranking m) (hfam : ∀ x, IsOddFamily (rank x))
    (heavyAt : R → ℕ) (hlt : ∀ x, heavyAt x < m)
    (hheavy : ∀ x, rank x ⟨heavyAt x, hlt x⟩ = 3) :
    ∀ x : R, 2 + 2 * (if 0 < rank x ⟨m - 1, by omega⟩ then (1 : ℝ) else 0)
      ≤ totalExcess (rank x) :=
  fun x => odd_total_excess hm hmo (rank x) (hfam x) (heavyAt x) (hlt x) (hheavy x)

/-- The indicator `breakpoint_lower_odd` also needs to be nonnegative. -/
theorem lastPos_nonneg {R : Type*} (hm : 2 < m) (rank : R → Ranking m) (x : R) :
    0 ≤ (if 0 < rank x ⟨m - 1, by omega⟩ then (1 : ℝ) else 0) := by
  split_ifs <;> norm_num

/-- **Both lemmas are about inhabited classes**, so neither bridge is empty: the even family
has `altFamily`, and the odd family is exhibited here. -/
noncomputable def oddWeight (m i : ℕ) : ℝ :=
  if i = m - 2 then 3 else if i = m - 1 then -3 else if i = 0 then -1 else (-1 : ℝ) ^ i

noncomputable def oddFamily (m : ℕ) : Ranking m := fun i => oddWeight m (i : ℕ)

theorem oddFamily_weights (n : ℕ) (i : Fin (n + 3)) :
    oddFamily (n + 3) i = -3 ∨ oddFamily (n + 3) i = -1 ∨ oddFamily (n + 3) i = 1
      ∨ oddFamily (n + 3) i = 3 := by
  unfold oddFamily oddWeight
  split_ifs with h1 h2 h3
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rcases Nat.even_or_odd (i : ℕ) with he | ho
    · exact Or.inr (Or.inr (Or.inl he.neg_one_pow))
    · exact Or.inr (Or.inl ho.neg_one_pow)

/-! ### (O1) for even `m`: the flipped mixture's VALUE, not only its band

`O1_even` proves the flipped mixture is band-feasible at `eta_*(m) = (m-2)/(2(m-1))`.
Feasibility alone does not give (O1): the mixture must also ATTAIN the free value.  It
does, and for a reason that costs nothing: `excess` is built from `|prefixSum|`, so
flipping every sign leaves it unchanged, and the flipped mixture has exactly the value
`insMixture_free_value` computes for the plain one.  With that, (O1) is closed at every
`m` and both parities. -/

theorem prefixSum_neg (m : ℕ) (π : Ranking m) (k : ℕ) :
    prefixSum (fun i => -(π i)) k = -(prefixSum π k) := by
  unfold prefixSum
  rw [← Finset.sum_neg_distrib]

/-- **The sign flip leaves the excess unchanged.** -/
theorem excess_neg (m : ℕ) (π : Ranking m) (k : ℕ) :
    excess (fun i => -(π i)) k = excess π k := by
  unfold excess
  rw [prefixSum_neg, abs_neg]

/-- **(O1) attainment for the EVEN mixture.** -/
theorem insMixtureEven_free_value (m : ℕ) (hm : 1 < m) (D : ℝ) (hD : D ≠ 0)
    (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ m - 1) :
    ∑ a ∈ Finset.range (m - 1),
        ((1 / (2 * ((m : ℝ) - 1))) * (excess (insRanking m a) k / D)
          + (1 / (2 * ((m : ℝ) - 1)))
            * (excess (fun i => -(insRanking m a i)) k / D))
      = 2 / (D * ((m : ℝ) - 1)) := by
  classical
  have hterm : ∀ a ∈ Finset.range (m - 1),
      ((1 / (2 * ((m : ℝ) - 1))) * (excess (insRanking m a) k / D)
        + (1 / (2 * ((m : ℝ) - 1)))
          * (excess (fun i => -(insRanking m a i)) k / D))
      = (1 / ((m : ℝ) - 1)) * (excess (insRanking m a) k / D) := by
    intro a _
    rw [excess_neg m (insRanking m a) k]
    have hmr : ((m : ℝ) - 1) ≠ 0 := by
      have h1 : (1 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      linarith
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  exact insMixture_free_value m hm D hD k hk1 hk

/-! ## Audit -/

#print axioms heavy_eq_zero_or_one
#print axioms abs_weight
#print axioms one_le_abs_weight
#print axioms excess_eq_two_heavy
#print axioms prefixSum_one
#print axioms prefixSum_pred
#print axioms two_budget_identity
#print axioms two_budget_identity_div
#print axioms one_le_prefixSum_first
#print axioms one_le_prefixSum_last
#print axioms altWeight_lt
#print axioms altWeight_heavy_pos
#print axioms altWeight_heavy_neg
#print axioms altFamily_isFamily
#print axioms altFamily_first
#print axioms altFamily_last
#print axioms baseline_first
#print axioms baseline_last_lower
#print axioms altFamily_last_is_three
#print axioms altWeight2_decomp
#print axioms altFamily2_isFamily
#print axioms altFamily2_last
#print axioms baseline_last
#print axioms evenFamily_nonempty
#print axioms hid_for_breakpoint
#print axioms weight_odd
#print axioms prefixSum_zero
#print axioms prefixSum_succ
#print axioms prefixSum_parity
#print axioms one_le_abs_prefixSum_of_odd
#print axioms excess_nonneg
#print axioms jump_forces_excess
#print axioms totalExcess_ge_of_subset
#print axioms prefixSum_last_odd
#print axioms excess_last
#print axioms odd_total_excess
#print axioms insRanking_prefix
#print axioms insRanking_excess
#print axioms countIns_three
#print axioms countIns_neg_three
#print axioms countIns_neg_one
#print axioms countIns_one
#print axioms mixCount_three
#print axioms mixCount_neg_three
#print axioms mixCount_neg_one
#print axioms mixCount_one
#print axioms band_three
#print axioms band_neg_three
#print axioms odds_band_core
#print axioms evens_band_core
#print axioms band_one
#print axioms band_neg_one
#print axioms countInsFlip_eq
#print axioms mixCountEven_three
#print axioms mixCountEven_one
#print axioms band_even_three
#print axioms band_even_one
#print axioms O1_odd
#print axioms O1_even
#print axioms excess_neg
#print axioms insMixtureEven_free_value
#print axioms mixCountEven_symm
#print axioms insMixture_free_value
#print axioms insRanking_weights
#print axioms hineq_for_breakpoint
#print axioms lastPos_nonneg
#print axioms oddFamily_weights

end CIGAMF.P13.PaperCRanking
