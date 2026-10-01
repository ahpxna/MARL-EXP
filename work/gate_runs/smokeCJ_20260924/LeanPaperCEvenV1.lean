import «LeanPaperCRankingV1»

/-!
# Paper C: the extra ranking the even uniform-marginal construction needs

The even-`m` upper bound on `V_m(0)` mixes the `m-1` insertion rankings with one more,

    ( -3, +1, -1, +1, -1, ..., +1, -1, +3 ),

whose defining property is that its excess is **exactly `2` at every budget** --- not a
single spike, but a flat `2` across `k = 1, ..., m-1`.  That is what makes the mixture's
per-budget expectation `2/m + 2/m = 4/m` rather than something budget-dependent.

Everything follows from one induction.  The prefix sum alternates between `-3` and `-2`:
the first weight is `-3`, and the alternating block adds `+1` at odd positions and `-1` at
even ones, so an odd budget sees `-3` and an even budget `-2`.  Since the excess subtracts
`k mod 2`, both cases give `2`.

The total weight is a **corollary of the same pattern**, not a separate count: at `k = m`
with `m` even, `m-1` is odd, so the prefix is `-3` and the last weight `+3` closes it to
zero.  That is what `IsEvenFamily` needs, so the construction is a member of the family.
-/

namespace CIGAMF.P13.PaperCEven

open Finset
open CIGAMF.P13.PaperCRanking

variable {m : ℕ}

/-- `-3`, then `+1` at odd positions and `-1` at even ones, then `+3`. -/
noncomputable def flatEven (m : ℕ) : Ranking m := fun i =>
  if (i : ℕ) = 0 then -3
  else if (i : ℕ) = m - 1 then 3
  else if (i : ℕ) % 2 = 1 then 1 else -1

theorem flatEven_zero (hm : 0 < m) : flatEven m ⟨0, hm⟩ = -3 := by
  simp [flatEven]

theorem flatEven_last (hm : 0 < m) (h1 : 1 < m) :
    flatEven m ⟨m - 1, by omega⟩ = 3 := by
  have h0 : (m - 1 : ℕ) ≠ 0 := by omega
  simp [flatEven, h0]

theorem flatEven_mid (k : ℕ) (hk : k < m) (h0 : k ≠ 0) (hlast : k ≠ m - 1) :
    flatEven m ⟨k, hk⟩ = if k % 2 = 1 then 1 else -1 := by
  simp [flatEven, h0, hlast]

/-- **The prefix pattern.**  For every budget up to `m-1`, the prefix sum is `-3` at odd
budgets and `-2` at even ones. -/
theorem flatEven_prefix (hm : 1 < m) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 →
      prefixSum (flatEven m) k = if k % 2 = 1 then -3 else -2 := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hle
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega : n + 1 ≠ 0)) with h1 | h1
    · -- n + 1 = 1
      have hn : n = 0 := by omega
      subst hn
      rw [prefixSum_succ (flatEven m) 0 (by omega), prefixSum_zero,
          flatEven_zero (by omega)]
      norm_num
    · -- n >= 1
      have hn1 : 1 ≤ n := by omega
      have hnle : n ≤ m - 1 := by omega
      have hnm : n < m := by omega
      have hih := ih hn1 hnle
      have hne0 : n ≠ 0 := by omega
      have hnlast : n ≠ m - 1 := by omega
      rw [prefixSum_succ (flatEven m) n hnm, hih, flatEven_mid n hnm hne0 hnlast]
      rcases Nat.even_or_odd n with he | ho
      · have h2 : n % 2 = 0 := Nat.even_iff.mp he
        have h3 : (n + 1) % 2 = 1 := by omega
        rw [if_neg (by omega), if_neg (by omega), if_pos h3]
        norm_num
      · have h2 : n % 2 = 1 := Nat.odd_iff.mp ho
        have h3 : (n + 1) % 2 = 0 := by omega
        rw [if_pos h2, if_pos h2, if_neg (by omega)]
        norm_num

/-- **The excess is `2` at every budget.**  This is the property the mixture needs. -/
theorem flatEven_excess (hm : 1 < m) :
    ∀ k : ℕ, 1 ≤ k → k ≤ m - 1 → excess (flatEven m) k = 2 := by
  intro k hk1 hkle
  unfold excess
  rw [flatEven_prefix hm k hk1 hkle]
  rcases Nat.even_or_odd k with he | ho
  · have h2 : k % 2 = 0 := Nat.even_iff.mp he
    rw [if_neg (by omega), h2]
    norm_num
  · have h2 : k % 2 = 1 := Nat.odd_iff.mp ho
    rw [if_pos h2, h2]
    norm_num

/-- **The total is zero**, a corollary of the same pattern rather than a separate count:
for even `m` the budget `m-1` is odd, so the prefix is `-3` and the final `+3` closes it. -/
theorem flatEven_total (hm : 1 < m) (hpar : m % 2 = 0) :
    prefixSum (flatEven m) m = 0 := by
  have hlast : m - 1 < m := by omega
  have hstep : prefixSum (flatEven m) ((m - 1) + 1)
      = prefixSum (flatEven m) (m - 1) + flatEven m ⟨m - 1, hlast⟩ :=
    prefixSum_succ (flatEven m) (m - 1) hlast
  have hm1 : (m - 1) + 1 = m := by omega
  rw [hm1] at hstep
  have hodd : (m - 1) % 2 = 1 := by omega
  rw [hstep, flatEven_prefix hm (m - 1) (by omega) le_rfl, if_pos hodd,
      flatEven_last (by omega) hm]
  norm_num

/-- **The weights are the family's.** -/
theorem flatEven_weights (hm : 1 < m) (i : Fin m) :
    flatEven m i = -3 ∨ flatEven m i = -1 ∨ flatEven m i = 1 ∨ flatEven m i = 3 := by
  unfold flatEven
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inl rfl)

/-! ## Audit -/

#print axioms flatEven_prefix
#print axioms flatEven_excess
#print axioms flatEven_total
#print axioms flatEven_weights

end CIGAMF.P13.PaperCEven
