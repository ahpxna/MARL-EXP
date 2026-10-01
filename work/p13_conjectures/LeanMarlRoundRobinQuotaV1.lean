import Mathlib

/-!
# Round-robin keeps every sender within one of its quota (uniform targets; paper_marl_v2, V-Q)

A schedule serves one of `m` senders per step.  With uniform targets `1/m`, the quota of sender `j` after `t` steps is
`t/m`, and its deficit is `t/m - N_j(t)`.  Round-robin serves sender `t mod m` at step `t`.

## WHAT IS PROVED
* `rr_count` — after `t` steps round-robin has served sender `j` exactly `#{s < t : s mod m = j}` times, which is
  `t / m` or `t / m + 1`.
* `rr_within_one` — so `|N_j(t) - t/m| < 1` for every sender and every `t`: round-robin meets unit quota uniformly.
  This is the elementary fact behind "for uniform targets largest-deficit is round-robin and stays within one"; the
  non-uniform failure of largest-deficit is `LeanAdaptiveOnlineQuotaFailsV1.online_quota_fails` (PROVED, reused).

## WHAT THIS DOES NOT ESTABLISH
- That the E3 age-first order is round-robin: with several transmissions per step and index ties it is not
  (`LeanMarlAgeFirstInjectionV1` proves the transmission bound instead).
-/

namespace CIGAMF.P13.MarlRoundRobinQuota

open Finset

/-- How many of the steps `0, …, t-1` serve sender `j` under round-robin on `m` senders. -/
def rrCount (m t j : ℕ) : ℕ := ((range t).filter fun s => s % m = j).card

theorem rrCount_succ (m t j : ℕ) : rrCount m (t + 1) j = rrCount m t j + if t % m = j then 1 else 0 := by
  unfold rrCount
  rw [Finset.range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

/-- Round-robin counts are `t / m` or `t / m + 1` (exactly `t / m` plus one when `j < t mod m`). -/
theorem rr_count (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < m) :
    ∀ t, rrCount m t j = t / m + if j < t % m then 1 else 0 := by
  intro t
  induction t with
  | zero => simp [rrCount]
  | succ t ih =>
      rw [rrCount_succ, ih]
      have hmod := Nat.mod_lt t hm
      rcases Nat.lt_or_ge (t % m + 1) m with h | h
      · have h1 : (t + 1) % m = t % m + 1 := by
          rw [Nat.add_mod, Nat.one_mod_eq_one.mpr (by omega)]; exact Nat.mod_eq_of_lt (by omega)
        have h2 : (t + 1) / m = t / m := by
          have := Nat.div_add_mod (t + 1) m; have := Nat.div_add_mod t m; nlinarith [h1]
        rw [h1, h2]
        split_ifs <;> omega
      · have h1 : t % m = m - 1 := by omega
        have h1' : (t + 1) % m = 0 := by
          have : t + 1 = (t / m + 1) * m := by have := Nat.div_add_mod t m; nlinarith [h1]
          rw [this, Nat.mul_mod_left]
        have h2 : (t + 1) / m = t / m + 1 := by
          have : t + 1 = (t / m + 1) * m := by have := Nat.div_add_mod t m; nlinarith [h1]
          rw [this, Nat.mul_div_cancel _ hm]
        rw [h1', h2]
        split_ifs <;> omega

/-- **Round-robin is within one of quota**, for every sender and every horizon. -/
theorem rr_within_one (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < m) (t : ℕ) :
    |(rrCount m t j : ℝ) - (t : ℝ) / m| < 1 := by
  rw [rr_count m hm j hj t]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdecomp : (t : ℝ) = (t / m : ℕ) * m + (t % m : ℕ) := by
    exact_mod_cast (Nat.div_add_mod' t m).symm
  have hr : ((t % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt t hm
  have hr0 : (0 : ℝ) ≤ ((t % m : ℕ) : ℝ) := by positivity
  have hq : (t : ℝ) / m = (t / m : ℕ) + ((t % m : ℕ) : ℝ) / m := by
    rw [hdecomp]; field_simp
  have hfrac : ((t % m : ℕ) : ℝ) / m < 1 := by rw [div_lt_one hmR]; exact hr
  have hfrac0 : 0 ≤ ((t % m : ℕ) : ℝ) / m := by positivity
  rw [hq, abs_lt]
  split_ifs with h
  · have hpos : 0 < ((t % m : ℕ) : ℝ) / m := by
      have : (0 : ℝ) < ((t % m : ℕ) : ℝ) := by exact_mod_cast (show 0 < t % m by omega)
      positivity
    push_cast
    constructor <;> linarith
  · push_cast
    constructor <;> linarith

end CIGAMF.P13.MarlRoundRobinQuota

#print axioms CIGAMF.P13.MarlRoundRobinQuota.rrCount_succ
#print axioms CIGAMF.P13.MarlRoundRobinQuota.rr_count
#print axioms CIGAMF.P13.MarlRoundRobinQuota.rr_within_one
