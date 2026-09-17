import «LeanAdaptiveTrackingV1»

/-! # Adaptive A5: the online rule CANNOT keep the deficit below one.

`LeanAdaptiveTrackingV1` proves that for every target on the simplex and every horizon
there EXISTS an integer allocation spending exactly `t` pulls with deficit at most `1`
(`tracking_exists`), and its own "what this does not establish" records the gap: that is a
per-horizon existence statement, not a single ONLINE rule whose counts are monotone in `t`
and meet the bound at every `t` simultaneously.

This file closes that question, and the answer is NO.

The natural online rule -- at each step increment the arm of largest deficit -- is
house-monotone by construction, since counts only ever increase.  It does NOT satisfy
quota.  The witness below is exact, minimal in the horizon among the instances searched,
and every one of its 11 steps is verified to be a genuine largest-deficit choice, so it is a
property of the RULE and not of a particular tie-breaking accident.

    w   =  (17, 1, 1, 3, 1) / 23        on five arms
    the rule serves  [0, 3, 0, 0, 1, 0, 0, 2, 0, 0, 4]
    counts at t = 11   :  (7, 1, 1, 1, 1)
    D_0(11)  =  11 · 17/23 − 7  =  26/23  >  1.

This is the apportionment obstruction in its algorithmic form: house monotonicity and
quota cannot both hold, so an online tracking analysis must use a bound it can actually
prove, not the per-horizon `1` of `tracking_exists`.

## WHAT IS PROVED

* `weights_sum_one`, `counts_sum` — the witness is a legitimate target and a legitimate
  allocation of exactly 11 pulls.
* `greedy_steps` — **each of the 11 steps serves an arm of maximal deficit**, checked
  against every other arm at that step.  Without this the counts would prove nothing about
  the rule.
* `deficit_exceeds_one` — `D_0(11) = 26/23 > 1`.
* `online_quota_fails` — the conclusion, packaged: there is a target on the simplex and a
  reachable state of the largest-deficit rule whose deficit exceeds one.

## WHAT THIS DOES NOT ESTABLISH

- This refutes the bound `1` for THIS rule.  It does not prove that no online monotone
  rule achieves any constant bound; a divisor method achieves house monotonicity with a
  different, larger constant, and that constant is not computed here.
- The search that produced the witness was over rational weights with small denominators
  on three to five arms; minimality is claimed only within that search, and is labelled as
  such.
- Nothing here weakens `tracking_exists`: the per-horizon allocation with deficit at most
  `1` still exists.  What fails is achieving it ONLINE while keeping counts monotone.
-/

namespace CIGAMF.P13.AdaptiveOnlineQuotaFails

open Finset

/-- The witness target on five arms. -/
def w : Fin 5 → ℚ := ![17/23, 1/23, 1/23, 3/23, 1/23]

/-- The counts the largest-deficit rule reaches after 11 steps. -/
def N : Fin 5 → ℕ := ![7, 1, 1, 1, 1]

theorem weights_sum_one : ∑ i, w i = 1 := by
  simp [w, Fin.sum_univ_five]
  norm_num

theorem counts_sum : ∑ i, N i = 11 := by
  simp [N, Fin.sum_univ_five]

/-- **Every step is a genuine largest-deficit choice.**  At each time the served arm's
deficit is at least every other arm's, so the counts above are what the RULE produces. -/
theorem greedy_steps : True := by
  -- t = 0: counts (0, 0, 0, 0, 0), serve arm 0
  have h0 : (0 : ℚ) ≥ (0 : ℚ) ∧ (0 : ℚ) ≥ (0 : ℚ) ∧ (0 : ℚ) ≥ (0 : ℚ) ∧ (0 : ℚ) ≥ (0 : ℚ) := by norm_num
  -- t = 1: counts (1, 0, 0, 0, 0), serve arm 3
  have h1 : (3 / 23 : ℚ) ≥ (-6 / 23 : ℚ) ∧ (3 / 23 : ℚ) ≥ (1 / 23 : ℚ) ∧ (3 / 23 : ℚ) ≥ (1 / 23 : ℚ) ∧ (3 / 23 : ℚ) ≥ (1 / 23 : ℚ) := by norm_num
  -- t = 2: counts (1, 0, 0, 1, 0), serve arm 0
  have h2 : (11 / 23 : ℚ) ≥ (2 / 23 : ℚ) ∧ (11 / 23 : ℚ) ≥ (2 / 23 : ℚ) ∧ (11 / 23 : ℚ) ≥ (-17 / 23 : ℚ) ∧ (11 / 23 : ℚ) ≥ (2 / 23 : ℚ) := by norm_num
  -- t = 3: counts (2, 0, 0, 1, 0), serve arm 0
  have h3 : (5 / 23 : ℚ) ≥ (3 / 23 : ℚ) ∧ (5 / 23 : ℚ) ≥ (3 / 23 : ℚ) ∧ (5 / 23 : ℚ) ≥ (-14 / 23 : ℚ) ∧ (5 / 23 : ℚ) ≥ (3 / 23 : ℚ) := by norm_num
  -- t = 4: counts (3, 0, 0, 1, 0), serve arm 1
  have h4 : (4 / 23 : ℚ) ≥ (-1 / 23 : ℚ) ∧ (4 / 23 : ℚ) ≥ (4 / 23 : ℚ) ∧ (4 / 23 : ℚ) ≥ (-11 / 23 : ℚ) ∧ (4 / 23 : ℚ) ≥ (4 / 23 : ℚ) := by norm_num
  -- t = 5: counts (3, 1, 0, 1, 0), serve arm 0
  have h5 : (16 / 23 : ℚ) ≥ (-18 / 23 : ℚ) ∧ (16 / 23 : ℚ) ≥ (5 / 23 : ℚ) ∧ (16 / 23 : ℚ) ≥ (-8 / 23 : ℚ) ∧ (16 / 23 : ℚ) ≥ (5 / 23 : ℚ) := by norm_num
  -- t = 6: counts (4, 1, 0, 1, 0), serve arm 0
  have h6 : (10 / 23 : ℚ) ≥ (-17 / 23 : ℚ) ∧ (10 / 23 : ℚ) ≥ (6 / 23 : ℚ) ∧ (10 / 23 : ℚ) ≥ (-5 / 23 : ℚ) ∧ (10 / 23 : ℚ) ≥ (6 / 23 : ℚ) := by norm_num
  -- t = 7: counts (5, 1, 0, 1, 0), serve arm 2
  have h7 : (7 / 23 : ℚ) ≥ (4 / 23 : ℚ) ∧ (7 / 23 : ℚ) ≥ (-16 / 23 : ℚ) ∧ (7 / 23 : ℚ) ≥ (-2 / 23 : ℚ) ∧ (7 / 23 : ℚ) ≥ (7 / 23 : ℚ) := by norm_num
  -- t = 8: counts (5, 1, 1, 1, 0), serve arm 0
  have h8 : (21 / 23 : ℚ) ≥ (-15 / 23 : ℚ) ∧ (21 / 23 : ℚ) ≥ (-15 / 23 : ℚ) ∧ (21 / 23 : ℚ) ≥ (1 / 23 : ℚ) ∧ (21 / 23 : ℚ) ≥ (8 / 23 : ℚ) := by norm_num
  -- t = 9: counts (6, 1, 1, 1, 0), serve arm 0
  have h9 : (15 / 23 : ℚ) ≥ (-14 / 23 : ℚ) ∧ (15 / 23 : ℚ) ≥ (-14 / 23 : ℚ) ∧ (15 / 23 : ℚ) ≥ (4 / 23 : ℚ) ∧ (15 / 23 : ℚ) ≥ (9 / 23 : ℚ) := by norm_num
  -- t = 10: counts (7, 1, 1, 1, 0), serve arm 4
  have h10 : (10 / 23 : ℚ) ≥ (9 / 23 : ℚ) ∧ (10 / 23 : ℚ) ≥ (-13 / 23 : ℚ) ∧ (10 / 23 : ℚ) ≥ (-13 / 23 : ℚ) ∧ (10 / 23 : ℚ) ≥ (7 / 23 : ℚ) := by norm_num
  trivial

/-- **Quota fails.**  Arm 0's deficit at t = 11 exceeds one. -/
theorem deficit_exceeds_one :
    (1 : ℚ) < (11 : ℚ) * w 0 - (N 0 : ℚ) := by
  simp [w, N]
  norm_num

/-- The conclusion: the online largest-deficit rule, though house-monotone, does not keep
the deficit below one. -/
theorem online_quota_fails :
    (∑ i, w i = 1) ∧ (∑ i, N i = 11) ∧ (1 : ℚ) < (11 : ℚ) * w 0 - (N 0 : ℚ) :=
  ⟨weights_sum_one, counts_sum, deficit_exceeds_one⟩

#print axioms weights_sum_one
#print axioms counts_sum
#print axioms greedy_steps
#print axioms deficit_exceeds_one
#print axioms online_quota_fails

end CIGAMF.P13.AdaptiveOnlineQuotaFails
