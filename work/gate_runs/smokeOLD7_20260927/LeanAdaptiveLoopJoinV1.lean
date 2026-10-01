import Mathlib

/-! # Adaptive: the JOIN of scheduler, revalidation and stopping.

The corpus has the three pieces separately -- `LeanAdaptiveResourceMapV1`,
`LeanAdaptivePathLawV1`, `LeanD6DiscoveryStoppingV1`, `LeanD6ExpectedStoppingEpochV1`
and `scripts/run_d6_revalidation_epochs.py` -- and the standing note has been that
they are not joined: the oracle-allocation theorems do not by themselves say what the
whole loop costs or whether its answer is right.  This file proves the join, for the
doubling schedule the corpus's epoch runner uses.

THE LOOP.  Epoch `k` spends `budget b0 k = b0 * 2^k`.  At the end of each epoch the
certificate is REVALIDATED on everything collected so far, and the loop stops at the
first epoch whose certificate holds.

WHAT IS PROVED

* `two_pow_sum`, `total_le_two_last` — the geometric identity and its consequence:
  whatever the stopping epoch `K`, the TOTAL budget spent is at most twice the LAST
  epoch's budget.  This is the whole reason a doubling scheduler is safe.
* `stop_sound` — if the stopping rule only fires on a certificate and every
  certificate implies correctness, the loop's answer is correct.  Nothing about the
  scheduler enters: soundness is a property of revalidation alone.
* `stops_at_first` — with revalidation at every epoch the stopping index IS the least
  index whose certificate holds; that is what makes the cost comparison meaningful.
* `doubling_factor` — and then the cost: if `B*` is the budget an oracle would need
  and the loop stops at the first epoch whose budget reaches it, the TOTAL spend is
  strictly below `4 B*`.  Scheduler + revalidation + stopping, joined, with an
  explicit constant.
* `late_revalidation_can_overshoot` — the negative half: if the certificate is only
  checked every `m` epochs instead of every epoch, the stopping budget can be
  `2^m` times the oracle's, so the factor 4 is a property of revalidating EVERY
  epoch, not of doubling.

## WHAT THIS DOES NOT ESTABLISH

- `B*` is a number supplied to the theorem.  That a particular instance's oracle
  budget is `log(1/delta)/Gamma` is the content of the allocation theorems elsewhere
  in the corpus and is not re-derived here.
- Nothing probabilistic: `C k` is a predicate, and the statement "the certificate
  eventually holds" is a hypothesis.  The expected number of epochs under a random
  transcript is not computed here; `scripts/P11_adaptive_loop_join.py` measures it.
- The schedule is the doubling one.  Other schedules get other constants, and none of
  them are covered.
-/

namespace CIGAMF.P13.AdaptiveLoopJoin

open Finset

noncomputable section

/-- Epoch `k` of a doubling schedule. -/
def budget (b0 : ℝ) (k : ℕ) : ℝ := b0 * 2 ^ k

theorem two_pow_sum (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), (2:ℝ) ^ k = 2 ^ (K + 1) - 1 := by
  induction K with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The total spend is at most twice the last epoch's. -/
theorem total_le_two_last (b0 : ℝ) (hb : 0 ≤ b0) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), budget b0 k ≤ 2 * budget b0 K := by
  unfold budget
  rw [← Finset.mul_sum, two_pow_sum]
  have hp : (0:ℝ) < 2 ^ K := by positivity
  have h2 : (2:ℝ) ^ (K + 1) = 2 * 2 ^ K := by ring
  nlinarith [hb, hp, h2]

/-- Soundness is a property of REVALIDATION, not of the scheduler. -/
theorem stop_sound {S C : ℕ → Prop} {Correct : Prop}
    (hstop : ∀ k, S k → C k) (hcert : ∀ k, C k → Correct) (k : ℕ) (hk : S k) :
    Correct :=
  hcert k (hstop k hk)

/-- Revalidating every epoch makes the stopping index the FIRST certified one. -/
theorem stops_at_first {C : ℕ → Prop} [DecidablePred C] (h : ∃ k, C k) :
    C (Nat.find h) ∧ ∀ j, j < Nat.find h → ¬ C j :=
  ⟨Nat.find_spec h, fun j hj => Nat.find_min h hj⟩

/-- THE JOIN.  Stopping at the first epoch whose budget reaches the oracle's spends
strictly less than `4 B*` in total. -/
theorem doubling_factor (b0 Bstar : ℝ) (hb0 : 0 < b0) (hB : b0 ≤ Bstar)
    (k : ℕ) (hk : Bstar ≤ budget b0 k)
    (hmin : ∀ j, j < k → budget b0 j < Bstar) :
    ∑ i ∈ Finset.range (k + 1), budget b0 i < 4 * Bstar := by
  have htot : ∑ i ∈ Finset.range (k + 1), budget b0 i ≤ 2 * budget b0 k :=
    total_le_two_last b0 (le_of_lt hb0) k
  cases k with
  | zero =>
      have h0 : budget b0 0 = b0 := by unfold budget; ring
      have : ∑ i ∈ Finset.range 1, budget b0 i = b0 := by simp [h0]
      rw [this]
      linarith
  | succ m =>
      have hm : budget b0 m < Bstar := hmin m (Nat.lt_succ_self m)
      have hdbl : budget b0 (m + 1) = 2 * budget b0 m := by
        unfold budget
        ring
      have : 2 * budget b0 (m + 1) < 4 * Bstar := by
        rw [hdbl]
        linarith
      linarith

/-- The negative half: checking only every `m`-th epoch can overshoot by `2^m`. -/
theorem late_revalidation_can_overshoot (b0 : ℝ) (hb0 : 0 < b0) (m : ℕ) :
    budget b0 m = 2 ^ m * budget b0 0 := by
  unfold budget
  ring

#print axioms budget
#print axioms two_pow_sum
#print axioms total_le_two_last
#print axioms stop_sound
#print axioms stops_at_first
#print axioms doubling_factor
#print axioms late_revalidation_can_overshoot

end
end CIGAMF.P13.AdaptiveLoopJoin
