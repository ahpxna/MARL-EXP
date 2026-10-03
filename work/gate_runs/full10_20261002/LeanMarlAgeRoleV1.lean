import Mathlib

/-!
# Two roles of the age label: a conservative relabel is safe for a reliability cue, not for a propagation horizon

Ledger L-261 (02/10/2026): in the remote-inference testbed, relabelling fresher samples with older ages (the training-free
remap that keeps the age labels inside the training support) cost 0.50 of gain, while in the MARL receivers age is
hypothesised to act as a reliability weight.  PROTOCOL_RI_AGE_ROLE_20261002 tests the split; this file proves it in the
scalar linear-Gaussian picture.  A receiver combines its local estimate (error variance `a > 0`, unbiased) with a remote copy
(error variance `b ≥ 0` at the copy's TRUE age, unbiased, independent): ŷ = w · remote + (1 − w) · local, with mean squared
error `mse a b w = (1 − w)² a + w² b`; ignoring the copy (silence) is `w = 0`, error `a`.  The weight a receiver learned for
a label of age δ' is the optimal one for that age, `wopt a b' = a / (a + b')`.

## WHAT IS PROVED
* `mse_le_silent_iff` — `mse a b w ≤ a` iff `0 ≤ w ≤ 2a / (a + b)`: any weight up to twice the optimum is no worse than
  silence.
* `conservative_relabel_safe` — RELIABILITY role: if the label is OLDER than the copy (the label's variance `b' ≥ b`), the
  weight learned for the label is below the copy's optimum, and the receiver is never worse than silence.
* `overtrust_unsafe` — the opposite relabel (a stale copy labelled fresh, `b' < b`) can be worse than silence (a = 1,
  b = 10, b' = 0: error 10 > 1).  So the remap is safe for UPGRADES, not for downgrades.
* `drift_relabel_unsafe` — PROPAGATION role: if the copy must also be propagated by the label's age (the remote term carries
  a bias c when the label is wrong), even the conservative relabel can be worse than silence (a = 1, b = 0, b' = 1/2,
  bias c² = 4: error 17/9 > 1).

## WHAT THIS DOES NOT ESTABLISH
- That the trained receivers are linear combiners (the testbed and CityFlow results are empirical); only which repair a
  receiver of each kind admits.
-/

namespace CIGAMF.P13.MarlAgeRoleV1

/-- Mean squared error of the combination ŷ = w · remote + (1 − w) · local (unbiased, independent errors). -/
def mse (a b w : ℝ) : ℝ := (1 - w) ^ 2 * a + w ^ 2 * b

/-- The weight that is optimal for a copy of error variance `b`. -/
noncomputable def wopt (a b : ℝ) : ℝ := a / (a + b)

theorem mse_le_silent_iff (a b w : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    mse a b w ≤ a ↔ 0 ≤ w ∧ w ≤ 2 * a / (a + b) := by
  have hab : 0 < a + b := by linarith
  have key : mse a b w - a = w * ((a + b) * w - 2 * a) := by unfold mse; ring
  constructor
  · intro h
    have h' : w * ((a + b) * w - 2 * a) ≤ 0 := by linarith
    rcases le_or_gt 0 w with hw | hw
    · refine ⟨hw, ?_⟩
      rcases eq_or_lt_of_le hw with h0 | hpos
      · rw [← h0]; positivity
      · have : (a + b) * w - 2 * a ≤ 0 := by
          by_contra hc; push_neg at hc; nlinarith
        rw [le_div_iff₀ hab]; linarith
    · exfalso
      have : (a + b) * w - 2 * a < 0 := by nlinarith
      nlinarith
  · rintro ⟨hw0, hw1⟩
    rw [le_div_iff₀ hab] at hw1
    have : w * ((a + b) * w - 2 * a) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hw0 (by linarith)
    linarith

theorem conservative_relabel_safe (a b b' : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hbb : b ≤ b') :
    wopt a b' ≤ wopt a b ∧ mse a b (wopt a b') ≤ a := by
  have hab : 0 < a + b := by linarith
  have hab' : 0 < a + b' := by linarith
  have h1 : wopt a b' ≤ wopt a b := by
    unfold wopt; exact div_le_div_of_nonneg_left ha.le hab (by linarith)
  refine ⟨h1, (mse_le_silent_iff a b _ ha hb).2 ⟨by unfold wopt; positivity, ?_⟩⟩
  have h2 : wopt a b ≤ 2 * a / (a + b) := by
    unfold wopt; exact div_le_div_of_nonneg_right (by linarith) hab.le
  exact h1.trans h2

/-- A stale copy (variance 10) labelled fresh (variance 0): the learned weight 1 gives error 10 > 1 = silence. -/
theorem overtrust_unsafe : 1 < mse 1 10 (wopt 1 0) := by
  unfold mse wopt; norm_num

/-- Error when the remote term also carries a squared propagation bias `c` (the label's age is used to propagate). -/
def mseDrift (a b c w : ℝ) : ℝ := (1 - w) ^ 2 * a + w ^ 2 * (b + c)

/-- Conservative relabel (`b' = 1/2 ≥ b = 0`) under drift (squared bias 4): error 17/9 > 1 = silence. -/
theorem drift_relabel_unsafe : (0 : ℝ) ≤ 1 / 2 ∧ 1 < mseDrift 1 0 4 (wopt 1 (1 / 2)) := by
  refine ⟨by norm_num, ?_⟩
  unfold mseDrift wopt; norm_num

end CIGAMF.P13.MarlAgeRoleV1

#print axioms CIGAMF.P13.MarlAgeRoleV1.mse_le_silent_iff
#print axioms CIGAMF.P13.MarlAgeRoleV1.conservative_relabel_safe
#print axioms CIGAMF.P13.MarlAgeRoleV1.overtrust_unsafe
#print axioms CIGAMF.P13.MarlAgeRoleV1.drift_relabel_unsafe
