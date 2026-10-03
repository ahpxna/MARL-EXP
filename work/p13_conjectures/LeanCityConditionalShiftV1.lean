import Mathlib

/-!
# A partner upgrade that keeps the interface's distribution but changes its meaning is invisible to every input monitor

Direction: research/papers/audits/CITY_TWO_POPULATION_NOVELTY_20261002.md (N1); testbed: research/city_sim/PROTOCOL_CITY_C0_
20261002.md.  A car's view of a light is (time in phase); the light's policy decides what that view means for when the phase
ends.  Two kinds of light upgrade: EXT extends phases (the car sees times in phase it never saw: out of its training support),
CUT switches earlier inside the trained range (the car sees exactly the same distribution of views, with a different meaning).
This file isolates the second kind in a finite model and contrasts it with the first.

Model.  View x ∈ Fin 2 (0 = early in the phase, 1 = late); hidden y : Bool (true = the phase ends before the car arrives);
action a : Bool (true = go).  Loss: go when the phase ends = 20 (forced stop at the line), go otherwise = 0, slow = 1.
* ACT (the training light): early ⇒ the phase lasts (y = false), late ⇒ it ends (y = true); each view with weight ½.
* CUT (the upgrade): the phase ends in both views (y = true); each view with weight ½.

## WHAT IS PROVED
* `marg_eq` — ACT and CUT induce the SAME distribution of views (weight ½ on each).
* `monitor_blind` — consequently every monitor that reads the distribution of views (support, histogram, W1 to training, any
  function at all of the view law) returns the same verdict under ACT and CUT.
* `act_opt`, `fAct_risk` — the rule "go early, slow late" is optimal under ACT among all rules of the view (risk ½).
* `cut_harm` — under CUT the same rule has risk 21/2, while the always-slow rule has risk 1 and is optimal there: the upgrade
  costs the ACT-trained car 19/2, invisibly.
* `message_opt_act`, `message_opt_cut` — with the light's message (y itself: SPaT "does my phase end before I arrive"), the
  single rule "go iff the phase lasts" is optimal among ALL rules of (view, message) under BOTH lights: the message makes the car
  indifferent to the upgrade.
* `ext_detectable` — by contrast an EXT-type upgrade (a third view, never seen in training, with positive weight) leaves the
  training support, which a support monitor detects.

## WHAT THIS DOES NOT ESTABLISH
- That the learned cars of the C0 testbed or of SUMO behave like the rule `fAct` (the testbed measures it).
- Anything about how much an upgrade helps the light itself; the light's objective is not in this model.
-/

namespace CIGAMF.P13.CityConditionalShiftV1

noncomputable section

/-- Loss of action `a` (true = go) when the phase ends before arrival (`y = true`) or not. -/
def loss (y a : Bool) : ℝ := if a then (if y then 20 else 0) else 1

/-- The training light ACT: early ⇒ the phase lasts, late ⇒ it ends; each view with weight ½. -/
def actW (x : Fin 2) (y : Bool) : ℝ := if x = 0 then (if y then 0 else 1 / 2) else (if y then 1 / 2 else 0)

/-- The upgrade CUT: the phase ends in both views; each view with weight ½. -/
def cutW (_x : Fin 2) (y : Bool) : ℝ := if y then 1 / 2 else 0

/-- Distribution of views. -/
def marg (P : Fin 2 → Bool → ℝ) (x : Fin 2) : ℝ := P x true + P x false

/-- Risk of a rule of the view alone. -/
def riskV (P : Fin 2 → Bool → ℝ) (r : Fin 2 → Bool) : ℝ :=
  ∑ x : Fin 2, (P x true * loss true (r x) + P x false * loss false (r x))

/-- Risk of a rule of the view and the light's message. -/
def riskM (P : Fin 2 → Bool → ℝ) (r : Fin 2 → Bool → Bool) : ℝ :=
  ∑ x : Fin 2, (P x true * loss true (r x true) + P x false * loss false (r x false))

/-- The ACT-optimal rule: go early, slow late. -/
def fAct (x : Fin 2) : Bool := decide (x = 0)

/-- The always-slow rule. -/
def slow (_x : Fin 2) : Bool := false

/-- The message rule: go iff the phase lasts. -/
def gMsg (_x : Fin 2) (y : Bool) : Bool := !y

theorem marg_eq : marg actW = marg cutW := by
  funext x; fin_cases x <;> simp [marg, actW, cutW]

theorem monitor_blind {β : Type*} (M : (Fin 2 → ℝ) → β) : M (marg actW) = M (marg cutW) := by
  rw [marg_eq]

theorem fAct_risk : riskV actW fAct = 1 / 2 := by
  norm_num [riskV, Fin.sum_univ_two, actW, fAct, loss]

theorem act_opt (r : Fin 2 → Bool) : riskV actW fAct ≤ riskV actW r := by
  rw [fAct_risk]
  cases h0 : r 0 <;> cases h1 : r 1 <;> simp [riskV, Fin.sum_univ_two, actW, loss, h0, h1] <;> norm_num

theorem cut_harm : riskV cutW fAct = 21 / 2 ∧ riskV cutW slow = 1 ∧ ∀ r, riskV cutW slow ≤ riskV cutW r := by
  refine ⟨?_, ?_, fun r => ?_⟩
  · norm_num [riskV, Fin.sum_univ_two, cutW, fAct, loss]
  · norm_num [riskV, Fin.sum_univ_two, cutW, slow, loss]
  · cases h0 : r 0 <;> cases h1 : r 1 <;> simp [riskV, Fin.sum_univ_two, cutW, slow, loss, h0, h1] <;> norm_num

theorem message_opt_act (r : Fin 2 → Bool → Bool) : riskM actW gMsg ≤ riskM actW r := by
  cases h0 : r 0 true <;> cases h1 : r 0 false <;> cases h2 : r 1 true <;> cases h3 : r 1 false <;>
    simp [riskM, Fin.sum_univ_two, actW, gMsg, loss, h0, h1, h2, h3] <;> norm_num

theorem message_opt_cut (r : Fin 2 → Bool → Bool) : riskM cutW gMsg ≤ riskM cutW r := by
  cases h0 : r 0 true <;> cases h1 : r 0 false <;> cases h2 : r 1 true <;> cases h3 : r 1 false <;>
    simp [riskM, Fin.sum_univ_two, cutW, gMsg, loss, h0, h1, h2, h3] <;> norm_num

/-- EXT: a third view (very late) with weight ⅓, never present under the training light. -/
def actW3 (x : Fin 3) : ℝ := if x = 2 then 0 else 1 / 2

def extW3 (_x : Fin 3) : ℝ := 1 / 3

theorem ext_detectable : ∃ x : Fin 3, actW3 x = 0 ∧ 0 < extW3 x :=
  ⟨2, by simp [actW3], by norm_num [extW3]⟩

end

end CIGAMF.P13.CityConditionalShiftV1

#print axioms CIGAMF.P13.CityConditionalShiftV1.monitor_blind
#print axioms CIGAMF.P13.CityConditionalShiftV1.act_opt
#print axioms CIGAMF.P13.CityConditionalShiftV1.cut_harm
#print axioms CIGAMF.P13.CityConditionalShiftV1.message_opt_act
#print axioms CIGAMF.P13.CityConditionalShiftV1.message_opt_cut
#print axioms CIGAMF.P13.CityConditionalShiftV1.ext_detectable
