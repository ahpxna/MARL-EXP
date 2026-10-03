import Mathlib
import LeanMarlStrongOneHopV1
import LeanMarlDecisionLifetimeV1

/-!
# From one-step relay freshness to the relay action (the H7 composition)

`LeanMarlDecisionLifetimeV1.relay_action_equals_fresh` needs an age bound `h ≤ H` on the relay view, and its docstring
records that no such bound was proved.  `LeanMarlStrongOneHopV1.strong_one_hop` supplies one relative to the injection
ages: under `StrongHeads`, every copy is at most one step older than the agent's last transmission.  This module
composes the two.

Times are encoded as in `LeanMarlRelayOneHopV1` (step `t` is stored as `t + 1`, `0` = never), so at step `t` the age
of receiver `i`'s copy of agent `j` is `t + 1 − table t i j`, and the injection age of `j` is `t + 1 − lastTx t j`.

## WHAT IS PROVED
* `relay_age_le_inj` — under `StrongHeads`, `relayAge (t+1) i j ≤ injAge t j + 1` for every receiver `i` and agent
  `j ≠ i`, the head included.
* `relay_age_bound` — if every injection age at step `t` is at most `Φ`, every relayed copy at step `t+1` is at most
  `Φ + 1` old; `viewAge_le` for the maximal age of a receiver's view.
* `relay_action_fresh` — **the composition**: if the actor's gauge perturbation on its relay view is at most
  `e0 + ν · (maximal age of the view)` and the fresh margin of `a0` exceeds `2 (e0 + ν (Φ + 1))`, the relay action is
  `a0`.
* `w_inj_zero`, `relay_decision_satisfiable` — on the four-agent schedule of `LeanMarlNewsRelayV1` (repeated heads),
  every injection age at step 2 is `0`, and a two-action instance with `ν > 0` satisfies every hypothesis.

## WHAT THIS DOES NOT ESTABLISH
- The injection bound `Φ` for the hub (covering) head: under age-first ordering `Φ = m − 1`
  (`LeanMarlAgeFirstInjectionV1`), but a covering head is not age-first, and at constant capacity the covering head is
  transmitted at every step (`LeanMarlPriceOfCoverageV1.const_cover_transmitted`), so `Φ` must be supplied by the
  schedule.
- The perturbation model `e0 + ν · age` is measured (V-F), not derived; nothing about learned actors beyond it.
-/

namespace CIGAMF.P13.MarlRelayDecision

open Finset
open CIGAMF.P13.MarlRelayOneHop CIGAMF.P13.MarlStrongOneHop CIGAMF.P13.MarlDecisionLifetime

variable {m : ℕ}

/-- Age of receiver `i`'s copy of `j` at step `t` (encoded times). -/
def relayAge (S : ℕ → Fin m → Finset (Fin m)) (t : ℕ) (i j : Fin m) : ℕ := t + 1 - table S t i j

/-- Injection age of `j` at step `t`: steps since its last transmission. -/
def injAge (S : ℕ → Fin m → Finset (Fin m)) (t : ℕ) (j : Fin m) : ℕ := t + 1 - lastTx S t j

/-- The oldest copy in receiver `i`'s view at step `t`. -/
def viewAge (S : ℕ → Fin m → Finset (Fin m)) (t : ℕ) (i : Fin m) : ℕ :=
  (univ.erase i).sup (relayAge S t i)

variable {S : ℕ → Fin m → Finset (Fin m)}

theorem relay_age_le_inj {h : ℕ → Fin m} (H : StrongHeads S h) (t : ℕ) (i j : Fin m) (hji : j ≠ i) :
    relayAge S (t + 1) i j ≤ injAge S t j + 1 := by
  have h1 := strong_one_hop H t i j hji
  have h2 := lastTx_le_succ S t j
  unfold relayAge injAge
  omega

theorem relay_age_bound {h : ℕ → Fin m} (H : StrongHeads S h) (Φ t : ℕ)
    (hinj : ∀ j, injAge S t j ≤ Φ) (i j : Fin m) (hji : j ≠ i) :
    relayAge S (t + 1) i j ≤ Φ + 1 :=
  (relay_age_le_inj H t i j hji).trans (by have := hinj j; omega)

theorem viewAge_le {h : ℕ → Fin m} (H : StrongHeads S h) (Φ t : ℕ)
    (hinj : ∀ j, injAge S t j ≤ Φ) (i : Fin m) : viewAge S (t + 1) i ≤ Φ + 1 := by
  unfold viewAge
  refine Finset.sup_le fun j hj => ?_
  exact relay_age_bound H Φ t hinj i j (Finset.ne_of_mem_erase hj)

/-- **The composition (H7).**  One-step relay freshness, an injection bound and a margin larger than twice the
age-dependent perturbation give the fresh action on the relay view. -/
theorem relay_action_fresh {A : Type*} {h : ℕ → Fin m} (H : StrongHeads S h) (Φ t : ℕ)
    (hinj : ∀ j, injAge S t j ≤ Φ) (i : Fin m) (qf qr : A → ℝ) (a0 : A) (e0 ν c : ℝ) (hν : 0 ≤ ν)
    (hmove : ∀ a, |qr a - qf a - c| ≤ e0 + ν * (viewAge S (t + 1) i : ℕ))
    (hgap : ∀ b, b ≠ a0 → qf a0 - qf b > 2 * (e0 + ν * ((Φ + 1 : ℕ) : ℝ))) :
    ∀ b, b ≠ a0 → qr b < qr a0 :=
  relay_action_equals_fresh qf qr a0 e0 ν c (viewAge S (t + 1) i) (Φ + 1) hν (viewAge_le H Φ t hinj i) hmove hgap

/-! ## Satisfiability -/

/-- On the repeated-head schedule every agent is transmitted at step 2. -/
theorem w_inj_zero : ∀ j, injAge CIGAMF.P13.MarlNewsRelay.wS 2 j ≤ 0 := by
  decide

/-- Every hypothesis of `relay_action_fresh` holds on an instance with a strictly positive drift rate. -/
theorem relay_decision_satisfiable :
    StrongHeads CIGAMF.P13.MarlNewsRelay.wS CIGAMF.P13.MarlNewsRelay.wHead ∧ (∀ j, injAge CIGAMF.P13.MarlNewsRelay.wS 2 j ≤ 0) ∧
    ∃ (qf qr : Bool → ℝ) (c : ℝ),
      (∀ a, |qr a - qf a - c| ≤ (3 / 8 : ℝ) + (1 / 8 : ℝ) * (viewAge CIGAMF.P13.MarlNewsRelay.wS 3 0 : ℕ)) ∧
      (∀ b, b ≠ true → qf true - qf b > 2 * ((3 / 8 : ℝ) + (1 / 8 : ℝ) * ((0 + 1 : ℕ) : ℝ))) ∧
      qr false < qr true := by
  refine ⟨w_strong, w_inj_zero, fun b => if b then 3 else 0, fun b => if b then 13 else 10.3, 10, ?_, ?_, ?_⟩
  · intro a
    have hage : (0 : ℝ) ≤ (1 / 8 : ℝ) * (viewAge CIGAMF.P13.MarlNewsRelay.wS 3 0 : ℕ) := by positivity
    cases a <;> norm_num [abs_le] <;> linarith
  · intro b hb
    cases b
    · norm_num
    · exact absurd rfl hb
  · norm_num

end CIGAMF.P13.MarlRelayDecision

#print axioms CIGAMF.P13.MarlRelayDecision.relay_age_le_inj
#print axioms CIGAMF.P13.MarlRelayDecision.relay_age_bound
#print axioms CIGAMF.P13.MarlRelayDecision.viewAge_le
#print axioms CIGAMF.P13.MarlRelayDecision.relay_action_fresh
#print axioms CIGAMF.P13.MarlRelayDecision.w_inj_zero
#print axioms CIGAMF.P13.MarlRelayDecision.relay_decision_satisfiable
