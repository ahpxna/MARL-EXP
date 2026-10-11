import Mathlib

/-!
# The zero-byte emulator (EMU_OLD) is exact iff coverage holds — E12-a

PROTOCOL_E3_E12_E14_G3_G6_20261004 §E12 (written 04/10/2026 05:3x EDT, after the E12 panel: ledger L-330, 0 exceptions in
532 480 OLD agent-steps).  `scripts/MARL_e3_mixed_fleet_eval_v2.ExactVO(packet_only=True, rule='older')` builds, for OLD
receiver `i` and every sender `j` that the public legacy mirror lists at measurement time `ms j`, the entry
`(ms j, payload)` when a copy of that measurement is USABLE (received directly or relayed at age < 14 steps, so the 4-bit age
recovers the time); otherwise it SUBSTITUTES the newest usable older copy (rule `older`), drops the entry (`absent`) or
takes the current inbox entry (`fresh`).

## The model
* `ms : Fin m → Option ℕ` — the mirror's measurement time per sender (`none`: the K1 view has no entry for `j`).
* `meas j τ` — sender `j`'s measurement at time `τ` (the honest payload).  `refView` is the K1 view: `(τ, meas j τ)`.
* `Store` — what receiver `i` holds: a decidable usability predicate on keys `(j, τ)` and the payload stored for each key.
  HONEST store: every usable key carries the true measurement.  The reference entries themselves are honest by
  `ref_honest` of `LeanMarlLegacyViewDecoderV1`; here honesty of the RECEIVER's copies is a hypothesis.
* `emuView ms S sub` — the emulator with an ARBITRARY substitution rule `sub j τ` used when `(j, τ)` is not usable.  The
  only property used is `OlderOnly sub`: a substitute is strictly older than `τ` (or absent).  The implementation's `older`
  rule (`olderMax`, the newest usable older key) and the `absent` rule are both instances.
* Coverage `Covered ms S` — every listed key is usable.

## WHAT IS PROVED
* `emu_eq_ref_iff` — for an honest store and any `OlderOnly` substitution: emulated view = K1 view ⟺ coverage.
* `olderMax_olderOnly`, `absent_olderOnly` — the implementation's two rules satisfy the hypothesis.
* `emu_older_iff`, `emu_absent_iff` — the corollaries for those two rules (E12-b's prediction "view equal ⟺ C(i,t)").
* `fresh_sufficient` — under the `fresh` rule coverage is still sufficient …
* `fresh_not_necessary` — … but not necessary: a current inbox copy can coincide with the listed key while that key is not
  usable (e.g. received only at age ≥ 14), so the views agree without coverage.
* `dishonest_breaks` — the honesty hypothesis is needed: a covered but dishonest store gives a different view.
* `hyps_satisfiable`, `uncovered_instance` — the hypotheses of the iff hold on a concrete instance with coverage, and on one
  without coverage (both directions are exercised; nothing is vacuous).

## WHAT THIS DOES NOT ESTABLISH
* Nothing about returns: equal views on the SAME physical trajectory say nothing about OLD returns in a mixed fleet
  (E13: per-agent non-inferiority fails).  Coverage is a property of the channel realisation; its rate is measured
  (E12-d: 3.8e-5 failures per OLD agent-step), not proved.
* The honesty of the receiver's copies (packet integrity and the age-to-time recovery below the 14-step cap) is assumed.
-/

namespace MarlPacketEmulator

variable {m : ℕ} {V : Type}

/-- The K1 (legacy) view of one receiver: sender `j`'s entry is its measurement at the mirror's time `ms j`. -/
def refView (ms : Fin m → Option ℕ) (meas : Fin m → ℕ → V) : Fin m → Option (ℕ × V) :=
  fun j => (ms j).map (fun τ => (τ, meas j τ))

/-- What the receiver holds: usable keys and the payload stored under each key. -/
structure Store (m : ℕ) (V : Type) where
  usable : Fin m → ℕ → Prop
  dec : ∀ j τ, Decidable (usable j τ)
  pay : Fin m → ℕ → V

attribute [instance] Store.dec

/-- Honest store: every usable key carries the true measurement. -/
def Honest (S : Store m V) (meas : Fin m → ℕ → V) : Prop := ∀ j τ, S.usable j τ → S.pay j τ = meas j τ

/-- Coverage `C(i, t)`: every key listed by the mirror is usable. -/
def Covered (ms : Fin m → Option ℕ) (S : Store m V) : Prop := ∀ j τ, ms j = some τ → S.usable j τ

/-- The emulator with substitution rule `sub` for non-usable listed keys. -/
def emuView (ms : Fin m → Option ℕ) (S : Store m V) (sub : Fin m → ℕ → Option (ℕ × V)) : Fin m → Option (ℕ × V) :=
  fun j => match ms j with
    | none => none
    | some τ => if S.usable j τ then some (τ, S.pay j τ) else sub j τ

/-- A substitution never returns the listed time or a newer one. -/
def OlderOnly (sub : Fin m → ℕ → Option (ℕ × V)) : Prop := ∀ j τ x, sub j τ = some x → x.1 < τ

/-- **E12-a.** Honest store, older-only substitution: the emulated view equals the K1 view iff coverage holds. -/
theorem emu_eq_ref_iff (ms : Fin m → Option ℕ) (meas : Fin m → ℕ → V) (S : Store m V)
    (sub : Fin m → ℕ → Option (ℕ × V)) (hh : Honest S meas) (hs : OlderOnly sub) :
    emuView ms S sub = refView ms meas ↔ Covered ms S := by
  constructor
  · intro h j τ hj
    by_contra hu
    have hj' := congrFun h j
    simp only [emuView, refView, hj, Option.map_some, if_neg hu] at hj'
    exact absurd (hs j τ _ hj') (lt_irrefl τ)
  · intro hc
    funext j
    unfold emuView refView
    cases hj : ms j with
    | none => simp
    | some τ =>
      have hu := hc j τ hj
      simp [if_pos hu, hh j τ hu]

/-- The implementation's `older` rule: the newest usable key strictly older than `τ`, if any. -/
noncomputable def olderMax (S : Store m V) : Fin m → ℕ → Option (ℕ × V) :=
  fun j τ => by
    classical
    exact if ∃ k, k < τ ∧ S.usable j k then
      some (Nat.findGreatest (fun k => S.usable j k) (τ - 1), S.pay j (Nat.findGreatest (fun k => S.usable j k) (τ - 1)))
    else none

theorem olderMax_olderOnly (S : Store m V) : OlderOnly (olderMax S) := by
  intro j τ x hx
  classical
  unfold olderMax at hx
  split_ifs at hx with h
  · obtain ⟨k, hk, _⟩ := h
    cases hx
    have hle : Nat.findGreatest (fun k => S.usable j k) (τ - 1) ≤ τ - 1 := Nat.findGreatest_le _
    simp only
    omega

/-- The `absent` rule: no substitute. -/
def absent : Fin m → ℕ → Option (ℕ × V) := fun _ _ => none

theorem absent_olderOnly : OlderOnly (m := m) (V := V) absent := by
  intro j τ x hx; simp [absent] at hx

theorem emu_older_iff (ms : Fin m → Option ℕ) (meas : Fin m → ℕ → V) (S : Store m V) (hh : Honest S meas) :
    emuView ms S (olderMax S) = refView ms meas ↔ Covered ms S :=
  emu_eq_ref_iff ms meas S _ hh (olderMax_olderOnly S)

theorem emu_absent_iff (ms : Fin m → Option ℕ) (meas : Fin m → ℕ → V) (S : Store m V) (hh : Honest S meas) :
    emuView ms S absent = refView ms meas ↔ Covered ms S :=
  emu_eq_ref_iff ms meas S _ hh absent_olderOnly

/-- The `fresh` rule: the current inbox entry of `j` (any entry, not necessarily usable). -/
def fresh (cur : Fin m → Option (ℕ × V)) : Fin m → ℕ → Option (ℕ × V) := fun j _ => cur j

theorem fresh_sufficient (ms : Fin m → Option ℕ) (meas : Fin m → ℕ → V) (S : Store m V)
    (cur : Fin m → Option (ℕ × V)) (hh : Honest S meas) (hc : Covered ms S) :
    emuView ms S (fresh cur) = refView ms meas := by
  funext j
  unfold emuView refView
  cases hj : ms j with
  | none => simp
  | some τ =>
    have hu := hc j τ hj
    simp [if_pos hu, hh j τ hu]

/-- Under `fresh`, coverage is not necessary: one sender, listed at time 5, nothing usable, and the current inbox copy is
exactly the listed measurement (in E3: a copy seen only at age ≥ 14 is not usable but can be the current one). -/
theorem fresh_not_necessary :
    ∃ (ms : Fin 1 → Option ℕ) (meas : Fin 1 → ℕ → ℕ) (S : Store 1 ℕ) (cur : Fin 1 → Option (ℕ × ℕ)),
      Honest S meas ∧ emuView ms S (fresh cur) = refView ms meas ∧ ¬ Covered ms S := by
  refine ⟨fun _ => some 5, fun _ τ => τ, ⟨fun _ _ => False, fun _ _ => inferInstance, fun _ τ => τ⟩,
    fun _ => some (5, 5), ?_, ?_, ?_⟩
  · intro j τ h; exact h.elim
  · funext j; simp [emuView, refView, fresh]
  · intro h; exact h 0 5 rfl

/-- Honesty is needed: a covered store whose payload is wrong gives a different view. -/
theorem dishonest_breaks :
    ∃ (ms : Fin 1 → Option ℕ) (meas : Fin 1 → ℕ → ℕ) (S : Store 1 ℕ),
      Covered ms S ∧ emuView ms S (olderMax S) ≠ refView ms meas := by
  refine ⟨fun _ => some 5, fun _ τ => τ, ⟨fun _ _ => True, fun _ _ => inferInstance, fun _ _ => 0⟩, ?_, ?_⟩
  · intro j τ _; trivial
  · intro h
    have := congrFun h 0
    simp [emuView, refView] at this

/-- The hypotheses of `emu_eq_ref_iff` hold on a covered instance (both sides then agree). -/
theorem hyps_satisfiable :
    ∃ (ms : Fin 2 → Option ℕ) (meas : Fin 2 → ℕ → ℕ) (S : Store 2 ℕ),
      Honest S meas ∧ Covered ms S ∧ emuView ms S (olderMax S) = refView ms meas := by
  refine ⟨fun j => if j = 0 then some 3 else none, fun j τ => τ + j, ⟨fun _ _ => True, fun _ _ => inferInstance, fun j τ => τ + j⟩, ?_, ?_, ?_⟩
  · intro j τ _; rfl
  · intro j τ _; trivial
  · exact (emu_older_iff _ _ _ (fun j τ _ => rfl)).2 (fun j τ _ => trivial)

/-- … and on an uncovered honest instance, where the views differ (the other direction is exercised too). -/
theorem uncovered_instance :
    ∃ (ms : Fin 1 → Option ℕ) (meas : Fin 1 → ℕ → ℕ) (S : Store 1 ℕ),
      Honest S meas ∧ ¬ Covered ms S ∧ emuView ms S (olderMax S) ≠ refView ms meas := by
  refine ⟨fun _ => some 5, fun _ τ => τ, ⟨fun _ τ => τ = 2, fun _ _ => inferInstance, fun _ τ => τ⟩, ?_, ?_, ?_⟩
  · intro j τ _; rfl
  · intro h; exact absurd (h 0 5 rfl) (by decide)
  · intro h
    exact absurd ((emu_older_iff _ _ _ (fun j τ _ => rfl)).1 h) (fun hc => absurd (hc 0 5 rfl) (by decide))

#print axioms emu_eq_ref_iff
#print axioms olderMax_olderOnly
#print axioms absent_olderOnly
#print axioms emu_older_iff
#print axioms emu_absent_iff
#print axioms fresh_sufficient
#print axioms fresh_not_necessary
#print axioms dishonest_breaks
#print axioms hyps_satisfiable
#print axioms uncovered_instance

end MarlPacketEmulator
