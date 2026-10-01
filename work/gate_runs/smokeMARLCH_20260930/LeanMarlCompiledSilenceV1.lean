import Mathlib
import LeanUnifiedObstructionOrderV1

/-!
# Compiled silence: what a zero-byte policy can and cannot decide, and the conditioning pitfall

A zero-byte policy of receiver `i` acts on its local observation only: it is a function of `loc F` where `F` ranges
over global states (worlds) and `loc : World → O`.  A policy with messages acts on a finer observation `obs`
(`obs F = obs G → loc F = loc G`).  `safe F` is the set of acceptable actions in world `F`.  This module instantiates
the corpus's obstruction law (`LeanUnifiedObstructionOrderV1`, PROVED) at these objects, and proves the counting
identity behind the evaluation pitfall of paper_marl_v2 (V-U).

## WHAT IS PROVED
* `zero_byte_safe_iff` — some zero-byte policy is acceptable in every world iff no obstruction lies inside a local
  observation class (instance of `classes_resolve_iff`).
* `zero_byte_fails_on_obstruction` — if an obstruction lies inside one local class, EVERY zero-byte policy is
  unacceptable in some world of it (instance of `obstruction_error_floor_deterministic`); a randomised zero-byte rule
  has unacceptable mass at least `1/|H|` somewhere in it (`obstruction_error_floor_randomized`).
* `messages_keep_safety` — whenever a zero-byte policy is acceptable everywhere, so is a policy on any finer observation
  (instance of `resolution_refines`): messages cannot be needed where no obstruction hides.
* `agreement_split` — for any records and any two policies `X`, `Z` compared with a reference `T`:
  `#{X = T} − #{Z = T} = #{Z ≠ T, X = T} − #{Z = T, X ≠ T}` in `ℤ`.  The whole advantage of `X` over `Z` is, by
  construction, on the records where `Z` departs from `T`.
* `split_is_tautological` — on the records where `Z` departs from `T`, `Z` agrees with `T` on none, so every `X`
  "does at least as well there".  Showing that a policy does better on that split is therefore no evidence.
* `excess_over_null` — the informative comparison: against a second policy `Z'` with the same information, the excess
  on the split is `#{Z ≠ T, X = T} − #{Z ≠ T, Z' = T}`, which can be negative (`excess_can_be_negative`).

## WHAT THIS DOES NOT ESTABLISH
- That the E3 teacher's action is the acceptable set: the probe uses the teacher's action as a reference only.
- Any rate or sample statement.
-/

namespace CIGAMF.P13.MarlCompiledSilence

open Finset
open CIGAMF.P13.UnifiedObstructionOrder

variable {World Act O M : Type*} [DecidableEq World] [Fintype World] [DecidableEq Act] [Fintype Act]
  [DecidableEq O] [Fintype O] [DecidableEq M] [Fintype M]

variable (safe : World → Finset Act)

/-- **A zero-byte policy suffices exactly when no obstruction hides inside a local class.** -/
theorem zero_byte_safe_iff (loc : World → O) :
    (∃ pol : O → Act, ∀ F, pol (loc F) ∈ safe F)
      ↔ (∀ H : Finset World, IsObstruction safe H → ¬ ∃ k : O, H ⊆ univ.filter (fun F => loc F = k)) := by
  rw [← classes_resolve_iff safe loc]
  constructor
  · rintro ⟨pol, hpol⟩ k
    exact ⟨pol k, fun F hF => by
      simp only [mem_filter, mem_univ, true_and] at hF
      rw [← hF]; exact hpol F⟩
  · intro hall
    choose pol hpol using hall
    exact ⟨pol, fun F => hpol (loc F) F (by simp)⟩

/-- **Every zero-byte policy fails somewhere on an obstruction inside one local class.** -/
theorem zero_byte_fails_on_obstruction (loc : World → O) (pol : O → Act) {H : Finset World} (k : O)
    (hH : IsObstruction safe H) (hk : H ⊆ univ.filter (fun F => loc F = k)) :
    ∃ F ∈ H, pol (loc F) ∉ safe F := by
  obtain ⟨F, hF, hns⟩ := obstruction_error_floor_deterministic safe hH (pol k)
  refine ⟨F, hF, ?_⟩
  have : loc F = k := by simpa using hk hF
  rw [this]; exact hns

/-- **Messages cannot be needed where no obstruction hides**: an everywhere-acceptable zero-byte policy gives an
everywhere-acceptable policy on any finer observation. -/
theorem messages_keep_safety [Nonempty Act] (loc : World → O) (obs : World → M)
    (hfiner : ∀ F G, obs F = obs G → loc F = loc G)
    (hzero : ∀ k : O, HasCommon safe (univ.filter fun F => loc F = k)) :
    ∀ l : M, HasCommon safe (univ.filter fun F => obs F = l) :=
  resolution_refines safe loc obs hfiner hzero

section Counting

variable {R A : Type*} [Fintype R] [DecidableEq R] [DecidableEq A]

/-- **Agreement split.**  The difference in agreement with a reference `T` between two policies, record by record. -/
theorem agreement_split (X Z T : R → A) :
    ((univ.filter fun r => X r = T r).card : ℤ) - (univ.filter fun r => Z r = T r).card
      = ((univ.filter fun r => Z r ≠ T r ∧ X r = T r).card : ℤ)
        - (univ.filter fun r => Z r = T r ∧ X r ≠ T r).card := by
  have h1 : (univ.filter fun r => X r = T r).card
      = (univ.filter fun r => Z r ≠ T r ∧ X r = T r).card + (univ.filter fun r => Z r = T r ∧ X r = T r).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext r; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
    · rw [disjoint_filter]; intro r _ h1 h2; exact h1.1 h2.1
  have h2 : (univ.filter fun r => Z r = T r).card
      = (univ.filter fun r => Z r = T r ∧ X r ≠ T r).card + (univ.filter fun r => Z r = T r ∧ X r = T r).card := by
    rw [← card_union_of_disjoint]
    · congr 1; ext r; simp only [mem_filter, mem_univ, true_and, mem_union]; tauto
    · rw [disjoint_filter]; intro r _ h1 h2; exact h1.2 h2.2
  rw [h1, h2]; push_cast; ring

/-- **The split is tautological**: on the records where `Z` departs from `T`, `Z` agrees nowhere, so every `X` does at
least as well there. -/
theorem split_is_tautological (X Z T : R → A) :
    (univ.filter fun r => Z r ≠ T r ∧ Z r = T r).card = 0 ∧
      (univ.filter fun r => Z r ≠ T r ∧ Z r = T r).card ≤ (univ.filter fun r => Z r ≠ T r ∧ X r = T r).card := by
  have h : (univ.filter fun r => Z r ≠ T r ∧ Z r = T r) = ∅ := by
    ext r
    simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
    intro h1 h2
    exact h1 h2
  rw [h, card_empty]; exact ⟨rfl, Nat.zero_le _⟩

/-- **The informative comparison** against a same-information null `Z'`. -/
def excessOverNull (X Z Z' T : R → A) : ℤ :=
  ((univ.filter fun r => Z r ≠ T r ∧ X r = T r).card : ℤ) - (univ.filter fun r => Z r ≠ T r ∧ Z' r = T r).card

/-- The excess over the null is not positive by construction: it is negative when the null recovers more. -/
theorem excess_can_be_negative :
    excessOverNull (R := Fin 2) (A := Bool) (fun _ => false) (fun _ => false) (fun _ => true) (fun _ => true) < 0 := by
  decide

end Counting

end CIGAMF.P13.MarlCompiledSilence

#print axioms CIGAMF.P13.MarlCompiledSilence.zero_byte_safe_iff
#print axioms CIGAMF.P13.MarlCompiledSilence.zero_byte_fails_on_obstruction
#print axioms CIGAMF.P13.MarlCompiledSilence.messages_keep_safety
#print axioms CIGAMF.P13.MarlCompiledSilence.agreement_split
#print axioms CIGAMF.P13.MarlCompiledSilence.split_is_tautological
#print axioms CIGAMF.P13.MarlCompiledSilence.excess_can_be_negative
