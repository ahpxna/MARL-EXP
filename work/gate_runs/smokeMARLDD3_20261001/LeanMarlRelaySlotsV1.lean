import Mathlib
import LeanMarlRelayOneHopV1

/-!
# Relay with fixed slot sets (RELAY v3, the 4×4 grid): one-step freshness holds exactly for the agents every head carries

`models/marl_relay_v3.py` (ledger L-186) keeps the 185-bit relay packet for teams larger than nine: sender `k` relays
only the agents in a fixed public slot set `slot k` (the 8 nearest on the grid).  Its merge
(`make_slot_merge`, mirrored by `make_slot_mirror`, asserted equal at every step) is the E3 merge of
`LeanMarlRelayOneHopV1.table` with the relayed entries of `k` restricted to `slot k`:

    T_t(i,j) = t                                                       if j ∈ S_t(i)
             = max( C_t(i,j), max_{k ∈ S_t(i), j ∈ slot k} T_{t-1}(k,j) )   otherwise.

## WHAT IS PROVED
* `stable_le_lastTx` — no copy is fresher than the last transmission (as for the full relay).
* `stable_all` — with `slot k = everyone but k` the slot merge IS the full merge (`LeanMarlRelayOneHopV1.table`): the
  formal counterpart of the 3×3 parity test of ledger L-186 (on 3×3 the 8 nearest are everyone else).
* `head_stable_fresh`, `one_hop_slots` — under the covering-head hypotheses of `LeanMarlRelayOneHopV1.CoveringHeads`,
  if agent `j` is in the slot set of every head other than itself, then every receiver other than the next head holds
  a copy of `j` at least as recent as `j`'s last transmission up to the previous step: the one-step sandwich holds for
  `j` exactly as in `one_hop`.
* `slots_sharp` — the carrying hypothesis cannot be dropped: on a four-agent schedule that satisfies EVERY covering
  hypothesis at every step (`w4_hyps`), removing one agent from one head's slot set breaks the lower bound
  (`lastTx = 1`, table `= 0`), while the full slot sets satisfy it (`one_hop` applies, `w4_full_one_hop`).

## WHAT THIS DOES NOT ESTABLISH
- Any bound for an agent outside some head's slot set: it reaches receivers through other senders (multi-hop) and its
  age is not bounded by this theorem.  On the 4×4 grid with nearest-8 slots and a moving head, most agents are outside
  some head's slot set, so this module PREDICTS that the 3×3 one-hop guarantee does not transfer to the 4×4 relay.
- That the 4×4 runs use covering heads (the hub head) — that is the evaluator's `--order` option.
-/

namespace CIGAMF.P13.MarlRelaySlots

open Finset
open CIGAMF.P13.MarlRelayOneHop

variable {m : ℕ}

section Dynamics

variable (S : ℕ → Fin m → Finset (Fin m)) (slot : Fin m → Finset (Fin m))

/-- The RELAY v3 merge (encoded measurement times): decoded sender `k` relays only the agents in `slot k`. -/
def stable : ℕ → Fin m → Fin m → ℕ
  | 0, i, j => if j ∈ S 0 i then 1 else 0
  | t + 1, i, j =>
      if j ∈ S (t + 1) i then t + 2
      else max (cache S t i j) (((S (t + 1) i).filter fun k => j ∈ slot k).sup fun k => stable t k j)

theorem stable_le_lastTx (t : ℕ) : ∀ i j : Fin m, stable S slot t i j ≤ lastTx S t j := by
  induction t with
  | zero =>
      intro i j
      simp only [stable]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · exact Nat.zero_le _
  | succ t ih =>
      intro i j
      simp only [stable]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · refine max_le ((cache_le_lastTx S t i j).trans (lastTx_mono S t j)) ?_
        refine Finset.sup_le fun k _ => ?_
        exact (ih k j).trans (lastTx_mono S t j)

theorem stable_of_mem {t : ℕ} {i j : Fin m} (h : j ∈ S t i) : stable S slot t i j = t + 1 := by
  cases t with
  | zero => simp only [stable]; rw [if_pos h]
  | succ t => simp only [stable]; rw [if_pos h]

/-- Decoding `k` at step `t+1`, when `k` carries `j`, makes `i`'s copy of `j` at least as fresh as `k`'s. -/
theorem stable_ge_of_decoded {t : ℕ} {i k : Fin m} (hk : k ∈ S (t + 1) i) {j : Fin m} (hj : j ∈ slot k) :
    stable S slot t k j ≤ stable S slot (t + 1) i j := by
  simp only [stable]
  split_ifs with h
  · exact (stable_le_lastTx S slot t k j).trans (lastTx_le_succ S t j) |>.trans (by omega)
  · refine le_max_of_le_right (Finset.le_sup (f := fun k => stable S slot t k j) ?_)
    exact mem_filter.mpr ⟨hk, hj⟩

/-- **Parity.**  With every sender carrying everybody else, the slot merge is the full E3 merge. -/
theorem stable_all (t : ℕ) : ∀ i j : Fin m, stable S (fun k => univ.erase k) t i j = table S t i j := by
  induction t with
  | zero => intro i j; simp only [stable, table]
  | succ t ih =>
      intro i j
      simp only [stable, table]
      split_ifs with h
      · rfl
      · congr 1
        rw [Finset.filter_true_of_mem]
        · exact Finset.sup_congr rfl fun k _ => ih k j
        · intro k hk
          refine mem_erase.mpr ⟨?_, mem_univ _⟩
          rintro rfl
          exact h hk

variable {S slot}

/-- **The head's copy of a carried agent is as fresh as the network.** -/
theorem head_stable_fresh {h : ℕ → Fin m} (H : CoveringHeads S h) (j : Fin m)
    (hcar : ∀ u, j ≠ h u → j ∈ slot (h u)) :
    ∀ t, j ≠ h (t + 1) → stable S slot t (h (t + 1)) j = lastTx S t j := by
  intro t
  induction t with
  | zero =>
      intro hj
      by_cases hx : ∃ i, j ∈ S 0 i
      · have hm := H.covers 0 j hx hj
        rw [stable_of_mem S slot hm, lastTx_of_mem S hm]
      · have hnot : j ∉ S 0 (h (0 + 1)) := fun hm => hx ⟨_, hm⟩
        simp only [stable, lastTx]
        rw [if_neg hnot, if_neg hx]
  | succ t ih =>
      intro hj
      by_cases hx : ∃ i, j ∈ S (t + 1) i
      · have hm := H.covers (t + 1) j hx hj
        rw [stable_of_mem S slot hm, lastTx_of_mem S hm]
      · refine le_antisymm (stable_le_lastTx S slot (t + 1) _ j) ?_
        rw [lastTx_succ_of_not S t j hx]
        have hhead : h (t + 1) ∈ S (t + 1) (h (t + 1 + 1)) :=
          H.head_decoded (t + 1) (h (t + 1 + 1)) (H.distinct (t + 1))
        have hjne : j ≠ h (t + 1) := by
          rintro rfl
          exact hx ⟨_, hhead⟩
        rw [← ih hjne]
        exact stable_ge_of_decoded S slot hhead (hcar (t + 1) hjne)

/-- **One-step freshness with slots**, for every agent carried by every head other than itself. -/
theorem one_hop_slots {h : ℕ → Fin m} (H : CoveringHeads S h) (j : Fin m)
    (hcar : ∀ u, j ≠ h u → j ∈ slot (h u)) (t : ℕ) (i : Fin m) (hi : i ≠ h (t + 1)) :
    lastTx S t j ≤ stable S slot (t + 1) i j ∧ stable S slot (t + 1) i j ≤ lastTx S (t + 1) j := by
  refine ⟨?_, stable_le_lastTx S slot (t + 1) i j⟩
  by_cases hm : j ∈ S (t + 1) i
  · rw [stable_of_mem S slot hm]
    exact (lastTx_le_succ S t j).trans (by omega)
  · have hhead : h (t + 1) ∈ S (t + 1) i := H.head_decoded (t + 1) i hi
    have hjne : j ≠ h (t + 1) := by
      rintro rfl
      exact hm hhead
    rw [← head_stable_fresh H j hcar t hjne]
    exact stable_ge_of_decoded S slot hhead (hcar (t + 1) hjne)

end Dynamics

section Sharp

/-- Four-agent witness head sequence `0, 1, 2, 3, 0, …`. -/
def w4Head (t : ℕ) : Fin 4 := ⟨t % 4, Nat.mod_lt _ (by decide)⟩

/-- Prefix decoding of the order `(h, h+1, h+2, h+3)` with thresholds `2, 3, 1, 1`: the head decodes `h+1`; receiver
`h+1` decodes `h` and `h+2`; the others decode `h`.  Sender `h+2` reaches only the next head, so relay matters. -/
def w4S (t : ℕ) (i : Fin 4) : Finset (Fin 4) :=
  if i = w4Head t then {w4Head t + 1} else if i = w4Head t + 1 then {w4Head t, w4Head t + 2} else {w4Head t}

theorem w4Head_succ (t : ℕ) : w4Head (t + 1) = w4Head t + 1 := by
  apply Fin.ext
  simp only [w4Head, Fin.val_add]
  omega

theorem w4_hyps : CoveringHeads w4S w4Head := by
  refine ⟨?_, ?_, ?_⟩
  · intro t i hi
    unfold w4S
    generalize w4Head t = a at hi ⊢
    revert a i
    decide
  · intro t j hx hj
    rw [w4Head_succ] at hj ⊢
    obtain ⟨i, hi⟩ := hx
    revert hi hj
    unfold w4S
    generalize w4Head t = a
    revert a i j
    decide
  · intro t
    rw [w4Head_succ]
    generalize w4Head t = a
    revert a
    decide

/-- Full slot sets: the one-step bound holds on the witness at every step. -/
theorem w4_full_one_hop (t : ℕ) (i j : Fin 4) (hi : i ≠ w4Head (t + 1)) :
    lastTx w4S t j ≤ stable w4S (fun k => univ.erase k) (t + 1) i j := by
  rw [stable_all]
  exact (one_hop w4_hyps t i j hi).1

/-- Slot sets with one hole: head `1` does not carry agent `2`. -/
def w4Slot (k : Fin 4) : Finset (Fin 4) := if k = 1 then {0, 3} else univ.erase k

/-- **The carrying hypothesis is necessary.**  Every covering hypothesis holds (`w4_hyps`), receiver `3` is not the
step-1 head, agent `2` was transmitted at step `0` (`lastTx = 1`), and yet receiver `3` holds no copy of it after
step `1`, because the only sender that heard `2` is head `1`, which does not carry it. -/
theorem slots_sharp :
    (3 : Fin 4) ≠ w4Head 1 ∧ (2 : Fin 4) ∉ w4Slot (w4Head 1) ∧
    lastTx w4S 0 2 = 1 ∧ stable w4S w4Slot 1 3 2 = 0 := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · simp only [lastTx]
    rw [if_pos ⟨1, by decide⟩]
  · decide

end Sharp

end CIGAMF.P13.MarlRelaySlots

#print axioms CIGAMF.P13.MarlRelaySlots.stable_le_lastTx
#print axioms CIGAMF.P13.MarlRelaySlots.stable_all
#print axioms CIGAMF.P13.MarlRelaySlots.head_stable_fresh
#print axioms CIGAMF.P13.MarlRelaySlots.one_hop_slots
#print axioms CIGAMF.P13.MarlRelaySlots.w4_hyps
#print axioms CIGAMF.P13.MarlRelaySlots.w4_full_one_hop
#print axioms CIGAMF.P13.MarlRelaySlots.slots_sharp
