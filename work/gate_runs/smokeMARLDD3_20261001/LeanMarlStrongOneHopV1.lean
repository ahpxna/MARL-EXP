import Mathlib
import LeanMarlRelayOneHopV1
import LeanMarlRelayMemoryV1
import LeanMarlPrefixThresholdV1
import LeanMarlNewsRelayV1

/-!
# One-step freshness for EVERY receiver, without distinct heads (the E3 transient merge)

`LeanMarlRelayOneHopV1.one_hop` assumed that consecutive heads differ and excluded the next head as a receiver.  Neither
is needed.  The E3 merge keeps the receiver's own direct decodes (`cache`), and every receiver decodes at least one
sender on the prefix channel; with these, an induction over ALL receivers gives the one-step bound for every receiver,
the head included, for any head sequence that is decoded by everybody and covers the previous step.  Repeated heads (the
evaluator's hub rule repeats its head when the rich receiver was the head, ≈ 10 % of rich7 steps, ledger L-189) are
covered.

## WHAT IS PROVED
* `fresh_of_tx` — an agent transmitted at step `t` reaches every other receiver by step `t+1`.
* `strong_one_hop` — `lastTx_t(j) ≤ T_{t+1}(i,j) ≤ lastTx_{t+1}(j)` for every receiver `i` and every agent `j ≠ i`,
  under `StrongHeads`: the head is decoded by every other receiver, the head of step `t+1` covers step `t`, and every
  receiver decodes at least one sender.  No distinctness.
* `strong_memory_redundant` — hence keeping relayed copies (gossip memory) changes nothing for ANY receiver
  (strengthens `LeanMarlRelayMemoryV1.memory_redundant`, which excluded the head).
* `prefix_nonempty`, `prefix_strong_heads` — on the prefix channel at capacity `K ≥ 1` the first and third hypotheses
  hold automatically; only the covering rule for the head remains.
* `w_strong`, `w_strong_one_hop` — the four-agent schedule of `LeanMarlNewsRelayV1` (heads `0, 3, 3, …`, so
  `CoveringHeads.distinct` fails) satisfies `StrongHeads`, and the theorem applies to it.

## WHAT THIS DOES NOT ESTABLISH
- Anything when the head does not cover (`LeanMarlAgeFirstBreaksOneHopV1`).
-/

namespace CIGAMF.P13.MarlStrongOneHop

open Finset
open CIGAMF.P13.MarlRelayOneHop

variable {m : ℕ}

section Dynamics

variable (S : ℕ → Fin m → Finset (Fin m))

/-- The hypotheses: the head is decoded by every other receiver, the next head covers the step, and every receiver
decodes at least one sender. -/
structure StrongHeads (h : ℕ → Fin m) : Prop where
  head_decoded : ∀ t i, i ≠ h t → h t ∈ S t i
  covers : ∀ t j, (∃ i, j ∈ S t i) → j ≠ h (t + 1) → j ∈ S t (h (t + 1))
  nonempty : ∀ t i, (S t i).Nonempty

theorem cache_of_mem {t : ℕ} {i j : Fin m} (h : j ∈ S t i) : cache S t i j = t + 1 := by
  cases t with
  | zero => simp only [cache]; rw [if_pos h]
  | succ t => simp only [cache]; rw [if_pos h]

variable {S}

/-- An agent transmitted at step `t` reaches every other receiver by step `t+1`. -/
theorem fresh_of_tx {h : ℕ → Fin m} (H : StrongHeads S h) {t : ℕ} {i j : Fin m} (hx : ∃ i', j ∈ S t i')
    (hji : j ≠ i) : t + 1 ≤ table S (t + 1) i j := by
  by_cases hd : j ∈ S (t + 1) i
  · rw [table_of_mem S hd]; omega
  · have hsucc : table S (t + 1) i j = max (cache S t i j) ((S (t + 1) i).sup fun k => table S t k j) := by
      simp only [table]; rw [if_neg hd]
    rw [hsucc]
    by_cases hjh : j = h (t + 1)
    · exfalso
      have hih : i ≠ h (t + 1) := fun hi => hji (hjh.trans hi.symm)
      exact hd (by rw [hjh]; exact H.head_decoded (t + 1) i hih)
    · have hc := H.covers t j hx hjh
      by_cases hih : i = h (t + 1)
      · rw [← hih] at hc
        rw [cache_of_mem S hc]
        exact le_max_left _ _
      · have hk := H.head_decoded (t + 1) i hih
        have h2 : table S t (h (t + 1)) j ≤ (S (t + 1) i).sup fun k => table S t k j :=
          Finset.le_sup (f := fun k => table S t k j) hk
        rw [table_of_mem S hc] at h2
        exact le_max_of_le_right h2

/-- **One-step freshness for every receiver, with no distinctness of heads.** -/
theorem strong_one_hop {h : ℕ → Fin m} (H : StrongHeads S h) :
    ∀ t (i j : Fin m), j ≠ i → lastTx S t j ≤ table S (t + 1) i j := by
  intro t
  induction t with
  | zero =>
      intro i j hji
      by_cases hx : ∃ i', j ∈ S 0 i'
      · obtain ⟨i', hi'⟩ := hx
        rw [lastTx_of_mem S hi']
        exact fresh_of_tx H ⟨i', hi'⟩ hji
      · simp only [lastTx]; rw [if_neg hx]; exact Nat.zero_le _
  | succ t ih =>
      intro i j hji
      by_cases hx : ∃ i', j ∈ S (t + 1) i'
      · obtain ⟨i', hi'⟩ := hx
        rw [lastTx_of_mem S hi']
        exact fresh_of_tx H ⟨i', hi'⟩ hji
      · rw [lastTx_succ_of_not S t j hx]
        by_cases hd : j ∈ S (t + 1 + 1) i
        · rw [table_of_mem S hd]
          exact (lastTx_le_succ S t j).trans (by omega)
        · obtain ⟨k, hk⟩ := H.nonempty (t + 1 + 1) i
          have hkj : j ≠ k := fun e => hd (by rw [e]; exact hk)
          exact (ih k j hkj).trans (table_ge_of_decoded S hk j)

/-- The two-sided form. -/
theorem strong_one_hop_sandwich {h : ℕ → Fin m} (H : StrongHeads S h) (t : ℕ) (i j : Fin m) (hji : j ≠ i) :
    lastTx S t j ≤ table S (t + 1) i j ∧ table S (t + 1) i j ≤ lastTx S (t + 1) j :=
  ⟨strong_one_hop H t i j hji, table_le_lastTx S (t + 1) i j⟩

/-- **Relay memory is redundant for every receiver** (the head included). -/
theorem strong_memory_redundant {h : ℕ → Fin m} (H : StrongHeads S h) (t : ℕ) (i j : Fin m) (hji : j ≠ i) :
    CIGAMF.P13.MarlRelayMemory.ptable S (t + 1) i j = table S (t + 1) i j := by
  by_cases hj : j ∈ S (t + 1) i
  · simp only [CIGAMF.P13.MarlRelayMemory.ptable, table, if_pos hj]
  · refine le_antisymm ?_ (CIGAMF.P13.MarlRelayMemory.table_le_ptable S (t + 1) i j)
    exact (CIGAMF.P13.MarlRelayMemory.ptable_succ_le S t i j hj).trans (strong_one_hop H t i j hji)

end Dynamics

section Prefix

open CIGAMF.P13.MarlPrefixThreshold (threshold)

/-- On the prefix channel at capacity `K ≥ 1`, every receiver decodes at least one sender. -/
theorem prefix_nonempty (pos : Fin m → ℕ) (K : ℕ) (hK : 1 ≤ K) (a0 a1 : Fin m) (h0 : pos a0 = 0) (h1 : pos a1 = 1) :
    ∀ i, (prefixDecoded pos (threshold pos K) i).Nonempty := by
  intro i
  by_cases hi : i = a0
  · refine ⟨a1, ?_⟩
    simp only [prefixDecoded, mem_filter, mem_univ, true_and]
    refine ⟨fun e => ?_, ?_⟩
    · rw [e, hi, h0] at h1; omega
    · rw [hi]; unfold threshold; rw [if_pos (by omega)]; omega
  · refine ⟨a0, ?_⟩
    simp only [prefixDecoded, mem_filter, mem_univ, true_and]
    refine ⟨fun e => hi e.symm, ?_⟩
    unfold threshold; split_ifs <;> omega

/-- **On the prefix channel only the covering rule for the head remains to be checked.** -/
theorem prefix_strong_heads (pos : ℕ → Fin m → ℕ) (K : ℕ) (hK : 1 ≤ K) (a0 a1 : ℕ → Fin m)
    (h0 : ∀ t, pos t (a0 t) = 0) (h1 : ∀ t, pos t (a1 t) = 1) (h : ℕ → Fin m) (hhead : ∀ t, pos t (h t) = 0)
    (hcov : ∀ t j, (∃ i, j ∈ prefixDecoded (pos t) (threshold (pos t) K) i) → j ≠ h (t + 1) →
      j ∈ prefixDecoded (pos t) (threshold (pos t) K) (h (t + 1))) :
    StrongHeads (fun t => prefixDecoded (pos t) (threshold (pos t) K)) h := by
  refine ⟨fun t i hi => ?_, hcov, fun t => prefix_nonempty (pos t) K hK (a0 t) (a1 t) (h0 t) (h1 t)⟩
  exact prefix_head_decoded (pos t) (threshold (pos t) K) (h t) (hhead t)
    (fun i => by unfold threshold; split_ifs <;> omega) i hi

/-- The strong bound on the prefix channel. -/
theorem prefix_strong_one_hop (pos : ℕ → Fin m → ℕ) (K : ℕ) (hK : 1 ≤ K) (a0 a1 : ℕ → Fin m)
    (h0 : ∀ t, pos t (a0 t) = 0) (h1 : ∀ t, pos t (a1 t) = 1) (h : ℕ → Fin m) (hhead : ∀ t, pos t (h t) = 0)
    (hcov : ∀ t j, (∃ i, j ∈ prefixDecoded (pos t) (threshold (pos t) K) i) → j ≠ h (t + 1) →
      j ∈ prefixDecoded (pos t) (threshold (pos t) K) (h (t + 1)))
    (t : ℕ) (i j : Fin m) (hji : j ≠ i) :
    lastTx (fun t => prefixDecoded (pos t) (threshold (pos t) K)) t j ≤
      table (fun t => prefixDecoded (pos t) (threshold (pos t) K)) (t + 1) i j :=
  strong_one_hop (prefix_strong_heads pos K hK a0 a1 h0 h1 h hhead hcov) t i j hji

end Prefix

section Witness


/-- The repeated-head schedule of `LeanMarlNewsRelayV1` satisfies the strong hypotheses. -/
theorem w_strong : StrongHeads CIGAMF.P13.MarlNewsRelay.wS CIGAMF.P13.MarlNewsRelay.wHead := by
  refine ⟨CIGAMF.P13.MarlNewsRelay.w_hyps.head_decoded, CIGAMF.P13.MarlNewsRelay.w_hyps.covers, fun t i => ?_⟩
  rcases t with _ | _ | t
  · revert i; decide
  · revert i; decide
  · rw [CIGAMF.P13.MarlNewsRelay.wS_ge2]; revert i; decide

theorem w_strong_one_hop (t : ℕ) (i j : Fin 4) (hji : j ≠ i) : lastTx CIGAMF.P13.MarlNewsRelay.wS t j ≤ table CIGAMF.P13.MarlNewsRelay.wS (t + 1) i j :=
  strong_one_hop w_strong t i j hji

/-- On this schedule `CoveringHeads.distinct` fails (`CIGAMF.P13.MarlNewsRelay.w_heads_repeat`), so `one_hop` does not apply, but the strong
theorem does — for every receiver, the head included. -/
theorem w_distinct_fails : ¬ (∀ t, CIGAMF.P13.MarlNewsRelay.wHead (t + 1) ≠ CIGAMF.P13.MarlNewsRelay.wHead t) := fun h => h 1 CIGAMF.P13.MarlNewsRelay.w_heads_repeat

end Witness

end CIGAMF.P13.MarlStrongOneHop

#print axioms CIGAMF.P13.MarlStrongOneHop.fresh_of_tx
#print axioms CIGAMF.P13.MarlStrongOneHop.strong_one_hop
#print axioms CIGAMF.P13.MarlStrongOneHop.strong_one_hop_sandwich
#print axioms CIGAMF.P13.MarlStrongOneHop.strong_memory_redundant
#print axioms CIGAMF.P13.MarlStrongOneHop.prefix_nonempty
#print axioms CIGAMF.P13.MarlStrongOneHop.prefix_strong_heads
#print axioms CIGAMF.P13.MarlStrongOneHop.prefix_strong_one_hop
#print axioms CIGAMF.P13.MarlStrongOneHop.w_strong
#print axioms CIGAMF.P13.MarlStrongOneHop.w_strong_one_hop
#print axioms CIGAMF.P13.MarlStrongOneHop.w_distinct_fails
