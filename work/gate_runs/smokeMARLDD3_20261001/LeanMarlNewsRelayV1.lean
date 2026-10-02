import Mathlib
import LeanMarlRelayOneHopV1

/-!
# News relay with memory: the one-step freshness bound with packets of size O(L), for any team size

The E3 relay packet (`LeanMarlRelayOneHopV1.table`) carries the sender's table of EVERY other agent, which fits the
25 B budget only for `m ≤ 9` (`LeanMarlStatLayoutV1.relay_layout_bits`); fixed slot subsets lose the one-step bound
(`LeanMarlRelaySlotsV1.slots_sharp`).  Here a sender relays only its NEWS — the agents it decoded directly at the
previous step (with their ids) — and receivers keep memory (the freshest copy ever held):

    N_{t+1}(i,j) = t + 1                                                       if j ∈ S_{t+1}(i)
                 = max( N_t(i,j), [∃ k ∈ S_{t+1}(i), j ∈ S_t(k)] · t )            otherwise   (times encoded, `0` = never).

The packet of `k` at step `t+1` has `|S_t(k)|` entries, at most the largest threshold minus one: `O(L log m)` bits
instead of `O(m)`.

## WHAT IS PROVED
* `ntab_le_lastTx`, `ntab_mono` — no copy is fresher than the last transmission; memory never loses a copy.
* `news_one_hop` — if the head of every step is decoded by every other receiver and covers the previous step, then
  EVERY receiver (the head included) holds after step `t+1` a copy of every other agent at least as recent as that
  agent's last transmission up to step `t`, and never fresher than its last transmission up to `t+1`.  Unlike
  `LeanMarlRelayOneHopV1.one_hop` this needs NO distinctness of consecutive heads and does not exclude the head.
* `w_hyps`, `w_one_hop`, `w_heads_repeat` — a four-agent schedule (found by a search of random prefix schedules) whose
  head repeats satisfies the hypotheses at every step; the theorem applies to it.
* `memory_needed` — on the same schedule the same news packets WITHOUT memory (the receiver keeps only its own direct
  decodes, as the E3 cache) violate the lower bound: agent `1` was transmitted at step `0`, not at step `1`, and
  receiver `0` holds no copy of it after step `2`; with memory it does.

Together with `LeanMarlRelayMemoryV1.memory_redundant` (memory adds nothing when packets carry full tables): packet
content and receiver memory trade off exactly — full tables make memory redundant, news-only packets make memory
necessary, and news plus memory recovers the full-table guarantee.

## WHAT THIS DOES NOT ESTABLISH
- That the E3 student, trained on full-table relay, performs equally on news-relay inputs (an experiment).
- Byte accounting beyond the entry count: ids cost `⌈log₂ m⌉` bits per entry (4 for the 4×4 grid).
- Anything when a head does not cover (the age-first head: `LeanMarlAgeFirstBreaksOneHopV1`).
-/

namespace CIGAMF.P13.MarlNewsRelay

open Finset
open CIGAMF.P13.MarlRelayOneHop

variable {m : ℕ}

section Dynamics

variable (S : ℕ → Fin m → Finset (Fin m))

/-- The news reaching `i` at step `t+1` about `j`: a sender decoded by `i` at `t+1` decoded `j` directly at `t`
(the copy is measured at step `t`, encoded `t + 1`). -/
def newsAt (t : ℕ) (i j : Fin m) : ℕ := if ∃ k ∈ S (t + 1) i, j ∈ S t k then t + 1 else 0

/-- News relay WITH memory. -/
def ntab : ℕ → Fin m → Fin m → ℕ
  | 0, i, j => if j ∈ S 0 i then 1 else 0
  | t + 1, i, j => if j ∈ S (t + 1) i then t + 2 else max (ntab t i j) (newsAt S t i j)

/-- News relay WITHOUT memory: the receiver keeps only its own direct decodes (`LeanMarlRelayOneHopV1.cache`). -/
def ntabT : ℕ → Fin m → Fin m → ℕ
  | 0, i, j => if j ∈ S 0 i then 1 else 0
  | t + 1, i, j => if j ∈ S (t + 1) i then t + 2 else max (cache S t i j) (newsAt S t i j)

theorem newsAt_le (t : ℕ) (i j : Fin m) : newsAt S t i j ≤ lastTx S t j := by
  unfold newsAt
  split_ifs with h
  · obtain ⟨k, -, hk⟩ := h
    rw [lastTx_of_mem S hk]
  · exact Nat.zero_le _

theorem ntab_le_lastTx (t : ℕ) : ∀ i j : Fin m, ntab S t i j ≤ lastTx S t j := by
  induction t with
  | zero =>
      intro i j
      simp only [ntab]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · exact Nat.zero_le _
  | succ t ih =>
      intro i j
      simp only [ntab]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · exact max_le ((ih i j).trans (lastTx_mono S t j)) ((newsAt_le S t i j).trans (lastTx_mono S t j))

theorem ntab_of_mem {t : ℕ} {i j : Fin m} (h : j ∈ S t i) : ntab S t i j = t + 1 := by
  cases t with
  | zero => simp only [ntab]; rw [if_pos h]
  | succ t => simp only [ntab]; rw [if_pos h]

theorem ntab_mono (t : ℕ) (i j : Fin m) : ntab S t i j ≤ ntab S (t + 1) i j := by
  conv_rhs => simp only [ntab]
  split_ifs with h
  · exact (ntab_le_lastTx S t i j).trans (lastTx_le_succ S t j) |>.trans (by omega)
  · exact le_max_left _ _

/-- The hypotheses: the head is decoded by every other receiver, and the next head covers the step.  No distinctness. -/
structure NewsHeads (h : ℕ → Fin m) : Prop where
  head_decoded : ∀ t i, i ≠ h t → h t ∈ S t i
  covers : ∀ t j, (∃ i, j ∈ S t i) → j ≠ h (t + 1) → j ∈ S t (h (t + 1))

variable {S}

/-- An agent transmitted at step `t` reaches every other receiver by step `t+1`. -/
theorem fresh_of_tx {h : ℕ → Fin m} (H : NewsHeads S h) {t : ℕ} {i j : Fin m} (hx : ∃ i', j ∈ S t i') (hji : j ≠ i) :
    t + 1 ≤ ntab S (t + 1) i j := by
  by_cases hd : j ∈ S (t + 1) i
  · rw [ntab_of_mem S hd]; omega
  · have hsucc : ntab S (t + 1) i j = max (ntab S t i j) (newsAt S t i j) := by
      simp only [ntab]; rw [if_neg hd]
    rw [hsucc]
    by_cases hjh : j = h (t + 1)
    · exfalso
      have hih : i ≠ h (t + 1) := fun hi => hji (hjh.trans hi.symm)
      exact hd (by rw [hjh]; exact H.head_decoded (t + 1) i hih)
    · have hc := H.covers t j hx hjh
      by_cases hih : i = h (t + 1)
      · rw [← hih] at hc
        rw [ntab_of_mem S hc]
        exact le_max_left _ _
      · have hk := H.head_decoded (t + 1) i hih
        have : newsAt S t i j = t + 1 := by
          unfold newsAt; rw [if_pos ⟨h (t + 1), hk, hc⟩]
        rw [this]
        exact le_max_right _ _

/-- **One-step freshness with news packets and memory**, for every receiver and every other agent. -/
theorem news_one_hop {h : ℕ → Fin m} (H : NewsHeads S h) :
    ∀ t (i j : Fin m), j ≠ i → lastTx S t j ≤ ntab S (t + 1) i j ∧ ntab S (t + 1) i j ≤ lastTx S (t + 1) j := by
  intro t
  induction t with
  | zero =>
      intro i j hji
      refine ⟨?_, ntab_le_lastTx S 1 i j⟩
      by_cases hx : ∃ i', j ∈ S 0 i'
      · obtain ⟨i', hi'⟩ := hx
        rw [lastTx_of_mem S hi']
        exact fresh_of_tx H ⟨i', hi'⟩ hji
      · simp only [lastTx]; rw [if_neg hx]; exact Nat.zero_le _
  | succ t ih =>
      intro i j hji
      refine ⟨?_, ntab_le_lastTx S (t + 1 + 1) i j⟩
      by_cases hx : ∃ i', j ∈ S (t + 1) i'
      · obtain ⟨i', hi'⟩ := hx
        rw [lastTx_of_mem S hi']
        exact fresh_of_tx H ⟨i', hi'⟩ hji
      · rw [lastTx_succ_of_not S t j hx]
        exact (ih i j hji).1.trans (ntab_mono S (t + 1) i j)

end Dynamics

section Witness

/-- Decoded sets at step 0: order `(0, 3, 1, 2)`, capacities `(1, 3, 2, 3)`. -/
def wA (i : Fin 4) : Finset (Fin 4) := if i = 0 then {3} else if i = 1 then {0, 3, 2} else if i = 2 then {0, 3} else {0, 1, 2}

/-- Step 1: order `(3, 0, 2, 1)`, capacities `(2, 3, 1, 2)`. -/
def wB (i : Fin 4) : Finset (Fin 4) := if i = 0 then {3, 2} else if i = 1 then {3, 0, 2} else if i = 2 then {3} else {0, 2}

/-- Step 2 and later: order `(3, 2, 1, 0)`, capacities `(2, 2, 3, 3)`. -/
def wC (i : Fin 4) : Finset (Fin 4) := if i = 0 then {3, 2} else if i = 1 then {3, 2} else if i = 2 then {3, 1, 0} else {2, 1, 0}

def wS (t : ℕ) : Fin 4 → Finset (Fin 4) := if t = 0 then wA else if t = 1 then wB else wC

/-- Heads `0, 3, 3, 3, …`: the head repeats. -/
def wHead (t : ℕ) : Fin 4 := if t = 0 then 0 else 3

theorem wS_ge2 (t : ℕ) : wS (t + 1 + 1) = wC := by unfold wS; rw [if_neg (by omega), if_neg (by omega)]

theorem wHead_pos (t : ℕ) : wHead (t + 1) = 3 := by unfold wHead; rw [if_neg (by omega)]

theorem w_hyps : NewsHeads wS wHead := by
  refine ⟨?_, ?_⟩
  · intro t i hi
    rcases t with _ | _ | t
    · revert i; decide
    · revert i; decide
    · rw [wS_ge2]
      rw [wHead_pos] at hi ⊢
      revert i; decide
  · intro t j hx hj
    rw [wHead_pos] at hj ⊢
    rcases t with _ | _ | t
    · revert j; decide
    · revert j; decide
    · rw [wS_ge2] at hx ⊢
      revert j; decide

theorem w_one_hop (t : ℕ) (i j : Fin 4) (hji : j ≠ i) :
    lastTx wS t j ≤ ntab wS (t + 1) i j ∧ ntab wS (t + 1) i j ≤ lastTx wS (t + 1) j :=
  news_one_hop w_hyps t i j hji

/-- The heads repeat, so `LeanMarlRelayOneHopV1.CoveringHeads.distinct` fails on this schedule. -/
theorem w_heads_repeat : wHead 2 = wHead 1 := by decide

/-- **Memory is necessary for news packets.** -/
theorem memory_needed : lastTx wS 1 1 = 1 ∧ ntabT wS 2 0 1 = 0 ∧ 1 ≤ ntab wS 2 0 1 := by
  decide

end Witness

end CIGAMF.P13.MarlNewsRelay

#print axioms CIGAMF.P13.MarlNewsRelay.ntab_le_lastTx
#print axioms CIGAMF.P13.MarlNewsRelay.ntab_mono
#print axioms CIGAMF.P13.MarlNewsRelay.fresh_of_tx
#print axioms CIGAMF.P13.MarlNewsRelay.news_one_hop
#print axioms CIGAMF.P13.MarlNewsRelay.w_hyps
#print axioms CIGAMF.P13.MarlNewsRelay.w_one_hop
#print axioms CIGAMF.P13.MarlNewsRelay.w_heads_repeat
#print axioms CIGAMF.P13.MarlNewsRelay.memory_needed
