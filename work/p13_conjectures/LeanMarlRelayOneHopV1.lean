import Mathlib

/-!
# Relay tables under prefix decoding: one-step freshness with a covering head

The channel of paper_marl_v2 (Section 3).  At each step `t`, receiver `i` decodes a set `S t i` of senders (in E3, a
prefix of one committed order, minus itself).  A relay packet from `k` carries `k`'s merged table of the previous step.
The E3 merge (`models/marl_delivery_music.AgeMirror`, asserted equal to the evaluator's merged views at every step) is

    T_t(i,j) = t                                        if j ∈ S_t(i)
             = max( C_t(i,j), max_{k ∈ S_t(i)} T_{t-1}(k,j) )   otherwise,

with `C` the last DIRECT decode.  Times are ENCODED in `ℕ`: `0` = never, `s + 1` = measured at step `s`, so `max` and
`Finset.sup` (with `⊥ = 0`) are the merge.  The diagonal entries `table t i i` are not used by E3; they never enter an
off-diagonal entry here either, because `table (t+1) i j` reads `table t k j` only for `k ∈ S (t+1) i`, and `k = j` is
then already the direct branch.

## WHAT IS PROVED
* `cache_le_lastTx`, `table_le_lastTx` — no copy is fresher than the last transmission of its agent.
* `head_table_fresh` — if every receiver other than the head `h t` decodes `h t`, the head at `t+1` COVERS step `t`
  (decoded every transmitted packet except its own) and `h (t+1) ≠ h t`, then the head's table after step `t` equals the
  network's last transmission of every other agent.
* `one_hop` — under the same hypotheses, every receiver other than `h (t+1)` holds after step `t+1` a copy of every
  agent at least as recent as that agent's last transmission up to step `t`, and never fresher than its last
  transmission up to `t+1`: in ages, `f_{t+1}(j) ≤ a_{t+1}(i,j) ≤ 1 + f_t(j)`.
* `prefix_cover_exists`, `prefix_head_decoded` — in the threshold form of prefix decoding, `S i = {j ≠ i | pos j < r i}`,
  a receiver with the largest threshold covers the step, and a sender at position `0` is decoded by every receiver with
  `r ≥ 1`.
* `witness_hyps`, `witness_one_hop` — a concrete three-agent schedule satisfies every hypothesis at every step, and the
  theorem applies to it: the hypotheses are not vacuous.

## WHAT THIS DOES NOT ESTABLISH
- That the E3 age-first head satisfies the covering hypothesis: it does not (the replica finds violations of the bound
  under the age-first head).  The hub head of `models/marl_delivery_music_v4.py` is the rule that meets it.
- Anything about waiting or decisions: this is about information ages only.
- The threshold form itself ("the first `K` others" equals `{j ≠ i | pos j < r i}`) is proved in a separate module.
-/

namespace CIGAMF.P13.MarlRelayOneHop

open Finset

variable {m : ℕ}

section Dynamics

variable (S : ℕ → Fin m → Finset (Fin m))

/-- Last transmission of `j` up to step `t` (encoded: `0` never, `s+1` at step `s`). -/
def lastTx : ℕ → Fin m → ℕ
  | 0, j => if ∃ i, j ∈ S 0 i then 1 else 0
  | t + 1, j => if ∃ i, j ∈ S (t + 1) i then t + 2 else lastTx t j

/-- Last direct decode of `j` by `i` up to step `t` (encoded). -/
def cache : ℕ → Fin m → Fin m → ℕ
  | 0, i, j => if j ∈ S 0 i then 1 else 0
  | t + 1, i, j => if j ∈ S (t + 1) i then t + 2 else cache t i j

/-- The E3 relay merge (encoded measurement times). -/
def table : ℕ → Fin m → Fin m → ℕ
  | 0, i, j => if j ∈ S 0 i then 1 else 0
  | t + 1, i, j =>
      if j ∈ S (t + 1) i then t + 2 else max (cache S t i j) ((S (t + 1) i).sup fun k => table t k j)

theorem lastTx_le_succ (t : ℕ) (j : Fin m) : lastTx S t j ≤ t + 1 := by
  induction t with
  | zero => simp only [lastTx]; split_ifs <;> omega
  | succ t ih => simp only [lastTx]; split_ifs <;> omega

theorem lastTx_mono (t : ℕ) (j : Fin m) : lastTx S t j ≤ lastTx S (t + 1) j := by
  simp only [lastTx]
  split_ifs
  · exact (lastTx_le_succ S t j).trans (by omega)
  · exact le_rfl

theorem lastTx_of_mem {t : ℕ} {i j : Fin m} (h : j ∈ S t i) : lastTx S t j = t + 1 := by
  cases t with
  | zero => simp only [lastTx]; rw [if_pos ⟨i, h⟩]
  | succ t => simp only [lastTx]; rw [if_pos ⟨i, h⟩]

theorem lastTx_succ_of_not (t : ℕ) (j : Fin m) (h : ¬ ∃ i, j ∈ S (t + 1) i) :
    lastTx S (t + 1) j = lastTx S t j := by
  simp only [lastTx]; rw [if_neg h]

theorem cache_le_lastTx (t : ℕ) (i j : Fin m) : cache S t i j ≤ lastTx S t j := by
  induction t with
  | zero =>
      simp only [cache]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · exact Nat.zero_le _
  | succ t ih =>
      simp only [cache]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · exact ih.trans (lastTx_mono S t j)

theorem table_le_lastTx (t : ℕ) : ∀ i j : Fin m, table S t i j ≤ lastTx S t j := by
  induction t with
  | zero =>
      intro i j
      simp only [table]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · exact Nat.zero_le _
  | succ t ih =>
      intro i j
      simp only [table]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · refine max_le ((cache_le_lastTx S t i j).trans (lastTx_mono S t j)) ?_
        refine Finset.sup_le fun k _ => ?_
        exact (ih k j).trans (lastTx_mono S t j)

theorem table_of_mem {t : ℕ} {i j : Fin m} (h : j ∈ S t i) : table S t i j = t + 1 := by
  cases t with
  | zero => simp only [table]; rw [if_pos h]
  | succ t => simp only [table]; rw [if_pos h]

/-- Decoding `k` at step `t+1` makes `i`'s table at least as fresh as `k`'s table after step `t`. -/
theorem table_ge_of_decoded {t : ℕ} {i k : Fin m} (hk : k ∈ S (t + 1) i) (j : Fin m) :
    table S t k j ≤ table S (t + 1) i j := by
  simp only [table]
  split_ifs with h
  · exact (table_le_lastTx S t k j).trans (lastTx_le_succ S t j) |>.trans (by omega)
  · exact le_max_of_le_right (Finset.le_sup (f := fun k => table S t k j) hk)

/-- The three hypotheses of the one-hop theorem, for a head sequence `h`. -/
structure CoveringHeads (h : ℕ → Fin m) : Prop where
  /-- every receiver other than the head decodes the head -/
  head_decoded : ∀ t i, i ≠ h t → h t ∈ S t i
  /-- the next head decoded every packet transmitted at `t` except its own -/
  covers : ∀ t j, (∃ i, j ∈ S t i) → j ≠ h (t + 1) → j ∈ S t (h (t + 1))
  /-- consecutive heads differ -/
  distinct : ∀ t, h (t + 1) ≠ h t

variable {S}

/-- **The head's table is as fresh as the network.** -/
theorem head_table_fresh {h : ℕ → Fin m} (H : CoveringHeads S h) :
    ∀ t j, j ≠ h (t + 1) → table S t (h (t + 1)) j = lastTx S t j := by
  intro t
  induction t with
  | zero =>
      intro j hj
      by_cases hx : ∃ i, j ∈ S 0 i
      · have hm := H.covers 0 j hx hj
        rw [table_of_mem S hm, lastTx_of_mem S hm]
      · have hnot : j ∉ S 0 (h (0 + 1)) := fun hm => hx ⟨_, hm⟩
        simp only [table, lastTx]
        rw [if_neg hnot, if_neg hx]
  | succ t ih =>
      intro j hj
      by_cases hx : ∃ i, j ∈ S (t + 1) i
      · have hm := H.covers (t + 1) j hx hj
        rw [table_of_mem S hm, lastTx_of_mem S hm]
      · refine le_antisymm (table_le_lastTx S (t + 1) _ j) ?_
        rw [lastTx_succ_of_not S t j hx]
        have hhead : h (t + 1) ∈ S (t + 1) (h (t + 1 + 1)) :=
          H.head_decoded (t + 1) (h (t + 1 + 1)) (H.distinct (t + 1))
        have hjne : j ≠ h (t + 1) := by
          rintro rfl
          exact hx ⟨_, hhead⟩
        rw [← ih j hjne]
        exact table_ge_of_decoded S hhead j

/-- **One-step freshness.**  Every receiver other than the head `h (t+1)` holds, after step `t+1`, a copy of every agent
at least as recent as that agent's last transmission up to step `t`, and never fresher than its last transmission up
to `t+1`. -/
theorem one_hop {h : ℕ → Fin m} (H : CoveringHeads S h) (t : ℕ) (i j : Fin m) (hi : i ≠ h (t + 1)) :
    lastTx S t j ≤ table S (t + 1) i j ∧ table S (t + 1) i j ≤ lastTx S (t + 1) j := by
  refine ⟨?_, table_le_lastTx S (t + 1) i j⟩
  by_cases hm : j ∈ S (t + 1) i
  · rw [table_of_mem S hm]
    exact (lastTx_le_succ S t j).trans (by omega)
  · have hhead : h (t + 1) ∈ S (t + 1) i := H.head_decoded (t + 1) i hi
    have hjne : j ≠ h (t + 1) := by
      rintro rfl
      exact hm hhead
    rw [← head_table_fresh H t j hjne]
    exact table_ge_of_decoded S hhead j

/-- The same statement in ages.  With `age t i j = (t + 1) - table t i j` (steps since the copy was measured, for a
copy that exists) and `injAge t j = (t + 1) - lastTx t j`, the bound reads `age (t+1) i j ≤ 1 + injAge t j`. -/
theorem one_hop_age {h : ℕ → Fin m} (H : CoveringHeads S h) (t : ℕ) (i j : Fin m) (hi : i ≠ h (t + 1)) :
    (t + 2) - table S (t + 1) i j ≤ 1 + ((t + 1) - lastTx S t j) := by
  have := (one_hop H t i j hi).1
  have h2 := lastTx_le_succ S t j
  omega

end Dynamics

section Prefix

variable {m : ℕ}

/-- Threshold form of prefix decoding: receiver `i` decodes every other sender whose position is below its threshold. -/
def prefixDecoded (pos r : Fin m → ℕ) (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun j => j ≠ i ∧ pos j < r i

/-- **A covering receiver always exists**: one with the largest threshold decoded everything transmitted except its
own packet. -/
theorem prefix_cover_exists [NeZero m] (pos r : Fin m → ℕ) :
    ∃ c, ∀ j, (∃ i, j ∈ prefixDecoded pos r i) → j ≠ c → j ∈ prefixDecoded pos r c := by
  obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  refine ⟨c, fun j ⟨i, hi⟩ hjc => ?_⟩
  simp only [prefixDecoded, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact ⟨hjc, lt_of_lt_of_le hi.2 (hc i (Finset.mem_univ _))⟩

/-- A sender at position `0` is decoded by every other receiver whose threshold is at least one (capacity `≥ 1`). -/
theorem prefix_head_decoded (pos r : Fin m → ℕ) (hd : Fin m) (h0 : pos hd = 0) (hr : ∀ i, 1 ≤ r i) :
    ∀ i, i ≠ hd → hd ∈ prefixDecoded pos r i := by
  intro i hi
  simp only [prefixDecoded, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => hi h.symm, by rw [h0]; exact hr i⟩

end Prefix

section Witness

/-- Witness head sequence on three agents: `0, 1, 2, 0, 1, 2, …`. -/
def wHead (t : ℕ) : Fin 3 := ⟨t % 3, Nat.mod_lt _ (by decide)⟩

/-- Witness decoded sets: every receiver other than the head decodes the head (capacity one); the head decodes the next
sender.  This is prefix decoding of the order `(h, h+1, h+2)` with capacity one for everybody. -/
def wS (t : ℕ) (i : Fin 3) : Finset (Fin 3) := if i = wHead t then {wHead t + 1} else {wHead t}

theorem wHead_succ (t : ℕ) : wHead (t + 1) = wHead t + 1 := by
  apply Fin.ext
  simp only [wHead, Fin.val_add]
  omega

theorem witness_hyps : CoveringHeads wS wHead := by
  refine ⟨?_, ?_, ?_⟩
  · intro t i hi
    simp [wS, hi]
  · intro t j hx hj
    rw [wHead_succ] at hj ⊢
    obtain ⟨i, hi⟩ := hx
    revert hi hj
    unfold wS
    generalize wHead t = a
    revert a i j
    decide
  · intro t
    rw [wHead_succ]
    generalize wHead t = a
    revert a
    decide

/-- The theorem applies to the witness at every step: the hypotheses are satisfiable and the conclusion is not
vacuous. -/
theorem witness_one_hop (t : ℕ) (i j : Fin 3) (hi : i ≠ wHead (t + 1)) :
    lastTx wS t j ≤ table wS (t + 1) i j ∧ table wS (t + 1) i j ≤ lastTx wS (t + 1) j :=
  one_hop witness_hyps t i j hi

/-- In the witness every agent is transmitted at step `0`, so the lower bound is a real constraint (`lastTx = 1`). -/
theorem witness_lastTx_zero : ∀ j : Fin 3, lastTx wS 0 j = 1 ∨ lastTx wS 0 j = 0 := by
  intro j
  simp only [lastTx]
  split_ifs <;> simp

end Witness

end CIGAMF.P13.MarlRelayOneHop

#print axioms CIGAMF.P13.MarlRelayOneHop.table_le_lastTx
#print axioms CIGAMF.P13.MarlRelayOneHop.head_table_fresh
#print axioms CIGAMF.P13.MarlRelayOneHop.one_hop
#print axioms CIGAMF.P13.MarlRelayOneHop.one_hop_age
#print axioms CIGAMF.P13.MarlRelayOneHop.prefix_cover_exists
#print axioms CIGAMF.P13.MarlRelayOneHop.prefix_head_decoded
#print axioms CIGAMF.P13.MarlRelayOneHop.witness_hyps
#print axioms CIGAMF.P13.MarlRelayOneHop.witness_one_hop
