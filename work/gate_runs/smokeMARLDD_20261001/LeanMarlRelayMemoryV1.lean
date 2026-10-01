import Mathlib
import LeanMarlRelayOneHopV1

/-!
# Relay memory is redundant under a covering head

The E3 relay merge (`LeanMarlRelayOneHopV1.table`) keeps a receiver's DIRECT copies and the tables of the packets it
decodes in the current step, but not the relayed copies it received earlier.  A persistent (gossip) merge also keeps
those.  This module proves that, under a covering head, the two coincide for every receiver other than the head.

## WHAT IS PROVED
* `ptable_le_lastTx` — the persistent table is never fresher than the last transmission.
* `table_le_ptable` — the persistent table is at least as fresh as the transient one (it keeps more).
* `memory_redundant` — under `CoveringHeads`, for every receiver other than the head `h (t+1)`, the persistent and the
  transient tables are EQUAL after step `t + 1`: both are `t + 2` for a directly decoded agent, and both equal the
  agent's last transmission up to step `t` otherwise.

## WHAT THIS DOES NOT ESTABLISH
- Equality under the age-first head (the replica finds differences of at most 0.02 step there, not zero).
-/

namespace CIGAMF.P13.MarlRelayMemory

open Finset
open CIGAMF.P13.MarlRelayOneHop

variable {m : ℕ} (S : ℕ → Fin m → Finset (Fin m))

/-- The persistent (gossip) merge: also keeps the receiver's own previous table. -/
def ptable : ℕ → Fin m → Fin m → ℕ
  | 0, i, j => if j ∈ S 0 i then 1 else 0
  | t + 1, i, j =>
      if j ∈ S (t + 1) i then t + 2
      else max (max (cache S t i j) (ptable t i j)) ((S (t + 1) i).sup fun k => ptable t k j)

theorem ptable_le_lastTx (t : ℕ) : ∀ i j, ptable S t i j ≤ lastTx S t j := by
  induction t with
  | zero =>
      intro i j; simp only [ptable]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · exact Nat.zero_le _
  | succ t ih =>
      intro i j; simp only [ptable]
      split_ifs with h
      · rw [lastTx_of_mem S h]
      · refine max_le (max_le ((cache_le_lastTx S t i j).trans (lastTx_mono S t j))
          ((ih i j).trans (lastTx_mono S t j))) ?_
        exact Finset.sup_le fun k _ => (ih k j).trans (lastTx_mono S t j)

theorem table_le_ptable (t : ℕ) : ∀ i j, table S t i j ≤ ptable S t i j := by
  induction t with
  | zero => intro i j; simp only [table, ptable]; exact le_rfl
  | succ t ih =>
      intro i j; simp only [table, ptable]
      split_ifs with h
      · exact le_rfl
      · refine max_le (le_max_of_le_left (le_max_left _ _)) ?_
        refine Finset.sup_le fun k hk => ?_
        exact (ih k j).trans (le_max_of_le_right (Finset.le_sup (f := fun k => ptable S t k j) hk))

/-- Off the direct branch, the persistent table holds nothing newer than the last transmission up to `t`. -/
theorem ptable_succ_le (t : ℕ) (i j : Fin m) (hj : j ∉ S (t + 1) i) : ptable S (t + 1) i j ≤ lastTx S t j := by
  simp only [ptable, if_neg hj]
  exact max_le (max_le (cache_le_lastTx S t i j) (ptable_le_lastTx S t i j))
    (Finset.sup_le fun k _ => ptable_le_lastTx S t k j)

variable {S}

/-- **Relay memory is redundant under a covering head.** -/
theorem memory_redundant {h : ℕ → Fin m} (H : CoveringHeads S h) (t : ℕ) (i j : Fin m) (hi : i ≠ h (t + 1)) :
    ptable S (t + 1) i j = table S (t + 1) i j := by
  by_cases hj : j ∈ S (t + 1) i
  · simp only [ptable, table, if_pos hj]
  · refine le_antisymm ?_ (table_le_ptable S (t + 1) i j)
    exact (ptable_succ_le S t i j hj).trans (one_hop H t i j hi).1

end CIGAMF.P13.MarlRelayMemory

#print axioms CIGAMF.P13.MarlRelayMemory.ptable_le_lastTx
#print axioms CIGAMF.P13.MarlRelayMemory.table_le_ptable
#print axioms CIGAMF.P13.MarlRelayMemory.memory_redundant
