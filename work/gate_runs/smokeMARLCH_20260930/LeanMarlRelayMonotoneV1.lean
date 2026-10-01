import Mathlib
import LeanMarlRelayOneHopV1

/-!
# Freshness is monotone in the decoded sets (hence in capacity, for a fixed order sequence)

The relay merge of `LeanMarlRelayOneHopV1` is monotone: decoding more packets at every step can only make every
receiver's copies fresher.  With a FIXED sequence of committed orders, a larger capacity gives a larger threshold and
hence (threshold form) a larger decoded set, so freshness is monotone in capacity.

## WHAT IS PROVED
* `lastTx_mono_sets`, `cache_mono_sets`, `table_mono_sets` — pointwise larger decoded sets at every step give pointwise
  later (encoded) transmission times, direct copies and relay tables.
* `prefix_mono` — in threshold form, larger thresholds give larger decoded sets.
* `freshness_mono_capacity` — for a fixed order sequence, larger thresholds at every step give fresher tables.

## WHAT THIS DOES NOT ESTABLISH
- Monotonicity of any policy's return in capacity (paper_marl_v2 V-S: measured waiting is not always monotone).
- Anything for an ADAPTIVE order, whose order depends on past capacities.
-/

namespace CIGAMF.P13.MarlRelayMonotone

open Finset
open CIGAMF.P13.MarlRelayOneHop

variable {m : ℕ} (S S' : ℕ → Fin m → Finset (Fin m))

theorem lastTx_mono_sets (h : ∀ t i, S t i ⊆ S' t i) : ∀ t j, lastTx S t j ≤ lastTx S' t j := by
  intro t
  induction t with
  | zero =>
      intro j
      simp only [lastTx]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (let ⟨i, hi⟩ := h1; ⟨i, h 0 i hi⟩) h2
      · exact Nat.zero_le _
      · exact le_rfl
  | succ t ih =>
      intro j
      simp only [lastTx]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (let ⟨i, hi⟩ := h1; ⟨i, h (t + 1) i hi⟩) h2
      · exact (lastTx_le_succ S t j).trans (by omega)
      · exact ih j

theorem cache_mono_sets (h : ∀ t i, S t i ⊆ S' t i) : ∀ t i j, cache S t i j ≤ cache S' t i j := by
  intro t
  induction t with
  | zero =>
      intro i j
      simp only [cache]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h 0 i h1) h2
      · exact Nat.zero_le _
      · exact le_rfl
  | succ t ih =>
      intro i j
      simp only [cache]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h (t + 1) i h1) h2
      · exact (cache_le_lastTx S t i j).trans ((lastTx_le_succ S t j).trans (by omega))
      · exact ih i j

theorem table_mono_sets (h : ∀ t i, S t i ⊆ S' t i) : ∀ t i j, table S t i j ≤ table S' t i j := by
  intro t
  induction t with
  | zero =>
      intro i j
      simp only [table]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h 0 i h1) h2
      · exact Nat.zero_le _
      · exact le_rfl
  | succ t ih =>
      intro i j
      simp only [table]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd (h (t + 1) i h1) h2
      · have hmax : max (cache S t i j) ((S (t + 1) i).sup fun k => table S t k j) ≤ lastTx S (t + 1) j := by
          have := table_le_lastTx S (t + 1) i j
          simp only [table, if_neg h1] at this
          exact this
        exact le_trans hmax (by have := lastTx_le_succ S (t + 1) j; omega)
      · refine max_le_max (cache_mono_sets S S' h t i j) ?_
        refine Finset.sup_le fun k hk => ?_
        exact (ih k j).trans (Finset.le_sup (f := fun k => table S' t k j) (h (t + 1) i hk))

theorem prefix_mono (pos r r' : Fin m → ℕ) (h : ∀ i, r i ≤ r' i) :
    ∀ i, prefixDecoded pos r i ⊆ prefixDecoded pos r' i := by
  intro i j hj
  simp only [prefixDecoded, mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2 (h i)⟩

/-- **Freshness is monotone in capacity for a fixed order sequence.** -/
theorem freshness_mono_capacity (pos : ℕ → Fin m → ℕ) (r r' : ℕ → Fin m → ℕ) (h : ∀ t i, r t i ≤ r' t i) :
    ∀ t i j, table (fun t => prefixDecoded (pos t) (r t)) t i j ≤ table (fun t => prefixDecoded (pos t) (r' t)) t i j :=
  table_mono_sets _ _ fun t => prefix_mono (pos t) (r t) (r' t) (h t)

end CIGAMF.P13.MarlRelayMonotone

#print axioms CIGAMF.P13.MarlRelayMonotone.lastTx_mono_sets
#print axioms CIGAMF.P13.MarlRelayMonotone.cache_mono_sets
#print axioms CIGAMF.P13.MarlRelayMonotone.table_mono_sets
#print axioms CIGAMF.P13.MarlRelayMonotone.prefix_mono
#print axioms CIGAMF.P13.MarlRelayMonotone.freshness_mono_capacity
