import Mathlib
import LeanMarlReceiverFloorV2

/-!
# The prefix channel with unequal, time-varying budgets satisfies the two inclusions of `ReceiverFloorV2.Step`

`LeanMarlReceiverFloorV2` proves the richest-receiver floor for an ABSTRACT step (public set `P`, hidden sender `h`, decode
sets `D r` with `r ∉ P → D r ⊆ P` and `r ∈ P → D r ⊆ insert h P`) and leaves as a paper argument that the prefix channel
with unequal budgets is such a step (its docstring, "WHAT THIS DOES NOT ESTABLISH").  This file closes that gap at the
list level (01/10/2026 21:3x EDT).

Model (the E3 decode rule): a committed order `l : List α`; receiver `r` with budget `K r` decodes the first `K r` entries
of the order other than its own, `(l.erase r).take (K r)`.  With any `Kst ≥ K r` for all receivers (e.g. the largest
budget), `P` = the first `Kst` entries, `h` = the entry in position `Kst` (a default `d` if the order is shorter).

## WHAT IS PROVED
* `take_erase_subset` — removing one entry and keeping `n` keeps only entries among the first `n + 1`.
* `take_erase_of_not_mem_take` — removing an entry that is not among the first `n` leaves the first `n` unchanged.
* `prefixStep` — the prefix decode rule IS a `ReceiverFloorV2.Step` (both inclusions proved; no `Nodup` needed).
* `prefixStep_card` — `|P| ≤ Kst`.
* `prefix_receiver_floor` — for every sequence of committed orders (every scheduler) and every budget sequence, every
  receiver knows at most `Σ_{s<n} K*(s)` other senders measured in the last `n` steps, with full relay and unbounded memory.
* `prefix_witness` — three agents, budgets 1, order `[0, 1, 2]`: receiver 2 knows exactly one sender after one step
  (the hypotheses are satisfiable and the bound is attained).

## WHAT THIS DOES NOT ESTABLISH
- That the Python decode (`models/marl_delivery_music.py`, prefix mode) is this function; that is a code-reading claim.
- Anything about learned receivers, values or returns.
-/

namespace CIGAMF.P13.MarlPrefixInstanceV1

open Finset CIGAMF.P13.MarlReceiverFloorV2

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem mem_take_mono {l : List α} {m n : ℕ} (hmn : m ≤ n) {x : α} (hx : x ∈ l.take m) : x ∈ l.take n := by
  have h : l.take m = (l.take n).take m := by rw [List.take_take, Nat.min_eq_left hmn]
  rw [h] at hx
  exact List.mem_of_mem_take hx

theorem take_erase_subset (l : List α) (r : α) (n : ℕ) : ∀ x ∈ (l.erase r).take n, x ∈ l.take (n + 1) := by
  induction l generalizing n with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
    intro x hx
    by_cases har : a = r
    · subst har
      rw [List.erase_cons_head] at hx
      rw [List.take_succ_cons]
      exact List.mem_cons_of_mem _ hx
    · have hne : ¬ (a == r) = true := by simpa using har
      rw [List.erase_cons_tail hne] at hx
      cases n with
      | zero => simp at hx
      | succ k =>
        rw [List.take_succ_cons] at hx
        rw [List.take_succ_cons]
        rcases List.mem_cons.1 hx with h | h
        · rw [h]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih k x h)

theorem take_erase_of_not_mem_take (l : List α) (r : α) (n : ℕ) (hr : r ∉ l.take n) :
    (l.erase r).take n = l.take n := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
    cases n with
    | zero => simp
    | succ k =>
      rw [List.take_succ_cons] at hr
      have har : a ≠ r := fun h => hr (h ▸ List.mem_cons_self)
      have hrt : r ∉ t.take k := fun h => hr (List.mem_cons_of_mem _ h)
      have hne : ¬ (a == r) = true := by simpa using har
      rw [List.erase_cons_tail hne, List.take_succ_cons, List.take_succ_cons, ih k hrt]

omit [DecidableEq α] in
theorem mem_take_succ {l : List α} {n : ℕ} (d : α) {x : α} (hx : x ∈ l.take (n + 1)) :
    x ∈ l.take n ∨ x = (l[n]?).getD d := by
  rw [List.take_add_one, List.mem_append] at hx
  rcases hx with h | h
  · exact Or.inl h
  · right
    cases hl : l[n]? with
    | none => rw [hl] at h; simp at h
    | some y => rw [hl] at h; simp at h; simp [h]

/-- The prefix decode rule as a `ReceiverFloorV2.Step`. -/
def prefixStep (l : List α) (K : α → ℕ) (Kst : ℕ) (hK : ∀ r, K r ≤ Kst) (d : α) : Step α where
  P := (l.take Kst).toFinset
  h := (l[Kst]?).getD d
  D := fun r => ((l.erase r).take (K r)).toFinset
  hout := by
    intro r hr x hx
    rw [List.mem_toFinset] at hr hx ⊢
    have hx' := mem_take_mono (hK r) hx
    rwa [take_erase_of_not_mem_take l r Kst hr] at hx'
  hin := by
    intro r _ x hx
    rw [List.mem_toFinset] at hx
    have h1 := take_erase_subset l r Kst x (mem_take_mono (hK r) hx)
    rcases mem_take_succ d h1 with h2 | h2
    · exact mem_insert_of_mem (List.mem_toFinset.2 h2)
    · rw [h2]; exact mem_insert_self _ _

theorem prefixStep_card (l : List α) (K : α → ℕ) (Kst : ℕ) (hK : ∀ r, K r ≤ Kst) (d : α) :
    (prefixStep l K Kst hK d).P.card ≤ Kst := by
  calc (prefixStep l K Kst hK d).P.card ≤ (l.take Kst).length := List.toFinset_card_le _
    _ ≤ Kst := by rw [List.length_take]; exact Nat.min_le_left _ _

/-- **Prefix channel, unequal time-varying budgets, every scheduler.**  `ord s` is the committed order at step `s` (any
scheduler), `Kb s r` the budget of receiver `r`, `Kst s` any bound on the budgets at `s` (e.g. the largest).  Every receiver
knows at most `Σ_{s<n} Kst s` other senders measured in the last `n` steps. -/
theorem prefix_receiver_floor (ord : ℕ → List α) (Kb : ℕ → α → ℕ) (Kst : ℕ → ℕ) (hK : ∀ s r, Kb s r ≤ Kst s) (d : α)
    (n : ℕ) (i : α) :
    ((know (fun s => prefixStep (ord s) (Kb s) (Kst s) (hK s) d) n i).erase i).card ≤ ∑ s ∈ range n, Kst s :=
  (receiver_floor _ n i).trans (sum_le_sum fun _ _ => prefixStep_card _ _ _ _ _)

/-- Witness: three agents, every budget 1, order `[0, 1, 2]` at every step. -/
def witnessSch : ℕ → Step (Fin 3) := fun _ => prefixStep [0, 1, 2] (fun _ => 1) 1 (fun _ => le_rfl) 0

theorem prefix_witness : ((know witnessSch 1 (2 : Fin 3)).erase 2).card = 1 := by
  decide

end CIGAMF.P13.MarlPrefixInstanceV1

#print axioms CIGAMF.P13.MarlPrefixInstanceV1.take_erase_subset
#print axioms CIGAMF.P13.MarlPrefixInstanceV1.take_erase_of_not_mem_take
#print axioms CIGAMF.P13.MarlPrefixInstanceV1.prefixStep_card
#print axioms CIGAMF.P13.MarlPrefixInstanceV1.prefix_receiver_floor
#print axioms CIGAMF.P13.MarlPrefixInstanceV1.prefix_witness
