import Mathlib

/-!
# Shared broadcast with UNEQUAL receiver budgets: every receiver's freshness is bounded by the richest receiver's budget

Generalises `LeanMarlReceiverFloorV1` (one constant capacity `K`) to unequal, time-varying receiver budgets
(01/10/2026 20:0x EDT, ledger L-224).  In prefix broadcast with relay, receiver `r` decodes the first `K_r(s)` packets of the
committed order other than its own.  Let `K*(s) = max_r K_r(s)`.  Then at step `s`:
* the senders in positions `< K*(s)` form the set `P` ("deep-public": every packet any weak receiver decodes is among them);
* the sender in position `K*(s)` is `h`, decoded only by receivers that sit in `P` AND have budget `K*(s)`;
* any receiver outside `P` decodes a subset of `P`; any receiver inside `P` decodes a subset of `P ∪ {h}`.
Only these two inclusions are used, so the step is abstract: a public set `P`, a hidden sender `h` and decode sets `D r`
satisfying them (`Step`).  The prefix channel with arbitrary budgets is one instance (paper), the constant-`K` channel of V1
another (`Step.ofConst`, proved here).

## WHAT IS PROVED
* `private_pool` — not-yet-public window knowledge of any receiver is at most one sender, and only for receivers that have
  been in `P`.
* `pub_card_le` — the publicly carried senders after `n` steps are at most `Σ_{s<n} |P_s|`.
* `receiver_floor` — **every receiver knows at most `Σ_{s<n} |P_s|` other senders from the last `n` steps**; with
  `|P_s| = K*(s)` this is the richest-receiver bound `Σ_s K*(s)`, for every scheduler, relay content and memory.
* `receiver_floor_const` — with `|P_s| ≤ K` for all `s`: at most `K n` (the V1 statement).
* `Step.ofConst` — the constant-capacity prefix step (V1's decode rule) satisfies the two inclusions.
* `witness_attains` — attained (three agents, one step), so the hypotheses are satisfiable.

## WHAT THIS DOES NOT ESTABLISH
- The list-level fact that prefix decoding with budgets `K_r(s)` satisfies the two inclusions with `|P| = K*(s)` is argued
  in the paper (positions `< K_r ≤ K*` for receivers outside `P`, positions `≤ K*` minus self inside `P`), not formalised.
- Anything about learned receivers.
-/

namespace CIGAMF.P13.MarlReceiverFloorV2

open Finset

variable {α : Type*} [DecidableEq α]

/-- One window step: public set `P`, hidden sender `h`, decode sets `D r` with the two inclusions. -/
structure Step (α : Type*) [DecidableEq α] where
  P : Finset α
  h : α
  D : α → Finset α
  hout : ∀ r, r ∉ P → D r ⊆ P
  hin : ∀ r, r ∈ P → D r ⊆ insert h P

/-- The constant-capacity prefix step of V1: receivers outside `P` decode `P`, receivers in `P` decode `P \ {r}` and `h`. -/
def Step.ofConst (P : Finset α) (h : α) : Step α where
  P := P
  h := h
  D := fun r => if r ∈ P then insert h (P.erase r) else P
  hout := by
    intro r hr
    simp only [if_neg hr]
    exact subset_rfl
  hin := by
    intro r hr
    simp only [if_pos hr]
    exact insert_subset_insert h (erase_subset r P)

/-- Window knowledge (full relay with memory). -/
def know (sch : ℕ → Step α) : ℕ → α → Finset α
  | 0, _ => ∅
  | n + 1, r => know sch n r ∪ ((sch n).D r).biUnion (fun o => insert o (know sch n o))

/-- Senders of whom a window measurement has been carried by a packet of `P`. -/
def pub (sch : ℕ → Step α) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => pub sch n ∪ (sch n).P.biUnion (fun o => insert o (know sch n o))

variable (sch : ℕ → Step α)

theorem pub_succ_subset (n : ℕ) : pub sch n ⊆ pub sch (n + 1) := by
  intro x hx
  simp only [pub]
  exact mem_union_left _ hx

theorem packet_subset_pub {n : ℕ} {o : α} (ho : o ∈ (sch n).P) :
    insert o (know sch n o) ⊆ pub sch (n + 1) := by
  intro x hx
  simp only [pub]
  exact mem_union_right _ (mem_biUnion.2 ⟨o, ho, hx⟩)

theorem know_succ_of_not_mem {n : ℕ} {r : α} (hr : r ∉ (sch n).P) :
    know sch (n + 1) r ⊆ know sch n r ∪ pub sch (n + 1) := by
  intro x hx
  simp only [know, mem_union, mem_biUnion] at hx
  rcases hx with hx | ⟨o, ho, hxo⟩
  · exact mem_union_left _ hx
  · exact mem_union_right _ (packet_subset_pub sch ((sch n).hout r hr ho) hxo)

theorem know_succ_of_mem {n : ℕ} {r : α} (hr : r ∈ (sch n).P) :
    know sch (n + 1) r ⊆ pub sch (n + 1) ∪ insert (sch n).h (know sch n (sch n).h) := by
  intro x hx
  simp only [know, mem_union, mem_biUnion] at hx
  rcases hx with hx | ⟨o, ho, hxo⟩
  · exact mem_union_left _ (packet_subset_pub sch hr (mem_insert_of_mem hx))
  · rcases mem_insert.1 ((sch n).hin r hr ho) with hoh | hoP
    · rw [hoh] at hxo
      exact mem_union_right _ hxo
    · exact mem_union_left _ (packet_subset_pub sch hoP hxo)

/-- The private-pool invariant. -/
def PoolInv (n : ℕ) : Prop :=
  ∀ r, (know sch n r \ pub sch n).card ≤ 1 ∧ ((know sch n r \ pub sch n).Nonempty → r ∈ pub sch n)

theorem packet_new_le_one {n : ℕ} (ih : PoolInv sch n) (o : α) :
    (insert o (know sch n o) \ pub sch n).card ≤ 1 := by
  by_cases hne : (know sch n o \ pub sch n).Nonempty
  · have ho : o ∈ pub sch n := (ih o).2 hne
    have heq : insert o (know sch n o) \ pub sch n = know sch n o \ pub sch n := by
      ext x
      simp only [mem_sdiff, mem_insert]
      constructor
      · rintro ⟨hx | hx, hp⟩
        · exact absurd (hx ▸ ho) hp
        · exact ⟨hx, hp⟩
      · rintro ⟨hx, hp⟩
        exact ⟨Or.inr hx, hp⟩
    rw [heq]
    exact (ih o).1
  · have hempty : know sch n o \ pub sch n = ∅ := not_nonempty_iff_eq_empty.1 hne
    have hsub : insert o (know sch n o) \ pub sch n ⊆ {o} := by
      intro x hx
      rw [mem_sdiff, mem_insert] at hx
      rcases hx with ⟨hx | hx, hp⟩
      · exact mem_singleton.2 hx
      · have hmem : x ∈ know sch n o \ pub sch n := mem_sdiff.2 ⟨hx, hp⟩
        rw [hempty] at hmem
        exact absurd hmem (Finset.notMem_empty x)
    exact (card_le_card hsub).trans (card_singleton o).le

theorem private_pool (n : ℕ) : PoolInv sch n := by
  induction n with
  | zero =>
    intro r
    simp [know, pub]
  | succ n ih =>
    intro r
    by_cases hr : r ∈ (sch n).P
    · have hsub : know sch (n + 1) r \ pub sch (n + 1) ⊆
          insert (sch n).h (know sch n (sch n).h) \ pub sch n := by
        intro x hx
        rw [mem_sdiff] at hx ⊢
        rcases mem_union.1 (know_succ_of_mem sch hr hx.1) with h1 | h1
        · exact absurd h1 hx.2
        · exact ⟨h1, fun hp => hx.2 (pub_succ_subset sch n hp)⟩
      exact ⟨(card_le_card hsub).trans (packet_new_le_one sch ih _),
        fun _ => packet_subset_pub sch hr (mem_insert_self _ _)⟩
    · have hsub : know sch (n + 1) r \ pub sch (n + 1) ⊆ know sch n r \ pub sch n := by
        intro x hx
        rw [mem_sdiff] at hx ⊢
        rcases mem_union.1 (know_succ_of_not_mem sch hr hx.1) with h1 | h1
        · exact ⟨h1, fun hp => hx.2 (pub_succ_subset sch n hp)⟩
        · exact absurd h1 hx.2
      refine ⟨(card_le_card hsub).trans (ih r).1, fun hne => pub_succ_subset sch n ((ih r).2 ?_)⟩
      obtain ⟨x, hx⟩ := hne
      exact ⟨x, hsub hx⟩

/-- **Public growth**: at most `|P_s|` new publicly carried senders per step. -/
theorem pub_card_le (n : ℕ) : (pub sch n).card ≤ ∑ s ∈ range n, (sch s).P.card := by
  induction n with
  | zero => simp [pub]
  | succ n ihn =>
    have hpool := private_pool sch n
    have h1 : pub sch (n + 1) ⊆
        pub sch n ∪ (sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n) := by
      intro x hx
      by_cases hp : x ∈ pub sch n
      · exact mem_union_left _ hp
      · simp only [pub, mem_union, mem_biUnion] at hx
        rcases hx with hx | ⟨o, ho, hxo⟩
        · exact absurd hx hp
        · exact mem_union_right _ (mem_biUnion.2 ⟨o, ho, mem_sdiff.2 ⟨hxo, hp⟩⟩)
    have h2 : ((sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card ≤ (sch n).P.card := by
      calc ((sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card
          ≤ ∑ o ∈ (sch n).P, (insert o (know sch n o) \ pub sch n).card := card_biUnion_le
        _ ≤ ∑ _o ∈ (sch n).P, 1 := sum_le_sum fun o _ => packet_new_le_one sch hpool o
        _ = (sch n).P.card := by simp
    rw [sum_range_succ]
    calc (pub sch (n + 1)).card
        ≤ (pub sch n ∪ (sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card :=
          card_le_card h1
      _ ≤ (pub sch n).card + ((sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card :=
          card_union_le _ _
      _ ≤ (∑ s ∈ range n, (sch s).P.card) + (sch n).P.card := add_le_add ihn h2

/-- **Richest-receiver floor.**  Every receiver knows at most `Σ_{s<n} |P_s|` other senders from the window. -/
theorem receiver_floor (n : ℕ) (i : α) :
    ((know sch n i).erase i).card ≤ ∑ s ∈ range n, (sch s).P.card := by
  have hp := pub_card_le sch n
  have hpool := private_pool sch n i
  by_cases hne : (know sch n i \ pub sch n).Nonempty
  · have hi : i ∈ pub sch n := hpool.2 hne
    have hsub : (know sch n i).erase i ⊆ (pub sch n).erase i ∪ (know sch n i \ pub sch n) := by
      intro x hx
      rw [mem_erase] at hx
      by_cases hxp : x ∈ pub sch n
      · exact mem_union_left _ (mem_erase.2 ⟨hx.1, hxp⟩)
      · exact mem_union_right _ (mem_sdiff.2 ⟨hx.2, hxp⟩)
    have hpos : 1 ≤ (pub sch n).card := card_pos.2 ⟨i, hi⟩
    calc ((know sch n i).erase i).card
        ≤ ((pub sch n).erase i ∪ (know sch n i \ pub sch n)).card := card_le_card hsub
      _ ≤ ((pub sch n).erase i).card + (know sch n i \ pub sch n).card := card_union_le _ _
      _ ≤ ((pub sch n).card - 1) + 1 := by
          rw [card_erase_of_mem hi]
          exact add_le_add le_rfl hpool.1
      _ = (pub sch n).card := Nat.sub_add_cancel hpos
      _ ≤ _ := hp
  · have hsub : (know sch n i).erase i ⊆ pub sch n := by
      intro x hx
      by_contra hxp
      exact hne ⟨x, mem_sdiff.2 ⟨(mem_erase.1 hx).2, hxp⟩⟩
    exact (card_le_card hsub).trans hp

/-- The constant-capacity corollary (V1's `receiver_floor`). -/
theorem receiver_floor_const (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (n : ℕ) (i : α) :
    ((know sch n i).erase i).card ≤ K * n := by
  refine (receiver_floor sch n i).trans ?_
  calc ∑ s ∈ range n, (sch s).P.card ≤ ∑ _s ∈ range n, K := sum_le_sum fun s _ => hK s
    _ = K * n := by rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-- Witness: three agents, the constant step with `P = {0}`, `h = 1`; receiver 2 knows exactly one sender after one step. -/
def witness : ℕ → Step (Fin 3) := fun _ => Step.ofConst {0} 1

theorem witness_attains :
    (∀ s, (witness s).P.card ≤ 1) ∧ ((know witness 1 (2 : Fin 3)).erase 2).card = 1 := by
  refine ⟨fun s => by simp [witness, Step.ofConst], ?_⟩
  decide

end CIGAMF.P13.MarlReceiverFloorV2

#print axioms CIGAMF.P13.MarlReceiverFloorV2.private_pool
#print axioms CIGAMF.P13.MarlReceiverFloorV2.pub_card_le
#print axioms CIGAMF.P13.MarlReceiverFloorV2.receiver_floor
#print axioms CIGAMF.P13.MarlReceiverFloorV2.receiver_floor_const
#print axioms CIGAMF.P13.MarlReceiverFloorV2.witness_attains
