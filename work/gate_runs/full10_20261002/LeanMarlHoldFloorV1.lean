import Mathlib
import LeanMarlReceiverFloorV1

/-!
# Holding the committed order for r steps lowers the floor: the schedule-only dose (hold-r)

PROTOCOL_E3_HOLD_DOSE_20261001 and its prospective test (ledger L-228: HD1 / HD3 / HD4 supported): recomputing the age-first
order only every `r` steps (models/marl_delivery_hold.py) — same capacity, same packets, the same number of fresh senders per
step — lowers the gain of relay over compiled silence as `r` grows.  This file proves the channel half: when the step
(public set `P`, hidden sender `h`) is held for blocks of `r` steps, the publicly carried set grows by at most `K + 1` per
BLOCK instead of `K` per STEP, so every receiver knows at most `(K + 1) j` other senders after `j` blocks (`r j` steps),
whatever the relay content and memory — against `K r j` without holding.

## WHAT IS PROVED
* `pub_step_le` — any step adds at most `|P|` publicly carried senders (the step of V1's `pub_card_le`).
* `pub_second_subset`, `pub_second_card` — the SECOND step of a held step adds at most one (only the hidden sender's packet,
  decoded by the public receivers at the first step, can bring anything new).
* `pub_third_subset` — from the THIRD step of a held step on, nothing new becomes public.
* `block_growth` — within a block of a held schedule the public set grows by at most `K + 1`.
* `hold_pub_le`, `hold_floor` — after `j` blocks: `|pub| ≤ (K + 1) j` and every receiver knows at most `(K + 1) j` others.
* `hold_witness` — four agents, `K = 1`, `r = 3`, one block: the held schedule lets receiver 3 know exactly 2 = (K + 1) j
  senders, while a rotating schedule of the same capacity lets it know 3 = K r j: holding strictly lowers what can be known.

## WHAT THIS DOES NOT ESTABLISH
- The gain (the dose–response on the return is empirical, L-228); windows not aligned with the blocks (one extra block).
-/

namespace CIGAMF.P13.MarlHoldFloorV1

open Finset CIGAMF.P13.MarlReceiverFloor

variable {α : Type*} [DecidableEq α]

theorem pub_succ' (sch : ℕ → Step α) (n : ℕ) :
    pub sch (n + 1) = pub sch n ∪ (sch n).P.biUnion (fun o => insert o (know sch n o)) := rfl

theorem know_succ' (sch : ℕ → Step α) (n : ℕ) (r : α) :
    know sch (n + 1) r = know sch n r ∪ (dec (sch n) r).biUnion (fun o => insert o (know sch n o)) := rfl

theorem dec_subset (st : Step α) (r : α) : dec st r ⊆ insert st.h st.P := by
  unfold dec
  split_ifs
  · exact insert_subset_insert _ (erase_subset _ _)
  · exact subset_insert _ _

theorem pub_step_le (sch : ℕ → Step α) (n : ℕ) :
    (pub sch (n + 1)).card ≤ (pub sch n).card + (sch n).P.card := by
  have hpool := private_pool sch n
  have h1 : pub sch (n + 1) ⊆ pub sch n ∪ (sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n) := by
    intro x hx
    by_cases hp : x ∈ pub sch n
    · exact mem_union_left _ hp
    · rw [pub_succ', mem_union, mem_biUnion] at hx
      rcases hx with hx | ⟨o, ho, hxo⟩
      · exact absurd hx hp
      · exact mem_union_right _ (mem_biUnion.2 ⟨o, ho, mem_sdiff.2 ⟨hxo, hp⟩⟩)
  have h2 : ((sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card ≤ (sch n).P.card := by
    calc ((sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card
        ≤ ∑ o ∈ (sch n).P, (insert o (know sch n o) \ pub sch n).card := card_biUnion_le
      _ ≤ ∑ _o ∈ (sch n).P, 1 := sum_le_sum fun o _ => packet_new_le_one sch hpool o
      _ = (sch n).P.card := by simp
  calc (pub sch (n + 1)).card
      ≤ (pub sch n ∪ (sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card := card_le_card h1
    _ ≤ (pub sch n).card + ((sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card := card_union_le _ _
    _ ≤ (pub sch n).card + (sch n).P.card := Nat.add_le_add_left h2 _

/-- Second step of a held step: only the hidden sender's packet (seen by the public receivers) can add anything. -/
theorem pub_second_subset (sch : ℕ → Step α) (n : ℕ) (hs : sch (n + 1) = sch n) :
    pub sch (n + 1 + 1) ⊆ pub sch (n + 1) ∪ insert (sch n).h (know sch n (sch n).h) := by
  intro x hx
  by_cases hp : x ∈ pub sch (n + 1)
  · exact mem_union_left _ hp
  rw [pub_succ', mem_union, mem_biUnion] at hx
  rcases hx with hx | ⟨o, ho, hxo⟩
  · exact absurd hx hp
  rw [hs] at ho
  rcases mem_insert.1 hxo with rfl | hxk
  · exact absurd (packet_subset_pub sch ho (mem_insert_self _ _)) hp
  rw [know_succ', mem_union, mem_biUnion] at hxk
  rcases hxk with hxk | ⟨o', ho', hxo'⟩
  · exact absurd (packet_subset_pub sch ho (mem_insert_of_mem hxk)) hp
  have hdec : dec (sch n) o = insert (sch n).h ((sch n).P.erase o) := by unfold dec; rw [if_pos ho]
  rw [hdec, mem_insert] at ho'
  rcases ho' with rfl | ho'
  · exact mem_union_right _ hxo'
  · exact absurd (packet_subset_pub sch (mem_erase.1 ho').2 hxo') hp

theorem pub_second_card (sch : ℕ → Step α) (n : ℕ) (hs : sch (n + 1) = sch n) :
    (pub sch (n + 1 + 1)).card ≤ (pub sch (n + 1)).card + 1 := by
  set S := insert (sch n).h (know sch n (sch n).h)
  have h1 : pub sch (n + 1 + 1) ⊆ pub sch (n + 1) ∪ (S \ pub sch (n + 1)) := by
    intro x hx
    rcases mem_union.1 (pub_second_subset sch n hs hx) with h | h
    · exact mem_union_left _ h
    · by_cases hp : x ∈ pub sch (n + 1)
      · exact mem_union_left _ hp
      · exact mem_union_right _ (mem_sdiff.2 ⟨h, hp⟩)
  have h2 : (S \ pub sch (n + 1)).card ≤ 1 :=
    (card_le_card (sdiff_subset_sdiff (subset_refl S) (pub_succ_subset sch n))).trans
      (packet_new_le_one sch (private_pool sch n) _)
  calc (pub sch (n + 1 + 1)).card ≤ (pub sch (n + 1) ∪ (S \ pub sch (n + 1))).card := card_le_card h1
    _ ≤ (pub sch (n + 1)).card + (S \ pub sch (n + 1)).card := card_union_le _ _
    _ ≤ (pub sch (n + 1)).card + 1 := Nat.add_le_add_left h2 _

/-- From the third step of a held step on, nothing new becomes public. -/
theorem pub_third_subset (sch : ℕ → Step α) (n : ℕ) (hs0 : sch (n + 1) = sch n) (hs1 : sch (n + 1 + 1) = sch n) :
    pub sch (n + 1 + 1 + 1) ⊆ pub sch (n + 1 + 1) := by
  by_cases hP : (sch n).P = ∅
  · intro x hx
    rw [pub_succ', mem_union, mem_biUnion] at hx
    rcases hx with hx | ⟨o, ho, _⟩
    · exact hx
    · rw [hs1, hP] at ho; exact absurd ho (Finset.notMem_empty o)
  obtain ⟨o, ho⟩ := nonempty_iff_ne_empty.2 hP
  -- the hidden packet's content reached the public receivers at step n and was released at step n + 1
  have hH : insert (sch n).h (know sch n (sch n).h) ⊆ pub sch (n + 1 + 1) := by
    intro x hx
    have hx1 : x ∈ know sch (n + 1) o := by
      rw [know_succ', mem_union, mem_biUnion]
      refine Or.inr ⟨(sch n).h, ?_, hx⟩
      unfold dec; rw [if_pos ho]; exact mem_insert_self _ _
    have ho1 : o ∈ (sch (n + 1)).P := by rw [hs0]; exact ho
    exact packet_subset_pub sch ho1 (mem_insert_of_mem hx1)
  have hK : insert (sch (n + 1)).h (know sch (n + 1) (sch (n + 1)).h) ⊆ pub sch (n + 1 + 1) := by
    rw [hs0]
    intro x hx
    rcases mem_insert.1 hx with rfl | hx
    · exact hH (mem_insert_self _ _)
    rw [know_succ', mem_union, mem_biUnion] at hx
    rcases hx with hx | ⟨o', ho', hxo'⟩
    · exact hH (mem_insert_of_mem hx)
    rcases mem_insert.1 (dec_subset (sch n) _ ho') with rfl | ho'P
    · exact hH hxo'
    · exact pub_succ_subset sch (n + 1) (packet_subset_pub sch ho'P hxo')
  intro x hx
  have hs1' : sch (n + 1 + 1) = sch (n + 1) := by rw [hs1, hs0]
  rcases mem_union.1 (pub_second_subset sch (n + 1) hs1' hx) with h | h
  · exact h
  · exact hK h

/-- A schedule held for blocks of `r` steps. -/
def held (blk : ℕ → Step α) (r : ℕ) : ℕ → Step α := fun s => blk (s / r)

theorem held_at (blk : ℕ → Step α) (r : ℕ) (hr : 0 < r) (j i : ℕ) (hi : i < r) : held blk r (r * j + i) = blk j := by
  unfold held; congr 1; rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hi, add_zero]

theorem block_growth (blk : ℕ → Step α) (r : ℕ) (hr : 0 < r) (K : ℕ) (hK : ∀ s, (blk s).P.card ≤ K) (j : ℕ) :
    ∀ i, i ≤ r → (pub (held blk r) (r * j + i)).card ≤ (pub (held blk r) (r * j)).card + (K + 1) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rcases i with _ | i
    · have h := pub_step_le (held blk r) (r * j)
      rw [show held blk r (r * j) = blk j by simpa using held_at blk r hr j 0 hr] at h
      have := hK j
      simp only [add_zero, zero_add] at h ⊢
      omega
    rcases i with _ | i
    · have hs : held blk r (r * j + 1) = held blk r (r * j) := by
        rw [held_at blk r hr j 1 (by omega), show held blk r (r * j) = blk j by simpa using held_at blk r hr j 0 hr]
      have h2 := pub_second_card (held blk r) (r * j) hs
      have h1 := pub_step_le (held blk r) (r * j)
      rw [show held blk r (r * j) = blk j by simpa using held_at blk r hr j 0 hr] at h1
      have := hK j
      have e : r * j + (0 + 1 + 1) = r * j + 1 + 1 := by ring
      rw [e]; omega
    · have hs0 : held blk r (r * j + i + 1) = held blk r (r * j + i) := by
        rw [show r * j + i + 1 = r * j + (i + 1) by ring, held_at blk r hr j (i + 1) (by omega), held_at blk r hr j i (by omega)]
      have hs1 : held blk r (r * j + i + 1 + 1) = held blk r (r * j + i) := by
        rw [show r * j + i + 1 + 1 = r * j + (i + 2) by ring, held_at blk r hr j (i + 2) (by omega), held_at blk r hr j i (by omega)]
      have hsub := pub_third_subset (held blk r) (r * j + i) hs0 hs1
      have e1 : r * j + (i + 1 + 1 + 1) = r * j + i + 1 + 1 + 1 := by ring
      have e2 : r * j + (i + 1 + 1) = r * j + i + 1 + 1 := by ring
      have hprev := ih (by omega)
      rw [e2] at hprev
      rw [e1]
      exact (card_le_card hsub).trans hprev

theorem hold_pub_le (blk : ℕ → Step α) (r : ℕ) (hr : 0 < r) (K : ℕ) (hK : ∀ s, (blk s).P.card ≤ K) (j : ℕ) :
    (pub (held blk r) (r * j)).card ≤ (K + 1) * j := by
  induction j with
  | zero => simp [pub]
  | succ j ih =>
    have h := block_growth blk r hr K hK j r le_rfl
    rw [show r * j + r = r * (j + 1) by ring] at h
    calc (pub (held blk r) (r * (j + 1))).card ≤ (pub (held blk r) (r * j)).card + (K + 1) := h
      _ ≤ (K + 1) * j + (K + 1) := Nat.add_le_add_right ih _
      _ = (K + 1) * (j + 1) := by ring

theorem know_erase_le_pub (sch : ℕ → Step α) (n : ℕ) (i : α) : ((know sch n i).erase i).card ≤ (pub sch n).card := by
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
    calc ((know sch n i).erase i).card ≤ ((pub sch n).erase i ∪ (know sch n i \ pub sch n)).card := card_le_card hsub
      _ ≤ ((pub sch n).erase i).card + (know sch n i \ pub sch n).card := card_union_le _ _
      _ ≤ ((pub sch n).card - 1) + 1 := by rw [card_erase_of_mem hi]; exact add_le_add le_rfl hpool.1
      _ = (pub sch n).card := Nat.sub_add_cancel hpos
  · have hsub : (know sch n i).erase i ⊆ pub sch n := by
      intro x hx
      by_contra hxp
      exact hne ⟨x, mem_sdiff.2 ⟨(mem_erase.1 hx).2, hxp⟩⟩
    exact card_le_card hsub

/-- **Hold floor.**  After `j` held blocks every receiver knows at most `(K + 1) j` other senders from the window. -/
theorem hold_floor (blk : ℕ → Step α) (r : ℕ) (hr : 0 < r) (K : ℕ) (hK : ∀ s, (blk s).P.card ≤ K) (j : ℕ) (i : α) :
    ((know (held blk r) (r * j) i).erase i).card ≤ (K + 1) * j :=
  (know_erase_le_pub _ _ i).trans (hold_pub_le blk r hr K hK j)

/-- Witness: four agents, `K = 1`; held (`P = {0}`, `h = 1` for 3 steps) vs rotating (`P = {0}`, `{1}`, `{2}`). -/
def heldW : ℕ → Step (Fin 4) := held (fun _ => ⟨{0}, 1⟩) 3
def rotW : ℕ → Step (Fin 4) := fun s => ⟨{⟨s % 3, by omega⟩}, ⟨(s + 1) % 3, by omega⟩⟩

theorem hold_witness :
    ((know heldW 3 (3 : Fin 4)).erase 3).card = 2 ∧ ((know rotW 3 (3 : Fin 4)).erase 3).card = 3 := by
  constructor <;> decide

end CIGAMF.P13.MarlHoldFloorV1

#print axioms CIGAMF.P13.MarlHoldFloorV1.pub_second_card
#print axioms CIGAMF.P13.MarlHoldFloorV1.pub_third_subset
#print axioms CIGAMF.P13.MarlHoldFloorV1.block_growth
#print axioms CIGAMF.P13.MarlHoldFloorV1.hold_floor
#print axioms CIGAMF.P13.MarlHoldFloorV1.hold_witness
