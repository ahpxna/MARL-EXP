import Mathlib

/-!
# Prefix broadcast with full relay: at constant capacity no scheduler keeps a receiver fresh

E3 context (ledger L-220 … L-223, 01/10/2026).  In the prefix-broadcast channel every agent sends one packet in a committed
order; at constant capacity `K` every receiver decodes the first `K` OTHER packets.  So the senders in the first `K`
positions (`P`, "public") are decoded by everybody else, the sender in position `K` (`h`, "hidden") only by the members of
`P`, and nobody decodes the rest.  With RELAY every decoded packet carries its sender's fresh state AND its sender's whole
knowledge (here the most generous version: full tables with unbounded memory).  `know sch n r` is the set of senders of
whom receiver `r` holds a measurement taken at one of the first `n` steps of a window (`sch` is the window's schedule).

## WHAT IS PROVED
* `private_pool` — the knowledge a receiver holds that no public packet has carried yet ("private") is at most ONE sender,
  and a receiver holds private knowledge only after it has itself been public.  (A private fact is created only by the
  hidden slot, which only public receivers decode, and a public receiver's packet releases everything it knew before.)
* `pub_card_le` — hence each step adds at most `K` senders to the publicly carried set: `|pub n| ≤ K n`.
* `receiver_floor` — **every receiver knows at most `K n` other senders from the last `n` steps**, for every scheduler,
  every relay content and every memory: the `(K+1)`-th decoded packet of the public receivers adds nothing to the floor.
* `forced_stale` — therefore at least `|α| − 1 − K n` other senders are known only from older steps or never: at every
  step, every receiver has at least `m − 1 − K(τ + 1)` senders of age `> τ`.  If `K (τ + 1) < m − 1` the channel FORCES
  copies older than `τ` on every receiver whatever the order (3×3, τ = 3: only K = 1; 4×4, τ = 9: only K = 1).
* `tk_window_subset`, `timed_floor`, `timed_forced_stale` — the same statements for the TIMED relay (latest measurement
  step per sender): at time `t` at most `K n` other senders have age `< n`, and at least `|α| − 1 − K n` have age `≥ n`.
* `layer_cake`, `burden_floor` — the stale burden beyond `τ` (ages capped at `D ≤ t`) of every receiver is at least
  `Σ_{τ ≤ d < D} (m − 1 − K (d + 1))` (natural subtraction), whatever the scheduler.
* `witness_attains` — the bound is attained (three agents, K = 1, one step), so the hypotheses are satisfiable and the
  constant `K` is sharp.

## WHAT THIS DOES NOT ESTABLISH
- That a learned receiver fails when its view leaves the training support; that is the empirical part (the E3 panels).
- Variable capacities: the statement is for one constant `K` (the hypothesis `(sch s).P.card ≤ K` and the decode rule).
-/

namespace CIGAMF.P13.MarlReceiverFloor

open Finset

variable {α : Type*} [DecidableEq α]

/-- One window step: `P` = the senders in the first `K` positions of the committed order (decoded by every other
receiver); `h` = the sender in position `K` (decoded only by the receivers in `P`). -/
structure Step (α : Type*) where
  P : Finset α
  h : α

/-- The senders receiver `r` decodes at a step: the public ones, plus the hidden one when `r` is itself public. -/
def dec (st : Step α) (r : α) : Finset α :=
  if r ∈ st.P then insert st.h (st.P.erase r) else st.P

/-- Window knowledge after `n` steps (full relay with memory): a decoded packet carries its sender's fresh state and the
sender's whole knowledge from the previous step. -/
def know (sch : ℕ → Step α) : ℕ → α → Finset α
  | 0, _ => ∅
  | n + 1, r => know sch n r ∪ (dec (sch n) r).biUnion (fun o => insert o (know sch n o))

/-- Senders of whom a window measurement has been carried by a PUBLIC packet. -/
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
  simp only [know, dec, if_neg hr, mem_union, mem_biUnion] at hx
  rcases hx with hx | ⟨o, ho, hxo⟩
  · exact mem_union_left _ hx
  · exact mem_union_right _ (packet_subset_pub sch ho hxo)

theorem know_succ_of_mem {n : ℕ} {r : α} (hr : r ∈ (sch n).P) :
    know sch (n + 1) r ⊆ pub sch (n + 1) ∪ insert (sch n).h (know sch n (sch n).h) := by
  intro x hx
  simp only [know, dec, if_pos hr, mem_union, mem_biUnion] at hx
  rcases hx with hx | ⟨o, ho, hxo⟩
  · exact mem_union_left _ (packet_subset_pub sch hr (mem_insert_of_mem hx))
  · rcases mem_insert.1 ho with rfl | ho'
    · exact mem_union_right _ hxo
    · exact mem_union_left _ (packet_subset_pub sch (mem_erase.1 ho').2 hxo)

/-- The private-pool invariant, as a predicate on one step. -/
def PoolInv (n : ℕ) : Prop :=
  ∀ r, (know sch n r \ pub sch n).card ≤ 1 ∧ ((know sch n r \ pub sch n).Nonempty → r ∈ pub sch n)

/-- A packet adds at most one sender that no public packet carried before. -/
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

/-- **The private pool holds at most one sender**, and only receivers that have been public hold one. -/
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

/-- **Each step adds at most `K` publicly carried senders.** -/
theorem pub_card_le (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (n : ℕ) : (pub sch n).card ≤ K * n := by
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
    calc (pub sch (n + 1)).card
        ≤ (pub sch n ∪ (sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card :=
          card_le_card h1
      _ ≤ (pub sch n).card + ((sch n).P.biUnion (fun o => insert o (know sch n o) \ pub sch n)).card :=
          card_union_le _ _
      _ ≤ K * n + K := add_le_add ihn (h2.trans (hK n))
      _ = K * (n + 1) := by ring

/-- **Receiver floor.**  After `n` window steps every receiver knows at most `K n` OTHER senders from the window —
whatever the order, the relay content and the memory. -/
theorem receiver_floor (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (n : ℕ) (i : α) :
    ((know sch n i).erase i).card ≤ K * n := by
  have hp := pub_card_le sch K hK n
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
      _ ≤ K * n := hp
  · have hsub : (know sch n i).erase i ⊆ pub sch n := by
      intro x hx
      by_contra hxp
      exact hne ⟨x, mem_sdiff.2 ⟨(mem_erase.1 hx).2, hxp⟩⟩
    exact (card_le_card hsub).trans hp

/-- **Forced staleness.**  At least `|α| − 1 − K n` other senders are known only from before the window (or never). -/
theorem forced_stale [Fintype α] (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (n : ℕ) (i : α) :
    Fintype.card α - 1 - K * n ≤ ((univ.erase i) \ know sch n i).card := by
  have h1 := receiver_floor sch K hK n i
  have hsub : univ.erase i ⊆ ((univ.erase i) \ know sch n i) ∪ (know sch n i).erase i := by
    intro x hx
    by_cases hk : x ∈ know sch n i
    · exact mem_union_right _ (mem_erase.2 ⟨(mem_erase.1 hx).1, hk⟩)
    · exact mem_union_left _ (mem_sdiff.2 ⟨hx, hk⟩)
  have h2 := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_erase_of_mem (mem_univ i), card_univ] at h2
  generalize K * n = c at h1 ⊢
  omega


/-! ## Timed relay: the floor is about AGES

`tk sch t r j` = 1 + the latest measurement step of `j` that `r` holds after `t` absolute steps (0 = never heard), for the
same decode rule and full relay with memory.  A measurement taken at step `≥ t − n` is exactly "age < n" at time `t`. -/

/-- Timed full relay with memory at absolute steps. -/
def tk (sch : ℕ → Step α) : ℕ → α → α → ℕ
  | 0, _, _ => 0
  | t + 1, r, j => max (tk sch t r j) ((dec (sch t) r).sup (fun o => if j = o then t + 1 else tk sch t o j))

/-- Nothing measured in the future is known. -/
theorem tk_le (t : ℕ) : ∀ r j, tk sch t r j ≤ t := by
  induction t with
  | zero => intro r j; simp [tk]
  | succ t ih =>
    intro r j
    simp only [tk]
    refine max_le ((ih r j).trans (Nat.le_succ t)) (Finset.sup_le fun o _ => ?_)
    split_ifs
    · exact le_rfl
    · exact (ih o j).trans (Nat.le_succ t)

/-- The window `[w, w + n)` of the schedule, re-indexed from 0. -/
def shift (sch : ℕ → Step α) (w : ℕ) : ℕ → Step α := fun k => sch (w + k)

/-- **Bridge.**  A measurement taken inside the window is in the window knowledge of the abstract recursion. -/
theorem tk_window_subset (w : ℕ) : ∀ n r j, w + 1 ≤ tk sch (w + n) r j → j ∈ know (shift sch w) n r := by
  intro n
  induction n with
  | zero =>
    intro r j h
    have := h.trans (tk_le sch w r j)
    omega
  | succ n ih =>
    intro r j h
    rw [show w + (n + 1) = (w + n) + 1 from rfl] at h
    simp only [tk] at h
    simp only [know, shift, mem_union, mem_biUnion]
    rcases le_max_iff.1 h with h1 | h1
    · exact Or.inl (ih r j h1)
    · obtain ⟨o, ho, hoj⟩ := (Finset.le_sup_iff (Nat.succ_pos w)).1 h1
      refine Or.inr ⟨o, ho, ?_⟩
      split_ifs at hoj with hjo
      · simp [hjo]
      · exact mem_insert_of_mem (ih o j hoj)

/-- **Timed receiver floor.**  After `t` steps, at most `K n` other senders are known to receiver `i` from measurements of
the last `n` steps (ages `< n`), whatever the scheduler. -/
theorem timed_floor [Fintype α] (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t n : ℕ) (hn : n ≤ t) (i : α) :
    ((univ.filter (fun j => t - n + 1 ≤ tk sch t i j)).erase i).card ≤ K * n := by
  have hw : t - n + n = t := Nat.sub_add_cancel hn
  have hsub : (univ.filter (fun j => t - n + 1 ≤ tk sch t i j)).erase i ⊆ (know (shift sch (t - n)) n i).erase i := by
    intro j hj
    rw [mem_erase, mem_filter] at hj
    refine mem_erase.2 ⟨hj.1, tk_window_subset sch (t - n) n i j ?_⟩
    rw [hw]
    exact hj.2.2
  exact (card_le_card hsub).trans (receiver_floor (shift sch (t - n)) K (fun s => hK _) n i)

/-- **Timed forced staleness.**  At least `|α| − 1 − K n` other senders have age `≥ n` (no measurement from the last `n`
steps, or never heard). -/
theorem timed_forced_stale [Fintype α] (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t n : ℕ) (hn : n ≤ t) (i : α) :
    Fintype.card α - 1 - K * n ≤ ((univ.erase i).filter (fun j => tk sch t i j ≤ t - n)).card := by
  have h1 := timed_floor sch K hK t n hn i
  have hsub : univ.erase i ⊆ ((univ.erase i).filter (fun j => tk sch t i j ≤ t - n)) ∪
      (univ.filter (fun j => t - n + 1 ≤ tk sch t i j)).erase i := by
    intro j hj
    by_cases hk : tk sch t i j ≤ t - n
    · exact mem_union_left _ (mem_filter.2 ⟨hj, hk⟩)
    · exact mem_union_right _ (mem_erase.2 ⟨(mem_erase.1 hj).1, mem_filter.2 ⟨mem_univ j, by omega⟩⟩)
  have h2 := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_erase_of_mem (mem_univ i), card_univ] at h2
  generalize K * n = c at h1 ⊢
  omega


/-- **Layer cake.**  `Σ_j (min(a_j, D) − τ) = Σ_{τ ≤ d < D} #{j : a_j > d}`. -/
theorem layer_cake {ι : Type*} (S : Finset ι) (a : ι → ℕ) (τ D : ℕ) :
    ∑ j ∈ S, (min (a j) D - τ) = ∑ d ∈ Finset.Ico τ D, (S.filter (fun j => d < a j)).card := by
  have h1 : ∀ j, min (a j) D - τ = ((Finset.Ico τ D).filter (fun d => d < a j)).card := by
    intro j
    have hset : (Finset.Ico τ D).filter (fun d => d < a j) = Finset.Ico τ (min (a j) D) := by
      ext d
      simp only [mem_filter, Finset.mem_Ico, lt_min_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h3, h2⟩
      · rintro ⟨h1, h3, h2⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    rw [hset, Nat.card_Ico]
  simp_rw [h1, Finset.card_filter]
  exact Finset.sum_comm

/-- **Burden floor.**  At time `t`, for every `D ≤ t`, the stale burden of receiver `i` beyond `τ` (ages `t − tk`, capped
at `D`) is at least `Σ_{τ ≤ d < D} (|α| − 1 − K (d + 1))`, whatever the scheduler. -/
theorem burden_floor [Fintype α] (K : ℕ) (hK : ∀ s, (sch s).P.card ≤ K) (t τ D : ℕ) (hD : D ≤ t) (i : α) :
    ∑ d ∈ Finset.Ico τ D, (Fintype.card α - 1 - K * (d + 1)) ≤
      ∑ j ∈ univ.erase i, (min (t - tk sch t i j) D - τ) := by
  rw [layer_cake]
  refine Finset.sum_le_sum fun d hd => ?_
  have hd' : d + 1 ≤ t := by
    have := (Finset.mem_Ico.1 hd).2
    omega
  refine (timed_forced_stale sch K hK t (d + 1) hd' i).trans (card_le_card ?_)
  intro j hj
  rw [mem_filter] at hj ⊢
  refine ⟨hj.1, ?_⟩
  have := tk_le sch t i j
  have := hj.2
  omega

/-- The schedule of the witness: three agents, `K = 1`, sender 0 first and sender 1 second at every step. -/
def witness : ℕ → Step (Fin 3) := fun _ => ⟨{0}, 1⟩

/-- **The bound is attained** (and its hypotheses are satisfiable): after one step receiver 2 knows exactly one other
sender, `= K · n` with `K = n = 1`. -/
theorem witness_attains :
    (∀ s, (witness s).P.card ≤ 1) ∧ ((know witness 1 (2 : Fin 3)).erase 2).card = 1 * 1 := by
  refine ⟨fun s => by simp [witness], ?_⟩
  decide

end CIGAMF.P13.MarlReceiverFloor

#print axioms CIGAMF.P13.MarlReceiverFloor.private_pool
#print axioms CIGAMF.P13.MarlReceiverFloor.receiver_floor
#print axioms CIGAMF.P13.MarlReceiverFloor.forced_stale
#print axioms CIGAMF.P13.MarlReceiverFloor.witness_attains
#print axioms CIGAMF.P13.MarlReceiverFloor.tk_window_subset
#print axioms CIGAMF.P13.MarlReceiverFloor.timed_floor
#print axioms CIGAMF.P13.MarlReceiverFloor.timed_forced_stale
#print axioms CIGAMF.P13.MarlReceiverFloor.layer_cake
#print axioms CIGAMF.P13.MarlReceiverFloor.burden_floor
