import Mathlib

/-!
# Legacy-view decoder: each node rebuilds the frozen receiver's K1 view from base packets and its own state

E9b / E9c of PROTOCOL_E3_WAVE_ALL_PENDING_20261003 (04/10/2026 00:5x EDT; review HISTORY_FRAMING_REVIEW_20261004 item 2).
The object is the VIEW the legacy (K1) protocol would build from the same physical history — receiver `i`'s cache of
direct copies and its merged relay table — not a sequence model: the E3 actor is feed-forward on that view.

## The model (transcribes `models/marl_relay_v2.merge_views` under `models/marl_relay_v3.make_slot_merge`)
* `Pub` — the PUBLIC protocol: the legacy schedule `S t i` (the senders receiver `i` decodes at step `t`; in E3 the
  age-first const-1 order, a function of time only), the relay slots `slots k` and the candidate order `ord`.
* `x t j` — sender `j`'s fresh summary at step `t`: ANY physical trajectory (so it covers the mixed fleet, whose NEW
  agents change the traffic; the guarantee is about the same trajectory, not about returns).
* `merge` — the merge rule: nothing about oneself; a direct copy for a decoded sender; otherwise the freshest of the own
  cache copy and the slot-restricted previous tables of the decoded senders, compared strictly (first candidate wins
  ties: `e.measured_at > best[j].measured_at`).  Tables are rebuilt every step (no persistent relay memory: eviction).
* `ref` — the reference K1 run (the simulator's legacy semantics), starting from empty caches and tables.
* `nodeStep` — ONE node's update.  Its arguments are the public protocol, the step, the node's own local state and the
  base packets it received; it cannot read `x` or another node's state (the type is the locality guarantee).  It decodes
  exactly the received base packets of its public schedule.
* `bundle` — the channel: the base packets physically delivered to `i` at `t` (senders in `D t i`), each carrying the
  sender's fresh entry and its slot-restricted table passed through a wire encoder `enc t` (identity = full precision;
  `wire c` = an age field saturated at `c` steps).
* `dec` — every node running `nodeStep` on what the channel delivers.

## WHAT IS PROVED
* `decoded_eq_sched` — under nesting (`S t i ⊆ D t i`) every node decodes exactly its legacy schedule (the E9 cost:
  `|S t i|` base packets per node per step, OLD and NEW nodes alike).
* `dec_eq_ref_upto` — under nesting, if the wire encoder is exact on entries younger than the step for every step
  `t < T`, then for every `t ≤ T` and every node, the decoder's cache and table EQUAL the reference K1 cache and view.
  Proof by induction (a refinement-mapping argument): initialization, cache update, slot restriction and the merge are
  all covered by the definitions.
* `dec_eq_ref` (full precision, every step) and `dec_wire_eq_ref` (age field saturated at `c`: exact for `t ≤ c + 1`;
  the 25 B packet with 5-bit ages, `c = 31`, covers the 26-step E3 episodes; the 4-bit field, `c = 14`, does not).
* `same_action` — any receiver input built from the step and the view (e.g. ages saturated at 14 steps) and any policy
  then give the same input and action on the decoder view as on the reference view.
* `ref_meas_lt`, `ref_honest` — invariants of the reference: every entry was measured before the step and carries the
  summary its sender measured then.  `freshest_perm` + `ref_merge_perm` — with honest entries, the merge does not depend
  on the order in which candidates are enumerated (TIE-BREAKING is immaterial).
* `miss_breaks` — the nesting hypothesis is not vacuous: one undelivered scheduled packet at step 0 already gives a
  decoder view without that sender while the reference view has its fresh summary.
* `saturation_can_flip` — the age bound is not vacuous: with a saturated age field the merge can keep a STALER relayed
  copy over a fresher own-cache copy.

## WHAT THIS DOES NOT ESTABLISH
- That the Python code implements this model: the per-step replay (packets, cache, view, input, action) is the evidence
  for that (scripts/MARL_e3_legacy_decoder_eval.py, scripts/MARL_e3_legacy_decoder_nodes_eval.py).
- Anything about returns.  In a mixed fleet the NEW agents change the trajectory `x`; the theorem gives the OLD
  receivers their K1 view of THAT trajectory, not the K1 fleet's trajectory or its return.
- That reproducing the whole view is necessary: equal views are sufficient for equal actions; different views can give
  the same action.
- Anything about stochastic policies' internal state beyond a deterministic function of the view.
-/

namespace CIGAMF.P13.MarlLegacyViewDecoderV1

/-- A table entry: its measurement step and payload. -/
@[ext] structure Ent (P : Type*) where
  meas : ℕ
  pay : P

section Pick

variable {P : Type*}

/-- The merge comparison: keep the current best unless the candidate is strictly fresher. -/
def pick : Option (Ent P) → Option (Ent P) → Option (Ent P)
  | none, b => b
  | some a, none => some a
  | some a, some b => if a.meas < b.meas then some b else some a

/-- The freshest candidate, scanning left to right. -/
def freshest (l : List (Option (Ent P))) : Option (Ent P) := l.foldl pick none

theorem pick_none_iff (a b : Option (Ent P)) : pick a b = none ↔ a = none ∧ b = none := by
  rcases a with _ | a <;> rcases b with _ | b
  · simp [pick]
  · simp [pick]
  · simp [pick]
  · simp only [pick]
    split_ifs <;> simp

theorem pick_some {a b : Option (Ent P)} {r : Ent P} (h : pick a b = some r) :
    (a = some r ∨ b = some r) ∧ (∀ x, a = some x → x.meas ≤ r.meas) ∧ (∀ x, b = some x → x.meas ≤ r.meas) := by
  rcases a with _ | a <;> rcases b with _ | b
  · simp [pick] at h
  · simp only [pick] at h
    cases h
    refine ⟨Or.inr rfl, ?_, ?_⟩
    · intro x hx; cases hx
    · intro x hx; cases hx; exact le_rfl
  · simp only [pick] at h
    cases h
    refine ⟨Or.inl rfl, ?_, ?_⟩
    · intro x hx; cases hx; exact le_rfl
    · intro x hx; cases hx
  · simp only [pick] at h
    split_ifs at h with hab
    · cases h
      refine ⟨Or.inr rfl, ?_, ?_⟩
      · intro x hx; cases hx; omega
      · intro x hx; cases hx; exact le_rfl
    · cases h
      refine ⟨Or.inl rfl, ?_, ?_⟩
      · intro x hx; cases hx; exact le_rfl
      · intro x hx; cases hx; omega

theorem pick_ge_left {a b : Option (Ent P)} {x : Ent P} (ha : a = some x) :
    ∃ y, pick a b = some y ∧ x.meas ≤ y.meas := by
  subst ha
  rcases b with _ | b
  · exact ⟨x, rfl, le_rfl⟩
  · simp only [pick]
    split_ifs with h
    · exact ⟨b, rfl, le_of_lt h⟩
    · exact ⟨x, rfl, le_rfl⟩

theorem pick_ge_right {a b : Option (Ent P)} {x : Ent P} (hb : b = some x) :
    ∃ y, pick a b = some y ∧ x.meas ≤ y.meas := by
  subst hb
  rcases a with _ | a
  · exact ⟨x, rfl, le_rfl⟩
  · simp only [pick]
    split_ifs with h
    · exact ⟨x, rfl, le_rfl⟩
    · exact ⟨a, rfl, by omega⟩

theorem foldl_pick_some (l : List (Option (Ent P))) : ∀ (acc : Option (Ent P)) (r : Ent P),
    l.foldl pick acc = some r →
      (acc = some r ∨ some r ∈ l) ∧ (∀ x, acc = some x → x.meas ≤ r.meas) ∧ (∀ x, some x ∈ l → x.meas ≤ r.meas) := by
  induction l with
  | nil =>
    intro acc r h
    simp only [List.foldl_nil] at h
    subst h
    refine ⟨Or.inl rfl, ?_, ?_⟩
    · intro x hx; cases hx; exact le_rfl
    · intro x hx; simp at hx
  | cons o l ih =>
    intro acc r h
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2, h3⟩ := ih _ _ h
    refine ⟨?_, ?_, ?_⟩
    · rcases h1 with h1 | h1
      · rcases (pick_some h1).1 with p | p
        · exact Or.inl p
        · exact Or.inr (by simp [p])
      · exact Or.inr (by simp [h1])
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := pick_ge_left (b := o) hx
      exact le_trans hxy (h2 y hy)
    · intro x hx
      rcases List.mem_cons.1 hx with hx | hx
      · obtain ⟨y, hy, hxy⟩ := pick_ge_right (a := acc) hx.symm
        exact le_trans hxy (h2 y hy)
      · exact h3 x hx

/-- The freshest candidate is a candidate, and no candidate is strictly fresher. -/
theorem freshest_some {l : List (Option (Ent P))} {r : Ent P} (h : freshest l = some r) :
    some r ∈ l ∧ ∀ x, some x ∈ l → x.meas ≤ r.meas := by
  obtain ⟨h1, -, h3⟩ := foldl_pick_some l none r h
  exact ⟨h1.resolve_left (by simp), h3⟩

theorem foldl_pick_none (l : List (Option (Ent P))) :
    ∀ acc, l.foldl pick acc = none ↔ acc = none ∧ ∀ o ∈ l, o = none := by
  induction l with
  | nil => intro acc; simp
  | cons o l ih =>
    intro acc
    simp only [List.foldl_cons, ih, pick_none_iff, List.mem_cons, forall_eq_or_imp]
    tauto

theorem freshest_eq_none {l : List (Option (Ent P))} : freshest l = none ↔ ∀ o ∈ l, o = none := by
  unfold freshest
  rw [foldl_pick_none]
  simp

/-- Candidates with the same measurement step are the same entry. -/
def Coherent (l : List (Option (Ent P))) : Prop :=
  ∀ a b : Ent P, some a ∈ l → some b ∈ l → a.meas = b.meas → a = b

/-- **Tie-breaking is immaterial for coherent candidates**: any enumeration order gives the same merge. -/
theorem freshest_perm {l l' : List (Option (Ent P))} (hp : l.Perm l') (hc : Coherent l) :
    freshest l = freshest l' := by
  rcases h : freshest l with _ | r
  · have hn := (freshest_eq_none (l := l)).1 h
    symm
    exact (freshest_eq_none).2 (fun o ho => hn o (hp.mem_iff.2 ho))
  · obtain ⟨hr, hmax⟩ := freshest_some h
    rcases h' : freshest l' with _ | r'
    · have hn := (freshest_eq_none (l := l')).1 h'
      exact absurd (hn _ (hp.mem_iff.1 hr)) (by simp)
    · obtain ⟨hr', hmax'⟩ := freshest_some h'
      have e1 := hmax r' (hp.mem_iff.2 hr')
      have e2 := hmax' r (hp.mem_iff.1 hr)
      congr 1
      exact hc r r' hr (hp.mem_iff.2 hr') (le_antisymm e2 e1)

end Pick

section Protocol

variable {ι P : Type*} [DecidableEq ι]

/-- The public protocol. -/
structure Pub (ι : Type*) where
  S : ℕ → ι → Finset ι
  slots : ι → Finset ι
  ord : List ι

/-- Receiver `i`'s merged view of sender `j` at step `t`: direct set `dir`, own cache `c`, previous tables `tab`. -/
def merge (ρ : Pub ι) (x : ℕ → ι → P) (t : ℕ) (i : ι) (dir : Finset ι) (c : ι → Option (Ent P))
    (tab : ι → ι → Option (Ent P)) (j : ι) : Option (Ent P) :=
  if j = i then none
  else if j ∈ dir then some ⟨t, x t j⟩
  else freshest (c j :: (ρ.ord.filter (fun k => decide (k ∈ dir))).map
    (fun k => if j ∈ ρ.slots k then tab k j else none))

/-- The global K1 state: every receiver's cache of direct copies and its merged view (its relay table). -/
structure St (ι P : Type*) where
  cache : ι → ι → Option (Ent P)
  view : ι → ι → Option (Ent P)

/-- One reference K1 step. -/
def refStep (ρ : Pub ι) (x : ℕ → ι → P) (t : ℕ) (σ : St ι P) : St ι P where
  cache i j := if j ∈ ρ.S t i then some ⟨t, x t j⟩ else σ.cache i j
  view i := merge ρ x t i (ρ.S t i) (σ.cache i) σ.view

/-- The reference K1 run; `ref ρ x t` is the state after steps `0 … t-1`. -/
def ref (ρ : Pub ι) (x : ℕ → ι → P) : ℕ → St ι P
  | 0 => ⟨fun _ _ => none, fun _ _ => none⟩
  | t + 1 => refStep ρ x t (ref ρ x t)

/-- One node's local legacy state. -/
structure Loc (ι P : Type*) where
  cache : ι → Option (Ent P)
  table : ι → Option (Ent P)

/-- A base packet: the sender's fresh entry and its (encoded, slot-restricted) table. -/
abbrev Base (ι P : Type*) := Ent P × (ι → Option (Ent P))

/-- **One node's update.**  Only the public protocol, the step, the node's own state `L` and the base packets `b` it
received enter; it decodes the received packets of its public schedule and merges with the unchanged rule. -/
def nodeStep (ρ : Pub ι) (t : ℕ) (i : ι) (L : Loc ι P) (b : ι → Option (Base ι P)) : Loc ι P :=
  let dir := (ρ.S t i).filter (fun k => (b k).isSome)
  { cache := fun j => if j ∈ dir then (b j).map Prod.fst else L.cache j,
    table := fun j => if j = i then none else if j ∈ dir then (b j).map Prod.fst
      else freshest (L.cache j :: (ρ.ord.filter (fun k => decide (k ∈ dir))).map
        (fun k => if j ∈ ρ.slots k then (b k).bind (fun p => p.2 j) else none)) }

/-- The channel: base packets of the senders physically delivered to `i` at `t`, tables through the wire encoder. -/
def bundle (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι) (enc : ℕ → Ent P → Ent P) (t : ℕ)
    (Ls : ι → Loc ι P) (i : ι) : ι → Option (Base ι P) :=
  fun k => if k ∈ D t i then
      some (⟨t, x t k⟩, fun j => if j ∈ ρ.slots k then ((Ls k).table j).map (enc t) else none)
    else none

/-- Every node running `nodeStep` on what the channel delivers. -/
def dec (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι) (enc : ℕ → Ent P → Ent P) : ℕ → ι → Loc ι P
  | 0 => fun _ => ⟨fun _ => none, fun _ => none⟩
  | t + 1 => fun i => nodeStep ρ t i (dec ρ x D enc t i) (bundle ρ x D enc t (dec ρ x D enc t) i)

/-- Reference invariant: every entry was measured before the current step. -/
theorem ref_meas_lt (ρ : Pub ι) (x : ℕ → ι → P) : ∀ t i j (e : Ent P),
    ((ref ρ x t).cache i j = some e → e.meas < t) ∧ ((ref ρ x t).view i j = some e → e.meas < t) := by
  intro t
  induction t with
  | zero => intro i j e; simp [ref]
  | succ t ih =>
    intro i j e
    constructor
    · intro h
      simp only [ref, refStep] at h
      by_cases hj : j ∈ ρ.S t i
      · rw [if_pos hj] at h; cases h; exact Nat.lt_succ_self t
      · rw [if_neg hj] at h; have := (ih i j e).1 h; omega
    · intro h
      simp only [ref, refStep, merge] at h
      by_cases h1 : j = i
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      by_cases h2 : j ∈ ρ.S t i
      · rw [if_pos h2] at h; cases h; exact Nat.lt_succ_self t
      rw [if_neg h2] at h
      obtain ⟨hm, -⟩ := freshest_some h
      simp only [List.mem_cons, List.mem_map] at hm
      rcases hm with hm | ⟨k, -, hk⟩
      · have := (ih i j e).1 hm.symm; omega
      · by_cases hs : j ∈ ρ.slots k
        · rw [if_pos hs] at hk; have := (ih k j e).2 hk; omega
        · rw [if_neg hs] at hk; cases hk

/-- Reference invariant: every entry about `j` carries the summary `j` measured at its measurement step. -/
theorem ref_honest (ρ : Pub ι) (x : ℕ → ι → P) : ∀ t i j (e : Ent P),
    ((ref ρ x t).cache i j = some e → e.pay = x e.meas j) ∧ ((ref ρ x t).view i j = some e → e.pay = x e.meas j) := by
  intro t
  induction t with
  | zero => intro i j e; simp [ref]
  | succ t ih =>
    intro i j e
    constructor
    · intro h
      simp only [ref, refStep] at h
      by_cases hj : j ∈ ρ.S t i
      · rw [if_pos hj] at h; cases h; rfl
      · rw [if_neg hj] at h; exact (ih i j e).1 h
    · intro h
      simp only [ref, refStep, merge] at h
      by_cases h1 : j = i
      · rw [if_pos h1] at h; cases h
      rw [if_neg h1] at h
      by_cases h2 : j ∈ ρ.S t i
      · rw [if_pos h2] at h; cases h; rfl
      rw [if_neg h2] at h
      obtain ⟨hm, -⟩ := freshest_some h
      simp only [List.mem_cons, List.mem_map] at hm
      rcases hm with hm | ⟨k, -, hk⟩
      · exact (ih i j e).1 hm.symm
      · by_cases hs : j ∈ ρ.slots k
        · rw [if_pos hs] at hk; exact (ih k j e).2 hk
        · rw [if_neg hs] at hk; cases hk

/-- Honest candidates about one sender are coherent. -/
theorem honest_coherent (x : ℕ → ι → P) (j : ι) (l : List (Option (Ent P)))
    (h : ∀ o ∈ l, ∀ e, o = some e → e.pay = x e.meas j) : Coherent l := by
  intro a b ha hb hab
  have h1 := h _ ha a rfl
  have h2 := h _ hb b rfl
  ext
  · exact hab
  · rw [h1, h2, hab]

/-- **Tie-breaking.**  On the reference state, enumerating the decoded senders in any order gives the same merge. -/
theorem ref_merge_perm (ρ : Pub ι) (x : ℕ → ι → P) (t : ℕ) (i : ι) (ord' : List ι) (hp : ord'.Perm ρ.ord) (j : ι) :
    merge { ρ with ord := ord' } x t i (ρ.S t i) ((ref ρ x t).cache i) (ref ρ x t).view j =
      merge ρ x t i (ρ.S t i) ((ref ρ x t).cache i) (ref ρ x t).view j := by
  simp only [merge]
  by_cases h1 : j = i
  · rw [if_pos h1, if_pos h1]
  rw [if_neg h1, if_neg h1]
  by_cases h2 : j ∈ ρ.S t i
  · rw [if_pos h2, if_pos h2]
  rw [if_neg h2, if_neg h2]
  apply freshest_perm (((hp.filter _).map _).cons _)
  apply honest_coherent x j
  intro o ho
  simp only [List.mem_cons, List.mem_map] at ho
  rcases ho with rfl | ⟨k, -, rfl⟩
  · exact fun e he => (ref_honest ρ x t i j e).1 he
  · intro e he
    by_cases hs : j ∈ ρ.slots k
    · rw [if_pos hs] at he; exact (ref_honest ρ x t k j e).2 he
    · rw [if_neg hs] at he; cases he

theorem map_enc {enc : ℕ → Ent P → Ent P} {t : ℕ} (h : ∀ e : Ent P, e.meas < t → enc t e = e)
    {o : Option (Ent P)} (ho : ∀ e, o = some e → e.meas < t) : o.map (enc t) = o := by
  rcases o with _ | e
  · rfl
  · show some (enc t e) = some e
    rw [h e (ho e rfl)]

/-- **Cost.**  Under nesting every node decodes exactly the base packets of its legacy schedule. -/
theorem decoded_eq_sched (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι) (enc : ℕ → Ent P → Ent P)
    (hnest : ∀ t i, ρ.S t i ⊆ D t i) (t : ℕ) (Ls : ι → Loc ι P) (i : ι) :
    (ρ.S t i).filter (fun k => (bundle ρ x D enc t Ls i k).isSome) = ρ.S t i := by
  apply Finset.filter_true_of_mem
  intro k hk
  simp [bundle, hnest t i hk]

/-- **Main theorem.**  Under nesting, if the wire encoder is exact on entries younger than the step at every step
`t < T`, every node's cache and table equal the reference K1 cache and view at every `t ≤ T`. -/
theorem dec_eq_ref_upto (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι) (enc : ℕ → Ent P → Ent P) (T : ℕ)
    (hnest : ∀ t i, ρ.S t i ⊆ D t i) (henc : ∀ t < T, ∀ e : Ent P, e.meas < t → enc t e = e) :
    ∀ t ≤ T, ∀ i, (dec ρ x D enc t i).cache = (ref ρ x t).cache i ∧ (dec ρ x D enc t i).table = (ref ρ x t).view i := by
  intro t
  induction t with
  | zero => intro _ i; exact ⟨rfl, rfl⟩
  | succ t ih =>
    intro hT i
    have hlt : t < T := by omega
    have ih' := ih (le_of_lt hlt)
    have hdir := decoded_eq_sched ρ x D enc hnest t (dec ρ x D enc t) i
    have hfr : ∀ j ∈ ρ.S t i, (bundle ρ x D enc t (dec ρ x D enc t) i j).map Prod.fst = some ⟨t, x t j⟩ := by
      intro j hj
      simp [bundle, hnest t i hj]
    have htab : ∀ k ∈ ρ.S t i, ∀ j, (bundle ρ x D enc t (dec ρ x D enc t) i k).bind (fun p => p.2 j) =
        if j ∈ ρ.slots k then (ref ρ x t).view k j else none := by
      intro k hk j
      simp only [bundle, if_pos (hnest t i hk), Option.bind_some]
      rw [(ih' k).2]
      by_cases hs : j ∈ ρ.slots k
      · rw [if_pos hs, if_pos hs]
        exact map_enc (henc t hlt) (fun e he => (ref_meas_lt ρ x t k j e).2 he)
      · rw [if_neg hs, if_neg hs]
    constructor
    · funext j
      simp only [dec, nodeStep, ref, refStep, hdir]
      by_cases hj : j ∈ ρ.S t i
      · rw [if_pos hj, if_pos hj]; exact hfr j hj
      · rw [if_neg hj, if_neg hj]; exact congrFun (ih' i).1 j
    · funext j
      simp only [dec, nodeStep, ref, refStep, merge, hdir]
      by_cases h1 : j = i
      · rw [if_pos h1, if_pos h1]
      rw [if_neg h1, if_neg h1]
      by_cases h2 : j ∈ ρ.S t i
      · rw [if_pos h2, if_pos h2]; exact hfr j h2
      rw [if_neg h2, if_neg h2, (ih' i).1]
      apply congrArg freshest
      apply congrArg (List.cons _)
      apply List.map_congr_left
      intro k hk
      have hk' : k ∈ ρ.S t i := by simpa using (List.mem_filter.1 hk).2
      rw [htab k hk' j]
      by_cases hs : j ∈ ρ.slots k
      · rw [if_pos hs, if_pos hs]
      · rw [if_neg hs, if_neg hs]

/-- Full-precision tables: the decoder equals the reference at every step. -/
theorem dec_eq_ref (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι) (hnest : ∀ t i, ρ.S t i ⊆ D t i) (t : ℕ)
    (i : ι) : (dec ρ x D (fun _ e => e) t i).cache = (ref ρ x t).cache i ∧
      (dec ρ x D (fun _ e => e) t i).table = (ref ρ x t).view i :=
  dec_eq_ref_upto ρ x D (fun _ e => e) t hnest (fun _ _ _ _ => rfl) t le_rfl i

/-- The wire age field saturated at `c` steps: sent as `min c (t - meas)`, decoded as `t - age`. -/
def wire (c t : ℕ) (e : Ent P) : Ent P := ⟨t - min c (t - e.meas), e.pay⟩

theorem wire_exact {c t : ℕ} {e : Ent P} (hm : e.meas ≤ t) (hc : t - e.meas ≤ c) : wire c t e = e := by
  obtain ⟨m, p⟩ := e
  dsimp only at hm hc
  show (⟨t - min c (t - m), p⟩ : Ent P) = ⟨m, p⟩
  rw [Nat.min_eq_right hc]
  congr 1
  omega

/-- Saturated tables: exact for every step `t ≤ c + 1` (5-bit ages, `c = 31`, cover a 26-step episode). -/
theorem dec_wire_eq_ref (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι) (c : ℕ)
    (hnest : ∀ t i, ρ.S t i ⊆ D t i) (t : ℕ) (ht : t ≤ c + 1) (i : ι) :
    (dec ρ x D (wire c) t i).cache = (ref ρ x t).cache i ∧ (dec ρ x D (wire c) t i).table = (ref ρ x t).view i :=
  dec_eq_ref_upto ρ x D (wire c) (c + 1) hnest
    (fun t' ht' e he => wire_exact (le_of_lt he) (by omega)) t ht i

/-- **Same input, same action** for any input built from the step and the view and any policy. -/
theorem same_action {X A : Type*} (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι)
    (hnest : ∀ t i, ρ.S t i ⊆ D t i) (input : ℕ → (ι → Option (Ent P)) → X) (pol : ι → X → A) (t : ℕ) (i : ι) :
    input t (dec ρ x D (fun _ e => e) t i).table = input t ((ref ρ x t).view i) ∧
      pol i (input t (dec ρ x D (fun _ e => e) t i).table) = pol i (input t ((ref ρ x t).view i)) := by
  rw [(dec_eq_ref ρ x D hnest t i).2]
  exact ⟨rfl, rfl⟩

/-- **Nesting is needed.**  One scheduled but undelivered packet at step 0: the decoder has no copy of that sender,
the reference view has its fresh summary. -/
theorem miss_breaks (ρ : Pub ι) (x : ℕ → ι → P) (D : ℕ → ι → Finset ι) (enc : ℕ → Ent P → Ent P) {i k : ι}
    (hki : k ≠ i) (hS : k ∈ ρ.S 0 i) (hD : k ∉ D 0 i) :
    (dec ρ x D enc 1 i).table k = none ∧ (ref ρ x 1).view i k = some ⟨0, x 0 k⟩ := by
  have h0 : dec ρ x D enc 0 = fun _ => ⟨fun _ => none, fun _ => none⟩ := rfl
  have hk : k ∉ (ρ.S 0 i).filter (fun k' => (bundle ρ x D enc 0 (dec ρ x D enc 0) i k').isSome) := by
    simp [bundle, hD]
  constructor
  · show (nodeStep ρ 0 i (dec ρ x D enc 0 i) (bundle ρ x D enc 0 (dec ρ x D enc 0) i)).table k = none
    simp only [nodeStep]
    rw [if_neg hki, if_neg hk]
    apply (freshest_eq_none).2
    intro o ho
    simp only [List.mem_cons, List.mem_map] at ho
    rcases ho with ho | ⟨k', -, rfl⟩
    · rw [ho, h0]
    · by_cases hs : k ∈ ρ.slots k'
      · rw [if_pos hs]
        simp only [bundle, h0]
        split_ifs <;> simp
      · rw [if_neg hs]
  · show (refStep ρ x 0 (ref ρ x 0)).view i k = some ⟨0, x 0 k⟩
    simp only [refStep, merge]
    rw [if_neg hki, if_pos hS]

end Protocol

/-- **Saturation can matter.**  Own-cache copy measured at step 3, relayed copy measured at step 2, merged at step 5:
full precision keeps the cache copy; with the age field saturated at 1 the relayed copy decodes as measured at step 4
and wins. -/
theorem saturation_can_flip :
    freshest [some (⟨3, 0⟩ : Ent ℕ), some ⟨2, 1⟩] = some ⟨3, 0⟩ ∧
      freshest [some (⟨3, 0⟩ : Ent ℕ), some (wire 1 5 ⟨2, 1⟩)] = some ⟨4, 1⟩ := by
  constructor <;> rfl

/-- The hypotheses are satisfiable with strictly more delivery than the schedule (two agents, schedule = the other
agent at even steps only, delivery = the other agent always). -/
theorem nesting_satisfiable :
    ∃ (S D : ℕ → Fin 2 → Finset (Fin 2)), (∀ t i, S t i ⊆ D t i) ∧ ∃ t i, S t i ≠ D t i :=
  ⟨fun t i => if t % 2 = 0 then {1 - i} else ∅, fun _ i => {1 - i},
    fun t i => by by_cases h : t % 2 = 0 <;> simp [h],
    ⟨1, 0, by decide⟩⟩

end CIGAMF.P13.MarlLegacyViewDecoderV1
