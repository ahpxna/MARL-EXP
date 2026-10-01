import Mathlib
import LeanUnifiedObstructionOrderV1
import «LeanPaperBSafeOrderV1»

/-!
# The decision depth of a prefix broadcast

A receiver with local observation `loc : World → O` decodes a set `D` of senders, each of which
broadcasts a deterministic record `msg j : World → M`.  Its view is `view D F` (its own
observation and the decoded records).  `safe F` is the set of acceptable actions in world `F`
(for instance, actions within `ε` of the team optimum; NOT "the teacher's action").

This module instantiates the obstruction law of the corpus (`LeanUnifiedObstructionOrderV1`,
`LeanPaperBSafeOrderV1`) at the prefix-broadcast channel of paper_marl_v2.

## WHAT IS PROVED

* `decode_safe_iff` — **the hitting law.**  Some policy on the view of `D` is acceptable in every
  world iff every obstruction the receiver's own observation cannot split (`LocalObstruction`) is
  split by a decoded sender.  Choosing the decode set is a hitting-set problem over the family
  `{senders that split H : H a local obstruction}`.
* `prefix_safe_iff`, `prefix_safe_mono` — on a prefix broadcast (decode the senders of position
  `< K`), capacity `K` suffices iff every local obstruction has a splitting sender at position
  `< K`; sufficiency is monotone in `K`.
* `prefix_safe_iff_safeAt` — **the same law as paper B's safe order.**  With
  `sepPos F G` = `0` if the receiver's own observation already separates `F, G`, else one plus the
  position of the earliest sender splitting them (`T` if none), capacity `K < T` suffices iff
  `SafeAt sepPos safe K` of `LeanPaperBSafeOrderV1`.  So the least sufficient capacity — the
  receiver's DECISION DEPTH — is paper B's `s* = max over obstructions of min over pairs of sep`.
* `nesting_price` / `nesting_price_individual` — **one order cannot serve every capacity**: two
  receivers of capacities `1` and `2`, three senders; each receiver alone is served by a decode set
  of its own size, but no nested pair `D₁ ⊆ D₂` with `|D₂| ≤ 2` serves both.
* `relay_closes_nesting` — with one relayed packet (the head forwards the records it decoded one
  hop earlier), the nested pair `{0} ⊆ {0,1}` serves both receivers.
* `hitting_embeds_decode` — every hitting-set instance is a single-receiver decode-set instance
  with the same feasible sets, so the least sufficient capacity is NP-hard to compute in general
  (Karp 1972; cited, not formalised).
* `decide_one_sender`, `identify_needs_all_but_one` — **acting is not identifying**: on the
  "answer any world but the true one" geometry with indicator records, one decoded sender
  suffices to act, while identification fails whenever two senders are left undecoded, i.e. it
  needs `m − 1` of the `m` senders.

## WHAT THIS DOES NOT ESTABLISH

- Records are deterministic and noiseless.  The noisy version is paper B's obstruction rate law
  (`LeanPaperBObstructionLawV1.obstruction_lower`), with the decoded sender as the query; it is
  not re-instantiated here.
- `safe` is a model input.  Nothing here says the E3 teacher's action, or a learned critic's
  `ε`-set, is the acceptable set; estimating it from data is a labelled diagnostic.
- Worlds are static within a decision epoch; the relay statement uses one forwarded packet of a
  static world (`relay_closes_nesting`), not the dynamic freshness model of
  `LeanMarlNewsRelayV1`.
-/

namespace CIGAMF.P13.MarlDecisionDepth

open Finset
open CIGAMF.P13.UnifiedObstructionOrder

/-! ## 1. The view of a decode set, and the hitting law -/

section View

variable {World Act J O M : Type*}
  [Fintype World] [DecidableEq World] [Fintype Act] [DecidableEq Act]
  [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O] [Fintype M] [DecidableEq M]

variable (safe : World → Finset Act) (loc : World → O) (msg : J → World → M)

/-- What a receiver sees after decoding the senders in `D`. -/
def view (D : Finset J) (F : World) : O × (J → Option M) :=
  (loc F, fun j => if j ∈ D then some (msg j F) else none)

/-- An obstruction the receiver's own observation cannot split. -/
def LocalObstruction (H : Finset World) : Prop :=
  IsObstruction safe H ∧ ∀ F ∈ H, ∀ G ∈ H, loc F = loc G

/-- Some decoded sender's record differs on two worlds of `H`. -/
def Splits (D : Finset J) (H : Finset World) : Prop :=
  ∃ j ∈ D, ∃ F ∈ H, ∃ G ∈ H, msg j F ≠ msg j G

theorem view_eq_iff (D : Finset J) (F G : World) :
    view loc msg D F = view loc msg D G ↔ loc F = loc G ∧ ∀ j ∈ D, msg j F = msg j G := by
  constructor
  · intro h
    simp only [view, Prod.mk.injEq] at h
    refine ⟨h.1, fun j hj => ?_⟩
    have := congrFun h.2 j
    simpa [hj] using this
  · rintro ⟨h1, h2⟩
    simp only [view, Prod.mk.injEq]
    refine ⟨h1, funext fun j => ?_⟩
    by_cases hj : j ∈ D
    · simp [hj, h2 j hj]
    · simp [hj]

/-- An obstruction is non-empty as soon as some action exists. -/
theorem obstruction_nonempty [Nonempty Act] {H : Finset World} (hH : IsObstruction safe H) :
    H.Nonempty := by
  by_contra he
  rw [Finset.not_nonempty_iff_eq_empty] at he
  apply hH
  obtain ⟨a⟩ := ‹Nonempty Act›
  exact ⟨a, fun F hF => by simp [he] at hF⟩

/-- **The hitting law.**  A policy on the decoded view is acceptable everywhere iff every local
obstruction is split by a decoded sender. -/
theorem decode_safe_iff [Nonempty Act] (D : Finset J) :
    (∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg D F) ∈ safe F)
      ↔ ∀ H : Finset World, LocalObstruction safe loc H → Splits msg D H := by
  constructor
  · rintro ⟨pol, hpol⟩ H ⟨hobs, hloc⟩
    by_contra hns
    obtain ⟨F0, hF0⟩ := obstruction_nonempty safe hobs
    apply hobs
    refine ⟨pol (view loc msg D F0), fun F hF => ?_⟩
    have hv : view loc msg D F = view loc msg D F0 := by
      rw [view_eq_iff]
      refine ⟨hloc F hF F0 hF0, fun j hj => ?_⟩
      by_contra hne
      exact hns ⟨j, hj, F, hF, F0, hF0, hne⟩
    rw [← hv]
    exact hpol F
  · intro hsplit
    have hcls := (classes_resolve_iff safe (view loc msg D)).2 (by
      rintro H hH ⟨k, hk⟩
      have hsame : ∀ F ∈ H, view loc msg D F = k := by
        intro F hF
        simpa using hk hF
      have hloc : ∀ F ∈ H, ∀ G ∈ H, loc F = loc G := by
        intro F hF G hG
        exact ((view_eq_iff loc msg D F G).1 ((hsame F hF).trans (hsame G hG).symm)).1
      obtain ⟨j, hj, F, hF, G, hG, hne⟩ := hsplit H ⟨hH, hloc⟩
      exact hne (((view_eq_iff loc msg D F G).1
        ((hsame F hF).trans (hsame G hG).symm)).2 j hj))
    choose pol hpol using hcls
    exact ⟨pol, fun F => hpol (view loc msg D F) F (by simp)⟩

/-- Decoding more senders never hurts. -/
theorem splits_mono {D D' : Finset J} (hDD : D ⊆ D') {H : Finset World}
    (h : Splits msg D H) : Splits msg D' H := by
  obtain ⟨j, hj, rest⟩ := h
  exact ⟨j, hDD hj, rest⟩

theorem decode_safe_mono [Nonempty Act] {D D' : Finset J} (hDD : D ⊆ D')
    (h : ∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg D F) ∈ safe F) :
    ∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg D' F) ∈ safe F := by
  rw [decode_safe_iff] at h ⊢
  exact fun H hH => splits_mono msg hDD (h H hH)

/-! ## 2. The prefix broadcast: capacity and decision depth -/

/-- The senders a receiver of capacity `K` decodes on a broadcast with positions `pos`. -/
def prefixD (pos : J → ℕ) (K : ℕ) : Finset J := univ.filter (fun j => pos j < K)

theorem prefix_safe_iff [Nonempty Act] (pos : J → ℕ) (K : ℕ) :
    (∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg (prefixD pos K) F) ∈ safe F)
      ↔ ∀ H : Finset World, LocalObstruction safe loc H →
          ∃ j, pos j < K ∧ ∃ F ∈ H, ∃ G ∈ H, msg j F ≠ msg j G := by
  rw [decode_safe_iff]
  constructor
  · intro h H hH
    obtain ⟨j, hj, rest⟩ := h H hH
    exact ⟨j, by simpa [prefixD] using hj, rest⟩
  · intro h H hH
    obtain ⟨j, hj, rest⟩ := h H hH
    exact ⟨j, by simpa [prefixD] using hj, rest⟩

theorem prefixD_mono (pos : J → ℕ) {K K' : ℕ} (hK : K ≤ K') : prefixD pos K ⊆ prefixD pos K' := by
  intro j hj
  simp only [prefixD, mem_filter, mem_univ, true_and] at hj ⊢
  omega

theorem prefix_safe_mono [Nonempty Act] (pos : J → ℕ) {K K' : ℕ} (hK : K ≤ K')
    (h : ∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg (prefixD pos K) F) ∈ safe F) :
    ∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg (prefixD pos K') F) ∈ safe F :=
  decode_safe_mono safe loc msg (prefixD_mono pos hK) h

/-- The separation order of the prefix broadcast: `0` if the receiver's own observation already
tells `F` and `G` apart, otherwise one plus the earliest position of a sender whose records differ,
and `T` ("never") when no sender's record differs. -/
noncomputable def sepPos (pos : J → ℕ) (T : ℕ) (F G : World) : ℕ :=
  if loc F ≠ loc G then 0
  else if h : (univ.filter (fun j => msg j F ≠ msg j G)).Nonempty then
    (univ.filter (fun j => msg j F ≠ msg j G)).inf' h (fun j => pos j + 1)
  else T

theorem unsafe_iff_obstruction (H : Finset World) :
    CIGAMF.P13.PaperBSafe.Unsafe safe H ↔ IsObstruction safe H := by
  unfold CIGAMF.P13.PaperBSafe.Unsafe IsObstruction HasCommon
  push_neg
  rfl

/-- **The decision depth is paper B's safe order.**  For every capacity below the "never" value
`T`, the prefix of length `K` suffices iff `SafeAt sepPos safe K`. -/
theorem prefix_safe_iff_safeAt [Nonempty Act] (pos : J → ℕ) (T K : ℕ) (hKT : K < T) :
    (∃ pol : O × (J → Option M) → Act, ∀ F, pol (view loc msg (prefixD pos K) F) ∈ safe F)
      ↔ CIGAMF.P13.PaperBSafe.SafeAt (sepPos loc msg pos T) safe K := by
  rw [prefix_safe_iff, CIGAMF.P13.PaperBSafe.safeAt_iff]
  constructor
  · intro h H hH
    rw [unsafe_iff_obstruction] at hH
    by_cases hloc : ∀ F ∈ H, ∀ G ∈ H, loc F = loc G
    · obtain ⟨j, hj, F, hF, G, hG, hne⟩ := h H ⟨hH, hloc⟩
      have hFG : F ≠ G := by rintro rfl; exact hne rfl
      refine ⟨F, hF, G, hG, hFG, ?_⟩
      unfold sepPos
      rw [if_neg (not_not.mpr (hloc F hF G hG))]
      have hmem : j ∈ univ.filter (fun j => msg j F ≠ msg j G) := by simpa using hne
      rw [dif_pos ⟨j, hmem⟩]
      exact (Finset.inf'_le _ hmem).trans (by omega)
    · push_neg at hloc
      obtain ⟨F, hF, G, hG, hne⟩ := hloc
      have hFG : F ≠ G := by rintro rfl; exact hne rfl
      refine ⟨F, hF, G, hG, hFG, ?_⟩
      unfold sepPos
      rw [if_pos hne]
      omega
  · intro h H ⟨hH, hloc⟩
    obtain ⟨F, hF, G, hG, _, hle⟩ := h H ((unsafe_iff_obstruction safe H).2 hH)
    unfold sepPos at hle
    rw [if_neg (not_not.mpr (hloc F hF G hG))] at hle
    by_cases hs : (univ.filter (fun j => msg j F ≠ msg j G)).Nonempty
    · rw [dif_pos hs] at hle
      obtain ⟨j, hj, hje⟩ := Finset.exists_mem_eq_inf' hs (fun j => pos j + 1)
      refine ⟨j, by omega, F, hF, G, hG, by simpa using hj⟩
    · rw [dif_neg hs] at hle
      omega

end View

/-! ## 3. One order cannot serve every capacity, and one relayed packet repairs it -/

section Nesting

/-- Worlds: three bits, one per sender. -/
abbrev W3 := Fin 3 → Bool

/-- Sender `j` broadcasts bit `j`. -/
def bitMsg (j : Fin 3) (F : W3) : Bool := F j

/-- Neither receiver observes anything locally. -/
def noLoc (_F : W3) : Unit := ()

/-- Receiver 1 must act on bit `0` (actions `Bool × Bool`, first coordinate read). -/
def safe1 (F : W3) : Finset (Bool × Bool) := univ.filter (fun a => a.1 = F 0)

/-- Receiver 2 must act on bits `1` and `2`. -/
def safe2 (F : W3) : Finset (Bool × Bool) := {(F 1, F 2)}

def w000 : W3 := ![false, false, false]
def w100 : W3 := ![true, false, false]
def w010 : W3 := ![false, true, false]
def w001 : W3 := ![false, false, true]

theorem obs1 : LocalObstruction safe1 noLoc ({w000, w100} : Finset W3) := by
  refine ⟨?_, fun _ _ _ _ => rfl⟩
  rintro ⟨a, ha⟩
  have h1 := ha w000 (by simp)
  have h2 := ha w100 (by simp)
  simp only [safe1, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  rw [h1] at h2
  simp [w000, w100] at h2

theorem obs2a : LocalObstruction safe2 noLoc ({w000, w010} : Finset W3) := by
  refine ⟨?_, fun _ _ _ _ => rfl⟩
  rintro ⟨a, ha⟩
  have h1 := ha w000 (by simp)
  have h2 := ha w010 (by simp)
  simp only [safe2, Finset.mem_singleton] at h1 h2
  rw [h1] at h2
  simp [w000, w010] at h2

theorem obs2b : LocalObstruction safe2 noLoc ({w000, w001} : Finset W3) := by
  refine ⟨?_, fun _ _ _ _ => rfl⟩
  rintro ⟨a, ha⟩
  have h1 := ha w000 (by simp)
  have h2 := ha w001 (by simp)
  simp only [safe2, Finset.mem_singleton] at h1 h2
  rw [h1] at h2
  simp [w000, w001] at h2

/-- Only sender `j₀` splits a pair differing in bit `j₀` alone. -/
theorem split_pair_only (D : Finset (Fin 3)) (u v : W3) (j0 : Fin 3)
    (huv : ∀ j, j ≠ j0 → u j = v j)
    (h : Splits bitMsg D ({u, v} : Finset W3)) : j0 ∈ D := by
  obtain ⟨j, hj, F, hF, G, hG, hne⟩ := h
  by_cases hj0 : j = j0
  · exact hj0 ▸ hj
  · exfalso
    simp only [Finset.mem_insert, Finset.mem_singleton] at hF hG
    unfold bitMsg at hne
    rcases hF with rfl | rfl <;> rcases hG with rfl | rfl
    · exact hne rfl
    · exact hne (huv j hj0)
    · exact hne (huv j hj0).symm
    · exact hne rfl

theorem need1 (D : Finset (Fin 3))
    (h : ∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg D F) ∈ safe1 F) : (0 : Fin 3) ∈ D := by
  rw [decode_safe_iff] at h
  exact split_pair_only D w000 w100 0
    (fun j hj => by fin_cases j <;> simp_all [w000, w100]) (h _ obs1)

theorem need2 (D : Finset (Fin 3))
    (h : ∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg D F) ∈ safe2 F) : (1 : Fin 3) ∈ D ∧ (2 : Fin 3) ∈ D := by
  rw [decode_safe_iff] at h
  refine ⟨split_pair_only D w000 w010 1
    (fun j hj => by fin_cases j <;> simp_all [w000, w010]) (h _ obs2a),
    split_pair_only D w000 w001 2
    (fun j hj => by fin_cases j <;> simp_all [w000, w001]) (h _ obs2b)⟩

/-- Receiver 1 with `{0}` and receiver 2 with `{1, 2}` are each served. -/
theorem nesting_price_individual :
    (∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg ({0} : Finset (Fin 3)) F) ∈ safe1 F) ∧
    (∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg ({1, 2} : Finset (Fin 3)) F) ∈ safe2 F) := by
  constructor
  · refine ⟨fun v => ((v.2 0).getD false, false), fun F => ?_⟩
    simp [view, safe1, bitMsg]
  · refine ⟨fun v => ((v.2 1).getD false, (v.2 2).getD false), fun F => ?_⟩
    simp [view, safe2, bitMsg]

/-- **The price of nesting.**  No nested pair of decode sets `D₁ ⊆ D₂` with `|D₂| ≤ 2` serves
both receivers, although each is served by a set of its own capacity.  A prefix broadcast with
capacities `1` and `2` is such a nested pair. -/
theorem nesting_price (D1 D2 : Finset (Fin 3)) (hsub : D1 ⊆ D2) (hcard : D2.card ≤ 2)
    (h1 : ∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg D1 F) ∈ safe1 F)
    (h2 : ∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg D2 F) ∈ safe2 F) : False := by
  have h0 := hsub (need1 D1 h1)
  obtain ⟨ha, hb⟩ := need2 D2 h2
  have huniv : (univ : Finset (Fin 3)) ⊆ D2 := by
    intro j _
    fin_cases j
    · exact h0
    · exact ha
    · exact hb
  have := Finset.card_le_card huniv
  simp at this
  omega

/-- The decoded set when the decoded head `0` forwards the records `R` it decoded one hop earlier
(static world, so the forwarded records equal the current ones). -/
def withRelay (R D : Finset (Fin 3)) : Finset (Fin 3) := if (0 : Fin 3) ∈ D then D ∪ R else D

/-- **One relayed packet closes the nesting price**: the prefix pair `{0} ⊆ {0, 1}` (capacities
`1` and `2`, head `0` first) serves both receivers once the head forwards `{1, 2}`. -/
theorem relay_closes_nesting :
    (∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg (withRelay {1, 2} {0}) F) ∈ safe1 F) ∧
    (∃ pol : Unit × (Fin 3 → Option Bool) → Bool × Bool,
      ∀ F, pol (view noLoc bitMsg (withRelay {1, 2} {0, 1}) F) ∈ safe2 F) ∧
    ({0} : Finset (Fin 3)) ⊆ {0, 1} := by
  obtain ⟨hA, hB⟩ := nesting_price_individual
  refine ⟨decode_safe_mono safe1 noLoc bitMsg ?_ hA, decode_safe_mono safe2 noLoc bitMsg ?_ hB, ?_⟩
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    subst hj
    simp [withRelay]
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl <;> simp [withRelay]
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    subst hj
    simp

end Nesting

/-! ## 4. Choosing the decode set is a hitting-set problem -/

section Hitting

variable {J : Type*} [Fintype J] [DecidableEq J] {r : ℕ}

/-- Twin worlds per set; the receiver observes which pair it is in. -/
def hsLoc (w : Fin r × Bool) : Fin r := w.1

/-- Sender `j` reveals the twin bit exactly when `j` belongs to the pair's set. -/
def hsMsg (Fam : Fin r → Finset J) (j : J) (w : Fin r × Bool) : Bool :=
  decide (j ∈ Fam w.1) && w.2

/-- The receiver must identify its world. -/
def hsSafe (w : Fin r × Bool) : Finset (Fin r × Bool) := {w}

theorem hs_twins_obstruction (i : Fin r) :
    LocalObstruction hsSafe hsLoc ({(i, false), (i, true)} : Finset (Fin r × Bool)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩
    have h1 := ha (i, false) (by simp)
    have h2 := ha (i, true) (by simp)
    simp [hsSafe] at h1 h2
    rw [h1] at h2
    simp at h2
  · intro F hF G hG
    simp only [Finset.mem_insert, Finset.mem_singleton] at hF hG
    rcases hF with rfl | rfl <;> rcases hG with rfl | rfl <;> rfl

/-- **Every hitting-set instance is a decode-set instance.** -/
theorem hitting_embeds_decode [NeZero r] (Fam : Fin r → Finset J) (D : Finset J) :
    (∃ pol : Fin r × (J → Option Bool) → Fin r × Bool,
      ∀ F, pol (view hsLoc (hsMsg Fam) D F) ∈ hsSafe F)
      ↔ ∀ i, ∃ j ∈ D, j ∈ Fam i := by
  rw [decode_safe_iff]
  constructor
  · intro h i
    obtain ⟨j, hj, F, hF, G, hG, hne⟩ := h _ (hs_twins_obstruction i)
    refine ⟨j, hj, ?_⟩
    by_contra hjF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hF hG
    rcases hF with rfl | rfl <;> rcases hG with rfl | rfl <;> simp [hsMsg, hjF] at hne
  · intro h H ⟨hH, hloc⟩
    obtain ⟨F0, hF0⟩ := obstruction_nonempty hsSafe hH
    set i := F0.1 with hi
    have hsub : ∀ F ∈ H, F.1 = i := fun F hF => hloc F hF F0 hF0
    have hmem : ∀ b : Bool, ((i, b) : Fin r × Bool) ∈ H := by
      intro b
      by_contra hb
      apply hH
      refine ⟨(i, !b), fun F hF => ?_⟩
      have hF1 := hsub F hF
      simp only [hsSafe, Finset.mem_singleton]
      obtain ⟨f1, f2⟩ := F
      simp only at hF1
      subst hF1
      cases b <;> cases f2 <;> simp_all
    obtain ⟨j, hj, hjF⟩ := h i
    exact ⟨j, hj, (i, false), hmem false, (i, true), hmem true, by simp [hsMsg, hjF]⟩

end Hitting

/-! ## 5. Acting is not identifying -/

section Gap

variable {m : ℕ}

/-- Sender `j` reports whether the world is `j`. -/
def indMsg (j w : Fin m) : Bool := decide (w = j)

def constLoc (_w : Fin m) : Unit := ()

/-- Any answer but the true world is acceptable. -/
def notSelf (w : Fin m) : Finset (Fin m) := univ.erase w

/-- Identification: only the true world is acceptable. -/
def idSafe (w : Fin m) : Finset (Fin m) := {w}

theorem notSelf_obstruction_univ {H : Finset (Fin m)} (hH : IsObstruction notSelf H) :
    H = univ := by
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, a ∉ H := by
    by_contra hc
    push_neg at hc
    exact hne (Finset.eq_univ_of_forall hc)
  apply hH
  refine ⟨a, fun F hF => ?_⟩
  simp only [notSelf, Finset.mem_erase, Finset.mem_univ, and_true]
  rintro rfl
  exact ha hF

/-- **One decoded sender suffices to act.** -/
theorem decide_one_sender (hm : 2 ≤ m) :
    ∃ pol : Unit × (Fin m → Option Bool) → Fin m,
      ∀ F, pol (view constLoc indMsg ({⟨0, by omega⟩} : Finset (Fin m)) F) ∈ notSelf F := by
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  rw [decode_safe_iff]
  rintro H ⟨hH, -⟩
  have hu := notSelf_obstruction_univ hH
  subst hu
  refine ⟨⟨0, by omega⟩, by simp, ⟨0, by omega⟩, by simp, ⟨1, by omega⟩, by simp, ?_⟩
  simp [indMsg, Fin.ext_iff]

/-- **Identification fails as soon as two senders are left undecoded**: it needs `m − 1` of the
`m` senders. -/
theorem identify_needs_all_but_one (D : Finset (Fin m)) (u v : Fin m) (huv : u ≠ v)
    (hu : u ∉ D) (hv : v ∉ D) :
    ¬ ∃ pol : Unit × (Fin m → Option Bool) → Fin m,
      ∀ F, pol (view constLoc indMsg D F) ∈ idSafe F := by
  haveI : Nonempty (Fin m) := ⟨u⟩
  rw [decode_safe_iff]
  intro h
  have hobs : LocalObstruction idSafe constLoc ({u, v} : Finset (Fin m)) := by
    refine ⟨?_, fun _ _ _ _ => rfl⟩
    rintro ⟨a, ha⟩
    have h1 := ha u (by simp)
    have h2 := ha v (by simp)
    simp [idSafe] at h1 h2
    exact huv (h1.symm.trans h2)
  obtain ⟨j, hj, F, hF, G, hG, hne⟩ := h _ hobs
  have hju : j ≠ u := by rintro rfl; exact hu hj
  have hjv : j ≠ v := by rintro rfl; exact hv hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hF hG
  rcases hF with rfl | rfl <;> rcases hG with rfl | rfl <;>
    simp [indMsg, Ne.symm hju, Ne.symm hjv, hju, hjv] at hne

end Gap

end CIGAMF.P13.MarlDecisionDepth

#print axioms CIGAMF.P13.MarlDecisionDepth.decode_safe_iff
#print axioms CIGAMF.P13.MarlDecisionDepth.prefix_safe_iff
#print axioms CIGAMF.P13.MarlDecisionDepth.prefix_safe_mono
#print axioms CIGAMF.P13.MarlDecisionDepth.prefix_safe_iff_safeAt
#print axioms CIGAMF.P13.MarlDecisionDepth.nesting_price_individual
#print axioms CIGAMF.P13.MarlDecisionDepth.nesting_price
#print axioms CIGAMF.P13.MarlDecisionDepth.relay_closes_nesting
#print axioms CIGAMF.P13.MarlDecisionDepth.hitting_embeds_decode
#print axioms CIGAMF.P13.MarlDecisionDepth.decide_one_sender
#print axioms CIGAMF.P13.MarlDecisionDepth.identify_needs_all_but_one
