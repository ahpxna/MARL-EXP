import Mathlib
import LeanMarlRelayOneHopV1
import LeanMarlPrefixThresholdV1
import LeanMarlInjectionFloorV1

/-!
# The price of coverage: a covering head costs one transmission per step at constant capacity, nothing with a rich
# receiver outside the prefix

The one-step bound (`LeanMarlRelayOneHopV1.one_hop`, `LeanMarlNewsRelayV1.news_one_hop`) needs the head of step `t+1`
to be a covering receiver of step `t`.  The replica (`scripts/MARL_e3_math_replica.py`, ledger L-181) found that this
head slows injection at constant `K = 1` (injection age 3.11 against the age-first floor 1.78 on 3×3; 6.56 against 3.50
on 4×4, `scripts/MARL_e3_news_relay_replica.py`).  This module explains both numbers exactly.

## WHAT IS PROVED
* `const_cover_pos`, `const_cover_transmitted` — with the threshold `r = K + [pos < K]`, `K ≥ 1`, every covering
  receiver sits at a position `≤ K`, so it was itself transmitted at that step.  A covering head of step `t+1` is
  therefore re-transmitted: one slot per step carries no new sender.
* `rich_cover_free` — conversely, a receiver with the largest threshold whose position is at least that threshold
  covers the step and was NOT transmitted (the rich7 situation): the covering head then costs nothing.
* `count_recent_rep`, `coverage_floor` — if every step shares a sender with the previous step and at most `L` senders
  are transmitted per step, at most `L + s (L - 1)` senders have injection age `≤ s`, hence
  `∑_j f_t(j) ≥ ∑_{s ≤ t} (m - L - s (L - 1))₊` — the floor of `LeanMarlInjectionFloorV1` with one slot per step lost.
* `hub_shares`, `hub_card`, `hub_floor` — on the prefix channel at constant `K` with covering heads, both hypotheses
  hold (`L = K + 1`), so the covering-head schedule obeys this larger floor.
* `coverage_floor_nine`, `coverage_floor_sixteen` — the stationary values `28 / 9 = 3.11` (`m = 9`) and
  `105 / 16 = 6.56` (`m = 16`) at `K = 1`, the replica's covering-head injection ages; the age-first floors are
  `16 / 9 = 1.78` (`LeanMarlInjectionFloorV1.floor_nine_two`) and `56 / 16 = 3.50` (`floor_sixteen_two`).
* `rot_hyps` — a three-agent rotation satisfies every hypothesis of `hub_floor` at every step (not vacuous).

## WHAT THIS DOES NOT ESTABLISH
- That the replica's covering-head rule ATTAINS the larger floor: the equality 3.11 = 28/9 and 6.56 = 105/16 is
  numerical (replica), the theorem is the lower bound.
- Which trade-off is better for the task: the covering head buys the one-step receiver bound and pays injection.
-/

namespace CIGAMF.P13.MarlPriceOfCoverage

open Finset
open CIGAMF.P13.MarlRelayOneHop (prefixDecoded)
open CIGAMF.P13.MarlPrefixThreshold (threshold)
open CIGAMF.P13.MarlInjectionFloor (injAge lastTx_le lastTx_spec sum_injAge_layer)

variable {m : ℕ}

section Channel

/-- The transmitted set of the prefix channel. -/
def tx (pos r : Fin m → ℕ) : Finset (Fin m) := univ.biUnion fun i => prefixDecoded pos r i

/-- `c` covers the step: it decoded every transmitted sender other than itself. -/
def Covering (pos r : Fin m → ℕ) (c : Fin m) : Prop := ∀ j, j ∈ tx pos r → j ≠ c → j ∈ prefixDecoded pos r c

theorem mem_tx {pos r : Fin m → ℕ} {j : Fin m} : j ∈ tx pos r ↔ ∃ i, j ≠ i ∧ pos j < r i := by
  simp [tx, prefixDecoded]

theorem const_cover_pos (K : ℕ) (hK : 1 ≤ K) (pos : Fin m → ℕ) (a0 aK : Fin m) (h0 : pos a0 = 0) (hk : pos aK = K)
    (c : Fin m) (hc : Covering pos (threshold pos K) c) : pos c ≤ K := by
  by_contra hlt
  have hne : aK ≠ a0 := by intro h; rw [h, h0] at hk; omega
  have hmem : aK ∈ tx pos (threshold pos K) := by
    refine mem_tx.mpr ⟨a0, hne, ?_⟩
    unfold threshold; rw [if_pos (by omega)]; omega
  have hnc : aK ≠ c := by intro h; rw [h] at hk; omega
  have hd := hc aK hmem hnc
  simp only [prefixDecoded, mem_filter, mem_univ, true_and] at hd
  unfold threshold at hd
  rw [if_neg (by omega)] at hd
  exact absurd hd.2 (by omega)

theorem pos_le_mem_tx (K : ℕ) (hK : 1 ≤ K) (pos : Fin m → ℕ) (a0 aK : Fin m) (h0 : pos a0 = 0) (hk : pos aK = K)
    (c : Fin m) (hc : pos c ≤ K) : c ∈ tx pos (threshold pos K) := by
  rcases Nat.eq_zero_or_pos (pos c) with hz | hp
  · refine mem_tx.mpr ⟨aK, ?_, ?_⟩
    · intro h; rw [h] at hz; omega
    · unfold threshold; split_ifs <;> omega
  · refine mem_tx.mpr ⟨a0, ?_, ?_⟩
    · intro h; rw [h] at hp; omega
    · unfold threshold; rw [if_pos (by omega)]; omega

/-- **At constant capacity a covering receiver was itself transmitted.** -/
theorem const_cover_transmitted (K : ℕ) (hK : 1 ≤ K) (pos : Fin m → ℕ) (a0 aK : Fin m) (h0 : pos a0 = 0)
    (hk : pos aK = K) (c : Fin m) (hc : Covering pos (threshold pos K) c) : c ∈ tx pos (threshold pos K) :=
  pos_le_mem_tx K hK pos a0 aK h0 hk c (const_cover_pos K hK pos a0 aK h0 hk c hc)

/-- **A rich receiver outside the prefix covers for free.** -/
theorem rich_cover_free (pos r : Fin m → ℕ) (c : Fin m) (hmax : ∀ i, r i ≤ r c) (hout : r c ≤ pos c) :
    Covering pos r c ∧ c ∉ tx pos r := by
  refine ⟨fun j hj hjc => ?_, fun hc => ?_⟩
  · obtain ⟨i, -, hi⟩ := mem_tx.mp hj
    simp only [prefixDecoded, mem_filter, mem_univ, true_and]
    exact ⟨hjc, lt_of_lt_of_le hi (hmax i)⟩
  · obtain ⟨i, -, hi⟩ := mem_tx.mp hc
    have := hmax i
    omega

/-- The rich case is satisfiable: three agents in order, thresholds `(2, 1, 2)`; agent `2` covers and is not sent. -/
theorem rich_witness :
    Covering (fun j : Fin 3 => j.val) (fun i => if i = 1 then 1 else 2) 2 ∧
      (2 : Fin 3) ∉ tx (fun j : Fin 3 => j.val) (fun i => if i = 1 then 1 else 2) :=
  rich_cover_free _ _ 2 (by decide) (by decide)

end Channel

section Injection

variable (U : ℕ → Finset (Fin m))

/-- The senders transmitted in the window `a, …, a + n`. -/
def win (a n : ℕ) : Finset (Fin m) := (range (n + 1)).biUnion fun u => U (a + u)

theorem win_card (L : ℕ) (hcard : ∀ u, (U u).card ≤ L) (hrep : ∀ u, ∃ k, k ∈ U u ∧ k ∈ U (u + 1)) (a : ℕ) :
    ∀ n, (win U a n).card + n ≤ L + n * L := by
  intro n
  induction n with
  | zero => simpa [win] using hcard a
  | succ n ih =>
      have hsplit : win U a (n + 1) = U (a + (n + 1)) ∪ win U a n := by
        unfold win; rw [Finset.range_add_one, biUnion_insert]
      obtain ⟨k, hk1, hk2⟩ := hrep (a + n)
      have hk2' : k ∈ U (a + (n + 1)) := by rwa [show a + (n + 1) = a + n + 1 by omega]
      have hkw : k ∈ win U a n := mem_biUnion.mpr ⟨n, mem_range.mpr (by omega), hk1⟩
      have hsub : U (a + (n + 1)) \ win U a n ⊆ (U (a + (n + 1))).erase k := by
        intro x hx
        rw [mem_sdiff] at hx
        exact mem_erase.mpr ⟨fun h => hx.2 (h ▸ hkw), hx.1⟩
      have h1 : (U (a + (n + 1)) \ win U a n).card ≤ (U (a + (n + 1))).card - 1 := by
        rw [← card_erase_of_mem hk2']; exact card_le_card hsub
      have h2 := hcard (a + (n + 1))
      have hL1 : 1 ≤ (U (a + (n + 1))).card := card_pos.mpr ⟨k, hk2'⟩
      have h3 : (win U a (n + 1)).card = (U (a + (n + 1)) \ win U a n).card + (win U a n).card := by
        rw [hsplit, card_sdiff_add_card]
      have h4 : (n + 1) * L = n * L + L := by ring
      omega

/-- **Recent senders with one repeat per step.** -/
theorem count_recent_rep (L : ℕ) (hcard : ∀ u, (U u).card ≤ L) (hrep : ∀ u, ∃ k, k ∈ U u ∧ k ∈ U (u + 1))
    (t s : ℕ) (hs : s ≤ t) : (univ.filter fun j => injAge U t j ≤ s).card + s ≤ L + s * L := by
  have hsub : (univ.filter fun j => injAge U t j ≤ s) ⊆ win U (t - s) s := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    unfold injAge at hj
    have hle := lastTx_le U t j
    obtain ⟨u, hu, hmem, he⟩ := lastTx_spec U t j (by omega)
    refine mem_biUnion.mpr ⟨u - (t - s), mem_range.mpr (by omega), ?_⟩
    rwa [show t - s + (u - (t - s)) = u by omega]
  have h1 := card_le_card hsub
  have h2 := win_card U L hcard hrep (t - s) s
  omega

/-- **The floor with one slot per step lost.** -/
theorem coverage_floor (L : ℕ) (hcard : ∀ u, (U u).card ≤ L) (hrep : ∀ u, ∃ k, k ∈ U u ∧ k ∈ U (u + 1)) (t : ℕ) :
    ∑ s ∈ range (t + 1), (m - (L + s * (L - 1))) ≤ ∑ j, injAge U t j := by
  rw [sum_injAge_layer U t]
  refine sum_le_sum fun s hs => ?_
  have hst : s ≤ t := by simpa [mem_range, Nat.lt_succ_iff] using hs
  have hU : (univ : Finset (Fin m)) =
      (univ.filter fun j => injAge U t j ≤ s) ∪ (univ.filter fun j => s < injAge U t j) := by
    ext j
    simp only [mem_univ, mem_union, mem_filter, true_and, true_iff]
    exact le_or_gt _ _
  have hsplit : m ≤ (univ.filter fun j => injAge U t j ≤ s).card + (univ.filter fun j => s < injAge U t j).card := by
    calc m = (univ : Finset (Fin m)).card := by simp
      _ = ((univ.filter fun j => injAge U t j ≤ s) ∪ (univ.filter fun j => s < injAge U t j)).card := by rw [← hU]
      _ ≤ _ := card_union_le _ _
  have hc := count_recent_rep U L hcard hrep t s hst
  have hL1 : 1 ≤ L := by
    obtain ⟨k, hk, -⟩ := hrep 0
    exact lt_of_lt_of_le (card_pos.mpr ⟨k, hk⟩) (hcard 0)
  have hmul : s * (L - 1) + s = s * L := by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [Nat.add_sub_cancel]; ring
  omega

/-- Stationary values at `L = 2` (`K = 1`): `m · F_cover = 28` for `m = 9`, `105` for `m = 16`. -/
theorem coverage_floor_nine : ∑ s ∈ range 8, (9 - (2 + s * (2 - 1))) = 28 := by decide
theorem coverage_floor_sixteen : ∑ s ∈ range 15, (16 - (2 + s * (2 - 1))) = 105 := by decide
/-- The age-first floor at `m = 16`, `L = 2`: `56 = 16 · 3.5`. -/
theorem floor_sixteen_two : ∑ s ∈ range 8, (16 - (s + 1) * 2) = 56 := by decide

end Injection

section Hub

/-- **On the prefix channel at constant capacity, covering heads make consecutive steps share a sender.** -/
theorem hub_shares (K : ℕ) (hK : 1 ≤ K) (pos : ℕ → Fin m → ℕ) (a0 aK : ℕ → Fin m) (h0 : ∀ t, pos t (a0 t) = 0)
    (hk : ∀ t, pos t (aK t) = K) (h : ℕ → Fin m) (hhead : ∀ t, pos t (h t) = 0)
    (hcov : ∀ t, Covering (pos t) (threshold (pos t) K) (h (t + 1))) (u : ℕ) :
    ∃ k, k ∈ tx (pos u) (threshold (pos u) K) ∧ k ∈ tx (pos (u + 1)) (threshold (pos (u + 1)) K) :=
  ⟨h (u + 1), const_cover_transmitted K hK (pos u) (a0 u) (aK u) (h0 u) (hk u) _ (hcov u),
    pos_le_mem_tx K hK (pos (u + 1)) (a0 (u + 1)) (aK (u + 1)) (h0 (u + 1)) (hk (u + 1)) _ (by rw [hhead]; omega)⟩

/-- At constant capacity at most `K + 1` senders are transmitted (positions are distinct). -/
theorem hub_card (K : ℕ) (pos : Fin m → ℕ) (hinj : Function.Injective pos) :
    (tx pos (threshold pos K)).card ≤ K + 1 := by
  rw [← card_image_of_injective _ hinj]
  calc ((tx pos (threshold pos K)).image pos).card ≤ (range (K + 1)).card := by
        refine card_le_card fun x hx => ?_
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
        obtain ⟨i, -, hi⟩ := mem_tx.mp hj
        refine mem_range.mpr (lt_of_lt_of_le hi ?_)
        unfold threshold; split_ifs <;> omega
    _ = K + 1 := card_range _

/-- **The covering-head floor on the prefix channel.** -/
theorem hub_floor (K : ℕ) (hK : 1 ≤ K) (pos : ℕ → Fin m → ℕ) (hinj : ∀ t, Function.Injective (pos t))
    (a0 aK : ℕ → Fin m) (h0 : ∀ t, pos t (a0 t) = 0) (hk : ∀ t, pos t (aK t) = K) (h : ℕ → Fin m)
    (hhead : ∀ t, pos t (h t) = 0) (hcov : ∀ t, Covering (pos t) (threshold (pos t) K) (h (t + 1))) (t : ℕ) :
    ∑ s ∈ range (t + 1), (m - ((K + 1) + s * (K + 1 - 1))) ≤
      ∑ j, injAge (fun u => tx (pos u) (threshold (pos u) K)) t j :=
  coverage_floor _ (K + 1) (fun u => hub_card K (pos u) (hinj u)) (hub_shares K hK pos a0 aK h0 hk h hhead hcov) t

/-- Rotation on three agents: at step `t` the order is `(a, a+1, a+2)` with `a = t mod 3`. -/
def rotHead (t : ℕ) : Fin 3 := ⟨t % 3, Nat.mod_lt _ (by decide)⟩

def rotPos (a : Fin 3) (j : Fin 3) : ℕ := (j - a).val

theorem rotHead_succ (t : ℕ) : rotHead (t + 1) = rotHead t + 1 := by
  apply Fin.ext
  simp only [rotHead, Fin.val_add]
  omega

/-- **The hypotheses of `hub_floor` are satisfiable** (`K = 1`, three agents, the covering head of each step heads the
next one). -/
theorem rot_hyps :
    (∀ t, Function.Injective (rotPos (rotHead t))) ∧ (∀ t, rotPos (rotHead t) (rotHead t) = 0) ∧
    (∀ t, rotPos (rotHead t) (rotHead t + 1) = 1) ∧
    (∀ t, Covering (rotPos (rotHead t)) (threshold (rotPos (rotHead t)) 1) (rotHead (t + 1))) := by
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · generalize rotHead t = a; revert a; decide
  · generalize rotHead t = a; revert a; decide
  · generalize rotHead t = a; revert a; decide
  · rw [rotHead_succ]
    unfold Covering tx
    generalize rotHead t = a
    revert a
    decide

theorem rot_floor (t : ℕ) :
    ∑ s ∈ range (t + 1), (3 - ((1 + 1) + s * (1 + 1 - 1))) ≤
      ∑ j, injAge (fun u => tx (rotPos (rotHead u)) (threshold (rotPos (rotHead u)) 1)) t j :=
  hub_floor 1 le_rfl (fun u => rotPos (rotHead u)) rot_hyps.1 rotHead (fun u => rotHead u + 1) rot_hyps.2.1
    rot_hyps.2.2.1 rotHead rot_hyps.2.1 rot_hyps.2.2.2 t

end Hub

end CIGAMF.P13.MarlPriceOfCoverage

#print axioms CIGAMF.P13.MarlPriceOfCoverage.const_cover_transmitted
#print axioms CIGAMF.P13.MarlPriceOfCoverage.rich_cover_free
#print axioms CIGAMF.P13.MarlPriceOfCoverage.rich_witness
#print axioms CIGAMF.P13.MarlPriceOfCoverage.count_recent_rep
#print axioms CIGAMF.P13.MarlPriceOfCoverage.coverage_floor
#print axioms CIGAMF.P13.MarlPriceOfCoverage.coverage_floor_nine
#print axioms CIGAMF.P13.MarlPriceOfCoverage.coverage_floor_sixteen
#print axioms CIGAMF.P13.MarlPriceOfCoverage.floor_sixteen_two
#print axioms CIGAMF.P13.MarlPriceOfCoverage.hub_shares
#print axioms CIGAMF.P13.MarlPriceOfCoverage.hub_card
#print axioms CIGAMF.P13.MarlPriceOfCoverage.hub_floor
#print axioms CIGAMF.P13.MarlPriceOfCoverage.rot_hyps
#print axioms CIGAMF.P13.MarlPriceOfCoverage.rot_floor
