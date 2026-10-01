import Mathlib

/-!
# The injection floor of a broadcast stream

`U t ⊆ Fin m` is the set of senders transmitted at step `t` (in the prefix channel of paper_marl_v2, the union of the
decoded sets: a prefix of the committed order, so its size is the stream length and sets the bytes).  The injection
age of `j` after step `t` is the number of steps since `j` was last transmitted (`t + 1` if never).  No receiver can
hold a copy of `j` fresher than its last transmission, so these ages bound every receiver's ages from below.

## WHAT IS PROVED
* `count_recent` — if at most `L` senders are transmitted per step, then for every `s ≤ t` at most `(s + 1) L` senders
  have injection age at most `s`: they were all transmitted in the `s + 1` steps `t - s, …, t`.
* `sum_injAge_layer` — the layer-cake identity for the finite age vector: `∑_j a_j = ∑_{s ≤ t} #{j : s < a_j}`.
* `injection_floor` — hence `∑_j a_j(t) ≥ ∑_{s ≤ t} (m - (s + 1) L)` (truncated subtraction), for EVERY schedule with
  at most `L` transmissions per step.  Divided by `m` this is the floor `F(m, L)` of the paper once `t + 1 ≥ ⌈m/L⌉`.
* `floor_nine_two`, `floor_nine_three`, `floor_nine_four` — the paper's values `16/9`, `1`, `2/3` (`m = 9`,
  `L = 2, 3, 4`) as exact sums.
* `floor_attained_example` — a schedule meets the bound with equality (three senders, one per step, round-robin).

## WHAT THIS DOES NOT ESTABLISH
- That the age-first order attains the floor for every `m` and `L`: only the example is proved here.
- Anything about receiver ages beyond the lower bound (see `LeanMarlRelayOneHopV1` for the one-step upper bound).
-/

namespace CIGAMF.P13.MarlInjectionFloor

open Finset

variable {m : ℕ} (U : ℕ → Finset (Fin m))

/-- Last transmission of `j` up to step `t`, encoded: `0` never, `s + 1` at step `s`. -/
def lastTx : ℕ → Fin m → ℕ
  | 0, j => if j ∈ U 0 then 1 else 0
  | t + 1, j => if j ∈ U (t + 1) then t + 2 else lastTx t j

/-- Injection age after step `t`: steps since the last transmission (`t + 1` if never transmitted). -/
def injAge (t : ℕ) (j : Fin m) : ℕ := (t + 1) - lastTx U t j

theorem lastTx_le (t : ℕ) (j : Fin m) : lastTx U t j ≤ t + 1 := by
  induction t with
  | zero => simp only [lastTx]; split_ifs <;> omega
  | succ t ih => simp only [lastTx]; split_ifs <;> omega

/-- A positive encoded time is an actual transmission. -/
theorem lastTx_spec (t : ℕ) (j : Fin m) (hpos : 0 < lastTx U t j) :
    ∃ u, u ≤ t ∧ j ∈ U u ∧ lastTx U t j = u + 1 := by
  induction t with
  | zero =>
      simp only [lastTx] at hpos ⊢
      split_ifs at hpos ⊢ with h
      · exact ⟨0, le_rfl, h, rfl⟩
      · omega
  | succ t ih =>
      simp only [lastTx] at hpos ⊢
      split_ifs at hpos ⊢ with h
      · exact ⟨t + 1, le_rfl, h, rfl⟩
      · obtain ⟨u, hu, hj, he⟩ := ih hpos
        exact ⟨u, by omega, hj, he⟩

theorem injAge_le (t : ℕ) (j : Fin m) : injAge U t j ≤ t + 1 := by
  unfold injAge; omega

/-- **Recent senders are few.**  With at most `L` transmissions per step, at most `(s + 1) L` senders have injection
age at most `s`. -/
theorem count_recent (L : ℕ) (hL : ∀ t, (U t).card ≤ L) (t s : ℕ) (hs : s ≤ t) :
    (univ.filter fun j => injAge U t j ≤ s).card ≤ (s + 1) * L := by
  have hsub : (univ.filter fun j => injAge U t j ≤ s) ⊆ (Icc (t - s) t).biUnion U := by
    intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    unfold injAge at hj
    have hle := lastTx_le U t j
    have hpos : 0 < lastTx U t j := by omega
    obtain ⟨u, hu, hmem, he⟩ := lastTx_spec U t j hpos
    refine mem_biUnion.mpr ⟨u, mem_Icc.mpr ⟨by omega, hu⟩, hmem⟩
  calc (univ.filter fun j => injAge U t j ≤ s).card
      ≤ ((Icc (t - s) t).biUnion U).card := card_le_card hsub
    _ ≤ ∑ u ∈ Icc (t - s) t, (U u).card := card_biUnion_le
    _ ≤ ∑ _u ∈ Icc (t - s) t, L := sum_le_sum fun u _ => hL u
    _ = (s + 1) * L := by
        rw [sum_const, Nat.card_Icc, smul_eq_mul]
        congr 1
        omega

/-- The layer-cake identity for a bounded age vector. -/
theorem sum_injAge_layer (t : ℕ) :
    ∑ j, injAge U t j = ∑ s ∈ range (t + 1), (univ.filter fun j => s < injAge U t j).card := by
  have hj : ∀ j, injAge U t j = ∑ s ∈ range (t + 1), if s < injAge U t j then 1 else 0 := by
    intro j
    rw [sum_boole]
    have : (range (t + 1)).filter (fun s => s < injAge U t j) = range (injAge U t j) := by
      ext s
      simp only [mem_filter, mem_range]
      have := injAge_le U t j
      omega
    simp [this]
  calc ∑ j, injAge U t j = ∑ j, ∑ s ∈ range (t + 1), (if s < injAge U t j then 1 else 0) :=
        sum_congr rfl fun j _ => hj j
    _ = ∑ s ∈ range (t + 1), ∑ j, (if s < injAge U t j then 1 else 0) := sum_comm
    _ = ∑ s ∈ range (t + 1), (univ.filter fun j => s < injAge U t j).card := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_boole]
        simp

/-- **The injection floor.**  For every schedule with at most `L` transmissions per step, the injection ages after
step `t` sum to at least `∑_{s ≤ t} (m - (s + 1) L)`. -/
theorem injection_floor (L : ℕ) (hL : ∀ t, (U t).card ≤ L) (t : ℕ) :
    ∑ s ∈ range (t + 1), (m - (s + 1) * L) ≤ ∑ j, injAge U t j := by
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
  have hc := count_recent U L hL t s hst
  omega

/-- The paper's floor values, `m · F(m, L)` for `m = 9`: `16`, `9`, `6` (so `F = 16/9, 1, 2/3`). -/
theorem floor_nine_two : ∑ s ∈ range 5, (9 - (s + 1) * 2) = 16 := by decide
theorem floor_nine_three : ∑ s ∈ range 3, (9 - (s + 1) * 3) = 9 := by decide
theorem floor_nine_four : ∑ s ∈ range 3, (9 - (s + 1) * 4) = 6 := by decide

/-- A round-robin schedule on three senders, one per step (`j` at steps `≡ j mod 3`). -/
def rrU (t : ℕ) : Finset (Fin 3) := {⟨t % 3, Nat.mod_lt _ (by decide)⟩}

theorem rrU_card (t : ℕ) : (rrU t).card ≤ 1 := by simp [rrU]

/-- **The floor is attained**: at step `2` the round-robin ages are `2, 1, 0`, summing to `3 = (3 - 1) + (3 - 2) +
(3 - 3)`, the bound of `injection_floor` with `L = 1`. -/
theorem floor_attained_example :
    ∑ j, injAge rrU 2 j = 3 ∧ ∑ s ∈ range 3, (3 - (s + 1) * 1) = 3 := by
  refine ⟨?_, by decide⟩
  simp only [injAge]
  decide

end CIGAMF.P13.MarlInjectionFloor

#print axioms CIGAMF.P13.MarlInjectionFloor.lastTx_spec
#print axioms CIGAMF.P13.MarlInjectionFloor.count_recent
#print axioms CIGAMF.P13.MarlInjectionFloor.sum_injAge_layer
#print axioms CIGAMF.P13.MarlInjectionFloor.injection_floor
#print axioms CIGAMF.P13.MarlInjectionFloor.floor_nine_two
#print axioms CIGAMF.P13.MarlInjectionFloor.floor_attained_example
