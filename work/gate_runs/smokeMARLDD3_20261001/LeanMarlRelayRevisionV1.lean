import Mathlib
import LeanMarlRelayOneHopV1
import LeanMarlStrongOneHopV1
import LeanMarlBlockFrontierV1
import LeanMarlPrefixThresholdV1

/-!
# Patching the selector theory of paper_marl (Paper 1) with the relay geometry of paper_marl_v2 (Paper 2)

Paper 1's revision bounds (`LeanMarlBlockFrontierV1.block_frontier`, `block_zero_price`, reused unchanged) need the
committed prefix `P` to be top-k by a score `w` whose marginals approximate the true value (`ScoreLocal f w η`).  Paper 1
could not satisfy this in traffic: its base order was a cached-queue order, not a score order (paper_marl.tex l.212–214),
so the bound never applied.  Under relay with a covering head the hypotheses become checkable:

1. **View determinacy** (`view_determinacy`, `age_formula`): after step `t+1`, receiver `i`'s copy of `j` is either fresh
   (`j` decoded directly at `t+1`, age 0) or EXACTLY the network's last transmission of `j` up to `t` (age `1 + f_t(j)`).
   The profile decides only who receives an age-0 copy; every other copy is fixed by the network history
   (`revision_ages`: two profiles with the same history differ only on their symmetric difference, by at most
   `1 + f_t(j)` per entry).
2. **A legal score** (`lin_scoreLocal`, `approx_scoreLocal`): if the team value is within `η/2` of the uniform-linear
   value `−c Σ ages`, then `ScoreLocal f w η` holds with `w(e) = c (1 + f_t(sender e))`, computable from the scheduler's
   mirror (legal information).
3. **The age-first prefix is top-k by that score** (`oldest_is_top`), so Paper 1's theorems apply:
   `relay_frontier` (every block-feasible profile is within `2η Σ_b (|P_b ∖ T_b| − R)_+` of one reachable with `R`
   revisions) and `relay_zero_price` (at `η = 0` the age-first prefix is optimal; no revision helps).

The revision headroom available to a learned selector is therefore controlled by `η`, the deviation of the actor's
age-sensitivity from uniform: a selector can gain only where some agents' freshness matters more than others'.

4. **Profile families** (`prefix_cover_preserving`, `cover_preserving_not_nested`): the relay guarantee needs only that
   every receiver decodes the head and the next head covers the step, a family strictly larger than nested prefixes.

## WHAT IS PROVED
`table_succ_le_of_not`, `view_determinacy`, `age_formula`, `lastTx_congr`, `revision_ages`, `linVal_insert`,
`lin_scoreLocal`, `approx_scoreLocal`, `oldest_is_top`, `relay_frontier`, `relay_zero_price`, `frontier_witness`,
`prefix_cover_preserving`, `cover_preserving_not_nested`.

## WHAT THIS DOES NOT ESTABLISH
- That a learned critic estimates `f` well (`ε` of Paper 1's Theorem 1): that is empirical, and was Paper 1's failure.
- Continuation effects: the value here is the value of the views after one step; a revision can change later steps.
- The encoding of non-head receiver–sender pairs as the edges `Fin n` (with the head's edges always included, at age
  0) is by construction; `relay_frontier` is stated on that edge set.
-/

namespace CIGAMF.P13.MarlRelayRevision

open Finset
open CIGAMF.P13.MarlRelayOneHop
open CIGAMF.P13.MarlStrongOneHop (StrongHeads strong_one_hop)

section View

variable {m : ℕ} (S : ℕ → Fin m → Finset (Fin m))

/-- A copy not decoded directly at `t+1` is no fresher than the last transmission up to `t`. -/
theorem table_succ_le_of_not (t : ℕ) (i j : Fin m) (hj : j ∉ S (t + 1) i) :
    table S (t + 1) i j ≤ lastTx S t j := by
  simp only [table]
  rw [if_neg hj]
  exact max_le (cache_le_lastTx S t i j) (Finset.sup_le fun k _ => table_le_lastTx S t k j)

variable {S}

/-- **View determinacy.** -/
theorem view_determinacy {h : ℕ → Fin m} (H : StrongHeads S h) (t : ℕ) (i j : Fin m) (hji : j ≠ i)
    (hj : j ∉ S (t + 1) i) : table S (t + 1) i j = lastTx S t j :=
  le_antisymm (table_succ_le_of_not S t i j hj) (strong_one_hop H t i j hji)

/-- Ages after step `t+1`: `0` for a direct decode, `1 + f_t(j)` otherwise. -/
theorem age_formula {h : ℕ → Fin m} (H : StrongHeads S h) (t : ℕ) (i j : Fin m) (hji : j ≠ i) :
    (t + 2) - table S (t + 1) i j = if j ∈ S (t + 1) i then 0 else 1 + ((t + 1) - lastTx S t j) := by
  split_ifs with hj
  · have := table_of_mem S hj
    omega
  · have h1 := view_determinacy H t i j hji hj
    have h2 := lastTx_le_succ S t j
    omega

/-- The last transmissions up to `t` depend only on the schedule up to `t`. -/
theorem lastTx_congr {S S' : ℕ → Fin m → Finset (Fin m)} (t : ℕ) :
    (∀ u, u ≤ t → S u = S' u) → ∀ j, lastTx S t j = lastTx S' t j := by
  induction t with
  | zero =>
      intro hS j
      simp only [lastTx]
      rw [hS 0 le_rfl]
  | succ t ih =>
      intro hS j
      simp only [lastTx]
      rw [hS (t + 1) le_rfl, ih (fun u hu => hS u (by omega)) j]

/-- **Two profiles with the same history differ only where their direct decodes differ**, and there by at most
`1 + f_t(j)`. -/
theorem revision_ages {S S' : ℕ → Fin m → Finset (Fin m)} {h h' : ℕ → Fin m} (H : StrongHeads S h)
    (H' : StrongHeads S' h') (t : ℕ) (hS : ∀ u, u ≤ t → S u = S' u) (i j : Fin m) (hji : j ≠ i) :
    ((j ∈ S (t + 1) i ↔ j ∈ S' (t + 1) i) →
        (t + 2) - table S (t + 1) i j = (t + 2) - table S' (t + 1) i j) ∧
      (t + 2) - table S (t + 1) i j ≤ 1 + ((t + 1) - lastTx S t j) ∧
      (t + 2) - table S' (t + 1) i j ≤ 1 + ((t + 1) - lastTx S t j) := by
  have hc := lastTx_congr t hS j
  rw [age_formula H t i j hji, age_formula H' t i j hji, ← hc]
  refine ⟨fun hiff => ?_, ?_, ?_⟩
  · by_cases hj : j ∈ S (t + 1) i
    · rw [if_pos hj, if_pos (hiff.mp hj)]
    · rw [if_neg hj, if_neg (fun h' => hj (hiff.mpr h'))]
  · split_ifs <;> omega
  · split_ifs <;> omega

end View

section Frontier

open CIGAMF.P13.MarlEstimatedRevision (ScoreLocal)
open CIGAMF.P13.MarlBlockFrontier (part block_frontier block_zero_price)

variable {n r : ℕ}

/-- Age of edge `e` under profile `E` (the `age_formula`): `0` if decoded directly, `1 + φ e` otherwise. -/
def ageVec (φ : Fin n → ℝ) (E : Finset (Fin n)) (e : Fin n) : ℝ := if e ∈ E then 0 else 1 + φ e

/-- The uniform-linear team value of a profile. -/
def linVal (c : ℝ) (φ : Fin n → ℝ) (E : Finset (Fin n)) : ℝ := -c * ∑ e, ageVec φ E e

theorem linVal_insert (c : ℝ) (φ : Fin n → ℝ) (E : Finset (Fin n)) (e : Fin n) (he : e ∉ E) :
    linVal c φ (insert e E) - linVal c φ E = c * (1 + φ e) := by
  have key : ∀ x, ageVec φ E x - ageVec φ (insert e E) x = if x = e then 1 + φ e else 0 := by
    intro x
    by_cases hx : x = e
    · subst hx; simp [ageVec, he]
    · simp [ageVec, hx, Finset.mem_insert]
  have hsum : ∑ x, ageVec φ E x - ∑ x, ageVec φ (insert e E) x = 1 + φ e := by
    rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun x _ => key x)]
    simp
  unfold linVal
  linear_combination c * hsum

/-- **The uniform-linear value satisfies Paper 1's `ScoreLocal` with the age score and `η = 0`.** -/
theorem lin_scoreLocal (c : ℝ) (φ : Fin n → ℝ) : ScoreLocal (linVal c φ) (fun e => c * (1 + φ e)) 0 := by
  intro A i hi
  rw [linVal_insert c φ A i hi]
  simp

/-- A value within `η/2` of the uniform-linear one satisfies `ScoreLocal` with `η`. -/
theorem approx_scoreLocal (f : Finset (Fin n) → ℝ) (c : ℝ) (φ : Fin n → ℝ) (η : ℝ)
    (hη : ∀ E, |f E - linVal c φ E| ≤ η / 2) : ScoreLocal f (fun e => c * (1 + φ e)) η := by
  intro A i hi
  have h1 := hη (insert i A)
  have h2 := hη A
  have h3 := linVal_insert c φ A i hi
  have : f (insert i A) - f A - c * (1 + φ i) =
      (f (insert i A) - linVal c φ (insert i A)) - (f A - linVal c φ A) := by linarith
  rw [this]
  calc |(f (insert i A) - linVal c φ (insert i A)) - (f A - linVal c φ A)|
      ≤ |f (insert i A) - linVal c φ (insert i A)| + |f A - linVal c φ A| := abs_sub _ _
    _ ≤ η / 2 + η / 2 := add_le_add h1 h2
    _ = η := by ring

/-- **The age-first prefix is top-k by the age score** (oldest first within every receiver block, `c ≥ 0`). -/
theorem oldest_is_top (blk : Fin n → Fin r) (P : Finset (Fin n)) (c : ℝ) (hc : 0 ≤ c) (φ : Fin n → ℝ)
    (hOld : ∀ e ∈ P, ∀ e' ∉ P, blk e = blk e' → φ e' ≤ φ e) :
    ∀ e ∈ P, ∀ e' ∉ P, blk e = blk e' → c * (1 + φ e') ≤ c * (1 + φ e) := by
  intro e he e' he' hb
  exact mul_le_mul_of_nonneg_left (by linarith [hOld e he e' he' hb]) hc

/-- **Paper 1's block frontier on the relay substrate.** -/
theorem relay_frontier (f : Finset (Fin n) → ℝ) (c : ℝ) (hc : 0 ≤ c) (φ : Fin n → ℝ) (η : ℝ)
    (hη : ∀ E, |f E - linVal c φ E| ≤ η / 2) (blk : Fin n → Fin r) (P T : Finset (Fin n)) (R : ℕ)
    (hcard : ∀ b, (part blk T b).card = (part blk P b).card)
    (hOld : ∀ e ∈ P, ∀ e' ∉ P, blk e = blk e' → φ e' ≤ φ e) :
    ∃ S : Finset (Fin n), (∀ b, (part blk S b).card = (part blk P b).card) ∧
      (∀ b, (part blk S b \ part blk P b).card ≤ R) ∧
      f T - f S ≤ 2 * η * (∑ b, (((part blk P b \ part blk T b).card - R : ℕ) : ℝ)) :=
  block_frontier f _ η (approx_scoreLocal f c φ η hη) blk P T R hcard (oldest_is_top blk P c hc φ hOld)

/-- **Zero price: for a uniform-linear actor the age-first prefix is optimal** (no revision helps). -/
theorem relay_zero_price (c : ℝ) (hc : 0 ≤ c) (φ : Fin n → ℝ) (blk : Fin n → Fin r) (P T : Finset (Fin n))
    (hcard : ∀ b, (part blk T b).card = (part blk P b).card)
    (hOld : ∀ e ∈ P, ∀ e' ∉ P, blk e = blk e' → φ e' ≤ φ e) :
    linVal c φ T ≤ linVal c φ P := by
  refine block_zero_price (linVal c φ) _ 0 (lin_scoreLocal c φ) blk P T hcard ?_
  intro e he e' he' hb
  simpa using oldest_is_top blk P c hc φ hOld e he e' he' hb

/-- The hypotheses are satisfiable and the conclusion is not vacuous: two edges in one block, injection ages `1, 0`,
the prefix `{0}` (the older sender) beats `{1}` strictly. -/
theorem frontier_witness :
    linVal (n := 2) 1 (fun e => if e = 0 then 1 else 0) {1} < linVal (n := 2) 1 (fun e => if e = 0 then 1 else 0) {0} ∧
      (∀ e ∈ ({0} : Finset (Fin 2)), ∀ e' ∉ ({0} : Finset (Fin 2)),
        (fun _ : Fin 2 => (0 : Fin 1)) e = (fun _ : Fin 2 => (0 : Fin 1)) e' →
          (fun e : Fin 2 => if e = 0 then (1 : ℝ) else 0) e' ≤ (fun e : Fin 2 => if e = 0 then (1 : ℝ) else 0) e) := by
  refine ⟨?_, ?_⟩
  · norm_num [linVal, ageVec, Fin.sum_univ_two]
  · intro e he e' he' _
    simp only [Finset.mem_singleton] at he he'
    subst he
    simp [he']

end Frontier

section Families

variable {m : ℕ}

/-- Every receiver other than the head decodes the head. -/
def HeadPreserving (D : Fin m → Finset (Fin m)) (h : Fin m) : Prop := ∀ i, i ≠ h → h ∈ D i

/-- Head-preserving, and receiver `c` decoded every transmitted sender but itself. -/
def CoverPreserving (D : Fin m → Finset (Fin m)) (h c : Fin m) : Prop :=
  HeadPreserving D h ∧ ∀ j, (∃ i, j ∈ D i) → j ≠ c → j ∈ D c

/-- Nested prefixes are cover-preserving. -/
theorem prefix_cover_preserving [NeZero m] (pos r : Fin m → ℕ) (hd : Fin m) (h0 : pos hd = 0) (hr : ∀ i, 1 ≤ r i) :
    ∃ c, CoverPreserving (prefixDecoded pos r) hd c := by
  obtain ⟨c, hc⟩ := prefix_cover_exists pos r
  exact ⟨c, prefix_head_decoded pos r hd h0 hr, hc⟩

/-- **The family is strictly larger than nested profiles**: a three-agent profile that is cover-preserving but not
nested (receivers `0` and `1` decode `{1}` and `{0}`). -/
theorem cover_preserving_not_nested :
    CoverPreserving (m := 3) (fun i => if i = 0 then {1} else {0}) 0 1 ∧
      ¬ ((fun i : Fin 3 => if i = 0 then ({1} : Finset (Fin 3)) else {0}) 0 ⊆
          (fun i : Fin 3 => if i = 0 then ({1} : Finset (Fin 3)) else {0}) 1) ∧
      ¬ ((fun i : Fin 3 => if i = 0 then ({1} : Finset (Fin 3)) else {0}) 1 ⊆
          (fun i : Fin 3 => if i = 0 then ({1} : Finset (Fin 3)) else {0}) 0) := by
  unfold CoverPreserving HeadPreserving
  decide

end Families

end CIGAMF.P13.MarlRelayRevision

#print axioms CIGAMF.P13.MarlRelayRevision.table_succ_le_of_not
#print axioms CIGAMF.P13.MarlRelayRevision.view_determinacy
#print axioms CIGAMF.P13.MarlRelayRevision.age_formula
#print axioms CIGAMF.P13.MarlRelayRevision.lastTx_congr
#print axioms CIGAMF.P13.MarlRelayRevision.revision_ages
#print axioms CIGAMF.P13.MarlRelayRevision.linVal_insert
#print axioms CIGAMF.P13.MarlRelayRevision.lin_scoreLocal
#print axioms CIGAMF.P13.MarlRelayRevision.approx_scoreLocal
#print axioms CIGAMF.P13.MarlRelayRevision.oldest_is_top
#print axioms CIGAMF.P13.MarlRelayRevision.relay_frontier
#print axioms CIGAMF.P13.MarlRelayRevision.relay_zero_price
#print axioms CIGAMF.P13.MarlRelayRevision.frontier_witness
#print axioms CIGAMF.P13.MarlRelayRevision.prefix_cover_preserving
#print axioms CIGAMF.P13.MarlRelayRevision.cover_preserving_not_nested
