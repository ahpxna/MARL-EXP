import Mathlib
import «LeanMarlEstimatedRevisionV1»

/-!
# T1 for heterogeneous receivers: the blockwise revision frontier (partition-matroid profiles)

The heterogeneous-receiver profile `S = (S_1, …, S_r)` is encoded as ONE set of edges
`S ⊆ Fin n` (an edge is a receiver–sender pair), with `blk : Fin n → Fin r` naming the receiver
(block) of each edge.  A feasible profile has, in every block `b`, the same number of edges as the
prefix `P` (receiver capacities).  Per-block revision radius: `|(S \ P) ∩ block b| ≤ R`.

The team value `f` is ANY set function of the edge set (coupled across receivers).  The only
hypothesis is edge-local: every marginal `f(A ∪ {e}) − f(A)` is within `η` of a score `w e`
(`ScoreLocal`, as in `LeanMarlEstimatedRevisionV1`).

## WHAT IS PROVED

* `block_frontier` — if `P` is top-`k_b` by `w` INSIDE every block, then for every per-block
  feasible `T` there is a feasible `S` with at most `R` replacements in EVERY block and
      f T − f S ≤ 2η · Σ_b (|P_b \ T_b| − R)₊.
  The single-set frontier (`score_frontier`) is the case `r = 1`.
* `block_zero_price` — a per-block cut margin of `2η` makes the prefix optimal over all
  per-block feasible profiles.
* `block_hypotheses_satisfiable` — a concrete two-receiver instance meets every hypothesis.

## WHAT THIS DOES NOT ESTABLISH

- That traffic values satisfy the edge-local hypothesis with a small `η`; `η` must be bounded by
  data (e.g. `LeanMarlRevisionAuditBridgeV1` transfer lemmas) or it is an assumption.
- Byte caps: the family here is per-block cardinality and radius only.
- Any learning statement; the calibration side is `LeanMarlRepairCalibrationV1` (needle class)
  and `LeanMarlProfileSearchV1` (finite search).
-/

namespace CIGAMF.P13.MarlBlockFrontier

open Finset CIGAMF.P13.MarlSubsetFrontier CIGAMF.P13.MarlEstimatedRevision

variable {n r : ℕ}

/-- Block `b`'s part of an edge set. -/
def part (blk : Fin n → Fin r) (S : Finset (Fin n)) (b : Fin r) : Finset (Fin n) :=
  S.filter (fun e => blk e = b)

theorem part_sdiff (blk : Fin n → Fin r) (S T : Finset (Fin n)) (b : Fin r) :
    part blk (S \ T) b = part blk S b \ part blk T b := by
  ext e; simp only [part, Finset.mem_filter, Finset.mem_sdiff]; tauto

theorem sum_by_blocks (blk : Fin n → Fin r) (A : Finset (Fin n)) (w : Fin n → ℝ) :
    A.sum w = ∑ b, (part blk A b).sum w := by
  unfold part
  exact (Finset.sum_fiberwise A blk w).symm

theorem card_by_blocks (blk : Fin n → Fin r) (A : Finset (Fin n)) :
    A.card = ∑ b, (part blk A b).card := by
  unfold part
  exact Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (blk x))

/-- The per-block exchange path, kept inside the block. -/
theorem block_path (blk : Fin n → Fin r) (P T : Finset (Fin n)) (R : ℕ) (b : Fin r)
    (hc : (part blk T b).card = (part blk P b).card) :
    ∃ S : Finset (Fin n), S.card = (part blk P b).card ∧ (S \ part blk P b).card ≤ R ∧
      S \ part blk T b ⊆ part blk P b ∧ (∀ e ∈ part blk T b \ S, e ∉ part blk P b) ∧
      (S \ part blk T b).card = (part blk P b \ part blk T b).card - R ∧
      (∀ e ∈ S, blk e = b) := by
  obtain ⟨S, hS, hSP, hsub, hout, hcard⟩ :=
    exchange_path (part blk P b) (part blk T b) (part blk P b).card R rfl hc
  refine ⟨S, hS, hSP, hsub, hout, hcard, fun e he => ?_⟩
  by_cases hT : e ∈ part blk T b
  · exact (Finset.mem_filter.mp hT).2
  · exact (Finset.mem_filter.mp (hsub (Finset.mem_sdiff.mpr ⟨he, hT⟩))).2

/-- **The blockwise frontier.** -/
theorem block_frontier (f : Finset (Fin n) → ℝ) (w : Fin n → ℝ) (η : ℝ) (h : ScoreLocal f w η)
    (blk : Fin n → Fin r) (P T : Finset (Fin n)) (R : ℕ)
    (hcard : ∀ b, (part blk T b).card = (part blk P b).card)
    (hTop : ∀ e ∈ P, ∀ e' ∉ P, blk e = blk e' → w e' ≤ w e) :
    ∃ S : Finset (Fin n), (∀ b, (part blk S b).card = (part blk P b).card) ∧
      (∀ b, (part blk S b \ part blk P b).card ≤ R) ∧
      f T - f S ≤ 2 * η * (∑ b, (((part blk P b \ part blk T b).card - R : ℕ) : ℝ)) := by
  classical
  choose Sb hSb using fun b => block_path blk P T R b (hcard b)
  set S := Finset.univ.biUnion Sb with hSdef
  have hpart : ∀ b, part blk S b = Sb b := by
    intro b; ext e
    simp only [part, Finset.mem_filter, hSdef, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨b', he⟩, hb⟩
      have := (hSb b').2.2.2.2.2 e he
      rw [show b = b' from hb.symm.trans this]; exact he
    · intro he
      exact ⟨⟨b, he⟩, (hSb b).2.2.2.2.2 e he⟩
  refine ⟨S, fun b => by rw [hpart]; exact (hSb b).1, fun b => by rw [hpart]; exact (hSb b).2.1, ?_⟩
  have hv := value_exchange_w f w η h S T
  -- per-block ordering of the exchanged edges
  have hblock : ∀ b, (part blk T b \ part blk S b).sum w ≤ (part blk S b \ part blk T b).sum w := by
    intro b
    rw [hpart]
    have hc : (Sb b \ part blk T b).card = (part blk T b \ Sb b).card :=
      Finset.card_sdiff_comm ((hSb b).1.trans (hcard b).symm)
    refine sum_le_of_pointwise (Sb b \ part blk T b) (part blk T b \ Sb b) w hc ?_
    intro i hi j hj
    have hiP := (hSb b).2.2.1 hi
    have hjP := (hSb b).2.2.2.1 j hj
    have hib : blk i = b := (Finset.mem_filter.mp hiP).2
    have hjb : blk j = b := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj).1).2
    refine hTop i (Finset.mem_filter.mp hiP).1 j ?_ (hib.trans hjb.symm)
    intro hjP'
    exact hjP (Finset.mem_filter.mpr ⟨hjP', hjb⟩)
  have hsum : (T \ S).sum w ≤ (S \ T).sum w := by
    rw [sum_by_blocks blk (T \ S) w, sum_by_blocks blk (S \ T) w]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [part_sdiff, part_sdiff]; exact hblock b
  have hcST : (S \ T).card = ∑ b, ((part blk P b \ part blk T b).card - R) := by
    rw [card_by_blocks blk (S \ T)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [part_sdiff, hpart]; exact (hSb b).2.2.2.2.1
  have hcTS : (T \ S).card = (S \ T).card := by
    rw [card_by_blocks blk (T \ S), card_by_blocks blk (S \ T)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [part_sdiff, part_sdiff, hpart]
    exact (Finset.card_sdiff_comm ((hSb b).1.trans (hcard b).symm)).symm
  rw [hcTS, hcST] at hv
  push_cast at hv ⊢
  linarith

/-- **Nesting is free under a per-block `2η` margin.** -/
theorem block_zero_price (f : Finset (Fin n) → ℝ) (w : Fin n → ℝ) (η : ℝ) (h : ScoreLocal f w η)
    (blk : Fin n → Fin r) (P T : Finset (Fin n))
    (hcard : ∀ b, (part blk T b).card = (part blk P b).card)
    (hMargin : ∀ e ∈ P, ∀ e' ∉ P, blk e = blk e' → 2 * η + w e' ≤ w e) :
    f T ≤ f P := by
  classical
  have hv := value_exchange_w f w η h P T
  have hblock : ∀ b, ((part blk P b \ part blk T b).card : ℝ) * (2 * η) ≤
      (part blk P b \ part blk T b).sum w - (part blk T b \ part blk P b).sum w := by
    intro b
    have hc : (part blk P b \ part blk T b).card = (part blk T b \ part blk P b).card :=
      Finset.card_sdiff_comm (hcard b).symm
    refine surplus_ge_card_mul' _ _ w (2 * η) hc ?_
    intro i hi j hj
    have hiP := (Finset.mem_sdiff.mp hi).1; have hjT := (Finset.mem_sdiff.mp hj)
    have hib : blk i = b := (Finset.mem_filter.mp hiP).2
    have hjb : blk j = b := (Finset.mem_filter.mp hjT.1).2
    refine hMargin i (Finset.mem_filter.mp hiP).1 j ?_ (hib.trans hjb.symm)
    intro hjP; exact hjT.2 (Finset.mem_filter.mpr ⟨hjP, hjb⟩)
  have hS : ((P \ T).card : ℝ) * (2 * η) ≤ (P \ T).sum w - (T \ P).sum w := by
    rw [sum_by_blocks blk (P \ T) w, sum_by_blocks blk (T \ P) w, card_by_blocks blk (P \ T)]
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [part_sdiff, part_sdiff]; exact hblock b
  have hc : (T \ P).card = (P \ T).card := by
    rw [card_by_blocks blk (T \ P), card_by_blocks blk (P \ T)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [part_sdiff, part_sdiff]; exact (Finset.card_sdiff_comm (hcard b).symm).symm
  rw [hc] at hv
  push_cast at hv
  nlinarith

/-- A concrete two-receiver instance meets every hypothesis of `block_frontier`: edges
`0,1` belong to receiver `0`, edges `2,3` to receiver `1`; a modular value (`η = 0`); prefix
`{0, 2}`; a per-block feasible `T = {1, 3}`. -/
theorem block_hypotheses_satisfiable :
    ∃ (f : Finset (Fin 4) → ℝ) (w : Fin 4 → ℝ) (blk : Fin 4 → Fin 2) (P T : Finset (Fin 4)),
      ScoreLocal f w 0 ∧ (∀ b, (part blk T b).card = (part blk P b).card) ∧
      (∀ e ∈ P, ∀ e' ∉ P, blk e = blk e' → w e' ≤ w e) ∧ T ≠ P := by
  refine ⟨fun S => S.sum (fun e => if e = 0 ∨ e = 2 then (1 : ℝ) else 0),
    fun e => if e = 0 ∨ e = 2 then 1 else 0, fun e => if e.val < 2 then 0 else 1, {0, 2}, {1, 3},
    ?_, ?_, ?_, by decide⟩
  · intro A i hi
    simp [Finset.sum_insert hi]
  · intro b; fin_cases b <;> decide
  · intro e he e' he' _
    simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
    rcases he with rfl | rfl <;> simp [he']

end CIGAMF.P13.MarlBlockFrontier

#print axioms CIGAMF.P13.MarlBlockFrontier.block_path
#print axioms CIGAMF.P13.MarlBlockFrontier.block_frontier
#print axioms CIGAMF.P13.MarlBlockFrontier.block_zero_price
#print axioms CIGAMF.P13.MarlBlockFrontier.block_hypotheses_satisfiable
