import Mathlib

/-!
# The nesting degree: how many revisions the BEST nested order can need

A system of per-budget target sets `O k` (for any set loss, its per-budget optima) and a chain
`C` (the prefix sets of one committed ranking: `C j ⊆ C k` for `j ≤ k`, `|C k| = k`).  The
chain is within `R` revisions of the system at budget `k` when `|C k \ O k| ≤ R`.  This is
pure combinatorics: no loss, no probability.

## WHAT IS PROVED

* `sdiff_le_of_chain` — for `j ≤ k`, `|O j \ O k| ≤ |O j \ C j| + |C k \ O k|`.  With equal
  cardinalities, `|O j \ C j| = |C j \ O j|`, so a chain within `R` revisions at both
  budgets forces `|O j \ O k| ≤ 2R` (`nesting_lower`).
* `two_budget_obstruction` — two disjoint targets `A` (size `t`) and `B` (size `t+1`) at
  consecutive budgets `t`, `t+1` force every chain to need at least `⌈t/2⌉` revisions at
  one of them: `t ≤ 2 · max(|C t \ A|, |C (t+1) \ B|)`.
* `nesting_degree_lower` — on `m` items with `2t + 1 ≤ m`, such a system EXISTS.  Hence the
  best nested order can need `⌈t/2⌉` revisions with `t = ⌊(m−1)/2⌋`, so the nesting degree
  grows linearly in `m`.  The value is `2` at `m = 7`, matching the exhaustive search in
  research/marl_budget/P1_d6_frontier (one revision always suffices for `m ≤ 6`, and fails
  on some system at `m = 7`).
* `chain_distance_le_min` — the trivial upper bound `|C k \ O k| ≤ min(k, m − k)` for any
  chain and any size-`k` target.
* `distance_regret_lower` — for the distance loss `ℓ_k(S) = |S \ O k|`, whose unique
  per-budget optimum is `O k`, the regret of any nested order after `R` revisions is at
  least `⌈t/2⌉ − R` at one of the two budgets.  So the price of nesting has a
  non-degenerate revision frontier for every `m ≥ 7`.

## WHAT THIS DOES NOT ESTABLISH

- The exact nesting degree.  The conjecture `R*(m) = ⌊(m+1)/4⌋` fits `m ≤ 8` in the search.
  The matching upper bound (a chain within `⌊(m+1)/4⌋` of every system) is not proved.
- That the obstruction is realised as the unique optima of a D6 compression loss.  That is
  a separate, exploratory search.
-/

namespace CIGAMF.P13.MarlNestingDegree

open Finset

variable {ι : Type*} [DecidableEq ι]

/-- **Chain transfer.**  `O j \ O k ⊆ (O j \ C j) ∪ (C k \ O k)` whenever `C j ⊆ C k`. -/
theorem sdiff_subset_of_chain (O C : ℕ → Finset ι) (j k : ℕ) (hC : C j ⊆ C k) :
    O j \ O k ⊆ (O j \ C j) ∪ (C k \ O k) := by
  intro x hx
  rcases Finset.mem_sdiff.mp hx with ⟨hxj, hxk⟩
  by_cases hxC : x ∈ C j
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hC hxC, hxk⟩))
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hxj, hxC⟩))

theorem sdiff_le_of_chain (O C : ℕ → Finset ι) (j k : ℕ) (hC : C j ⊆ C k) :
    (O j \ O k).card ≤ (O j \ C j).card + (C k \ O k).card :=
  (Finset.card_le_card (sdiff_subset_of_chain O C j k hC)).trans (Finset.card_union_le _ _)

/-- **The nesting lower bound.**  If a chain is within `R` revisions of the system at budgets
`j ≤ k` (equal sizes at `j`), then `|O j \ O k| ≤ 2R`. -/
theorem nesting_lower (O C : ℕ → Finset ι) (j k R : ℕ) (hC : C j ⊆ C k)
    (hcard : (C j).card = (O j).card)
    (hj : (C j \ O j).card ≤ R) (hk : (C k \ O k).card ≤ R) :
    (O j \ O k).card ≤ 2 * R := by
  have h := sdiff_le_of_chain O C j k hC
  have hc : (O j \ C j).card = (C j \ O j).card := Finset.card_sdiff_comm hcard.symm
  omega

/-- **Two-budget obstruction.**  Disjoint targets `A` (size `t`) at budget `t` and `B` at
budget `t + 1`: every chain needs `⌈t/2⌉` revisions at one of the two budgets. -/
theorem two_budget_obstruction (A B Ct Ct1 : Finset ι) (t : ℕ)
    (hAB : Disjoint A B) (hA : A.card = t) (hCt : Ct.card = t) (hsub : Ct ⊆ Ct1) :
    t ≤ 2 * max (Ct \ A).card (Ct1 \ B).card := by
  classical
  let O : ℕ → Finset ι := fun i => if i = 0 then A else B
  let C : ℕ → Finset ι := fun i => if i = 0 then Ct else Ct1
  have h := nesting_lower O C 0 1 (max (Ct \ A).card (Ct1 \ B).card)
    (by simpa [C] using hsub) (by simp [C, O, hCt, hA])
    (by simp [C, O]) (by simp [C, O])
  have hsd : (A \ B) = A := Finset.sdiff_eq_self_of_disjoint hAB
  simpa [O, hsd, hA] using h

/-- **The nesting degree grows linearly.**  On `m` items with `2t + 1 ≤ m`, there are targets
`A` (size `t`) and `B` (size `t + 1`) such that EVERY chain step `Ct ⊆ Ct1` with `|Ct| = t`
needs `t ≤ 2·max(|Ct \ A|, |Ct1 \ B|)`. -/
theorem nesting_degree_lower (m t : ℕ) (hm : 2 * t + 1 ≤ m) :
    ∃ A B : Finset (Fin m), A.card = t ∧ B.card = t + 1 ∧ Disjoint A B ∧
      ∀ Ct Ct1 : Finset (Fin m), Ct.card = t → Ct ⊆ Ct1 →
        t ≤ 2 * max (Ct \ A).card (Ct1 \ B).card := by
  classical
  obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin m)))
    (n := t) (by simp; omega)
  have hcompl : t + 1 ≤ (Finset.univ \ A).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ,
      Fintype.card_fin, hA]
    omega
  obtain ⟨B, hBsub, hB⟩ := Finset.exists_subset_card_eq (s := Finset.univ \ A) (n := t + 1)
    hcompl
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp (hBsub hxB)).2 hxA
  exact ⟨A, B, hA, hB, hAB, fun Ct Ct1 hCt hsub =>
    two_budget_obstruction A B Ct Ct1 t hAB hA hCt hsub⟩

/-- The trivial upper bound: any chain set of size `k` is within `min(k, m − k)` of any
size-`k` target. -/
theorem chain_distance_le_min (m k : ℕ) (Ck Ok : Finset (Fin m)) (hC : Ck.card = k)
    (hO : Ok.card = k) :
    (Ck \ Ok).card ≤ min k (m - k) := by
  classical
  apply le_min
  · exact hC ▸ Finset.card_le_card Finset.sdiff_subset
  · have hsub : Ck \ Ok ⊆ Okᶜ := by
      intro x hx; exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hx).2
    have := Finset.card_le_card hsub
    rwa [Finset.card_compl, Fintype.card_fin, hO] at this

/-- **A non-degenerate frontier for the price of nesting.**  For the distance loss
`ℓ_k(S) = |S \ O k|`, whose per-budget optimum `O k` has regret zero, take `R` revisions
after the budget is revealed from a chain step `Ct ⊆ Ct1`.  The best revised regret at a
budget is `(|C \ O| − R)₊`, since each revision removes at most one mismatch, and at one of
the two obstruction budgets it is at least `⌈t/2⌉ − R`. -/
theorem distance_regret_lower (m t R : ℕ) (hm : 2 * t + 1 ≤ m) :
    ∃ A B : Finset (Fin m), A.card = t ∧ B.card = t + 1 ∧ Disjoint A B ∧
      ∀ Ct Ct1 : Finset (Fin m), Ct.card = t → Ct ⊆ Ct1 →
        t ≤ 2 * (max ((Ct \ A).card - R) ((Ct1 \ B).card - R) + R) := by
  obtain ⟨A, B, hA, hB, hAB, h⟩ := nesting_degree_lower m t hm
  refine ⟨A, B, hA, hB, hAB, fun Ct Ct1 hCt hsub => ?_⟩
  have h1 := h Ct Ct1 hCt hsub
  have : max (Ct \ A).card (Ct1 \ B).card ≤
      max ((Ct \ A).card - R) ((Ct1 \ B).card - R) + R := by
    rcases le_total (Ct \ A).card (Ct1 \ B).card with hle | hle
    · rw [max_eq_right hle]
      have : (Ct1 \ B).card - R ≤ max ((Ct \ A).card - R) ((Ct1 \ B).card - R) :=
        le_max_right _ _
      omega
    · rw [max_eq_left hle]
      have : (Ct \ A).card - R ≤ max ((Ct \ A).card - R) ((Ct1 \ B).card - R) :=
        le_max_left _ _
      omega
  omega

/-- The obstruction is non-vacuous at `m = 7`: `t = 3`, so every nested order needs `2`
revisions at one budget (`3 ≤ 2·max`). -/
theorem nesting_degree_seven :
    ∃ A B : Finset (Fin 7), A.card = 3 ∧ B.card = 4 ∧ Disjoint A B ∧
      ∀ Ct Ct1 : Finset (Fin 7), Ct.card = 3 → Ct ⊆ Ct1 →
        2 ≤ max (Ct \ A).card (Ct1 \ B).card := by
  obtain ⟨A, B, hA, hB, hAB, h⟩ := nesting_degree_lower 7 3 (by norm_num)
  exact ⟨A, B, hA, hB, hAB, fun Ct Ct1 hCt hsub => by have := h Ct Ct1 hCt hsub; omega⟩

end CIGAMF.P13.MarlNestingDegree

#print axioms CIGAMF.P13.MarlNestingDegree.sdiff_le_of_chain
#print axioms CIGAMF.P13.MarlNestingDegree.nesting_lower
#print axioms CIGAMF.P13.MarlNestingDegree.two_budget_obstruction
#print axioms CIGAMF.P13.MarlNestingDegree.nesting_degree_lower
#print axioms CIGAMF.P13.MarlNestingDegree.chain_distance_le_min
#print axioms CIGAMF.P13.MarlNestingDegree.distance_regret_lower
#print axioms CIGAMF.P13.MarlNestingDegree.nesting_degree_seven
