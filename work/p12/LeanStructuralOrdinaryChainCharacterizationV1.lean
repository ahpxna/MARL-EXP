import Mathlib
import «LeanStructuralMinimumTransversalWidthV1»

/-!
# Ranking-free chain characterization of prefix-cover dimension

This extension closes the gap deliberately left open in
`LeanStructuralMinimumTransversalWidthV1`: the chain-cover predicate below is
ordinary inclusion comparability and contains no rankings, lists, or prefixes.

The constructive bridge orders ground elements by decreasing membership count
in the supplied Boolean-lattice chain (with an arbitrary deterministic
tiebreaker).  Nestedness makes every member of a chain an initial segment of
that order.
-/

namespace CIGAMF.P13.StructuralOrdinaryChainCharacterization

open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension
open CIGAMF.P13.StructuralMinimumTransversalWidth

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A ranking-free finite inclusion chain in the Boolean lattice. -/
def InclusionChain (C : Finset (Finset I)) : Prop :=
  ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A

/-- A ranking-free cover by at most `K` inclusion chains. -/
def InclusionChainCoverAtMost (X : Finset (Finset I)) (K : ℕ) : Prop :=
  ∃ cover : Finset (Finset (Finset I)),
    cover.card ≤ K ∧
      (∀ C ∈ cover, InclusionChain C) ∧
      ∀ S ∈ X, ∃ C ∈ cover, S ∈ C

private def membershipCount (C : Finset (Finset I)) (x : I) : ℕ :=
  (C.filter fun S ↦ x ∈ S).card

private theorem membershipCount_lt_of_mem_notMem
    (C : Finset (Finset I)) (hChain : InclusionChain C)
    (S : Finset I) (hSC : S ∈ C) {x y : I}
    (hx : x ∈ S) (hy : y ∉ S) :
    membershipCount C y < membershipCount C x := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro T hT
    simp only [Finset.mem_filter] at hT ⊢
    refine ⟨hT.1, ?_⟩
    rcases hChain S hSC T hT.1 with hST | hTS
    · exact hST hx
    · exact False.elim (hy (hTS hT.2))
  · intro hEq
    have hxFilter : S ∈ C.filter fun T ↦ x ∈ T := by
      simp [hSC, hx]
    have hyFilter : S ∉ C.filter fun T ↦ y ∈ T := by
      simp [hy]
    exact hyFilter (hEq ▸ hxFilter)

private theorem sorted_prefix_eq_of_cross_lt
    (ranking : List I) (hFull : IsFullRanking ranking)
    (S : Finset I)
    (r : I → I → Prop) [DecidableRel r]
    (hPair : ranking.Pairwise r)
    (hCross : ∀ x ∈ S, ∀ y ∉ S, ¬ r y x) :
    prefixSet ranking S.card = S := by
  classical
  have hCard : (prefixSet ranking S.card).card = S.card :=
    CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
      ranking hFull S.card (Finset.card_le_univ S)
  apply Finset.eq_of_subset_of_card_le ?_ (by simpa [hCard])
  intro y hyPrefix
  by_contra hyS
  have hNotSubset : ¬ S ⊆ prefixSet ranking S.card := by
    intro hSubset
    have hEq := Finset.eq_of_subset_of_card_le hSubset (by omega)
    exact hyS (hEq ▸ hyPrefix)
  rcases Set.not_subset.mp hNotSubset with ⟨x, hxS, hxNotPrefix⟩
  have hyTake : y ∈ ranking.take S.card := by
    simpa [prefixSet] using hyPrefix
  have hxRanking : x ∈ ranking := by
    have : x ∈ ranking.toFinset := by simpa [hFull.2] using (Finset.mem_univ x)
    simpa using this
  have hyRanking : y ∈ ranking := by
    have : y ∈ ranking.toFinset := by simpa [hFull.2] using (Finset.mem_univ y)
    simpa using this
  have hxNotTake : x ∉ ranking.take S.card := by
    simpa [prefixSet] using hxNotPrefix
  have hyIdx : ranking.idxOf y < S.card :=
    (List.mem_take_iff_idxOf_lt hyRanking).1 hyTake
  have hxIdx : S.card ≤ ranking.idxOf x := by
    exact Nat.le_of_not_gt (fun h ↦ hxNotTake
      ((List.mem_take_iff_idxOf_lt hxRanking).2 h))
  have hIdx : ranking.idxOf y < ranking.idxOf x := lt_of_lt_of_le hyIdx hxIdx
  let iy : Fin ranking.length :=
    ⟨ranking.idxOf y, List.idxOf_lt_length_of_mem hyRanking⟩
  let ix : Fin ranking.length :=
    ⟨ranking.idxOf x, List.idxOf_lt_length_of_mem hxRanking⟩
  have hRel : r (ranking.get iy) (ranking.get ix) := by
    apply hPair.rel_get_of_lt
    exact hIdx
  have hGetY : ranking.get iy = y := by
    simpa [iy] using
      (List.idxOf_get (List.idxOf_lt_length_of_mem hyRanking))
  have hGetX : ranking.get ix = x := by
    simpa [ix] using
      (List.idxOf_get (List.idxOf_lt_length_of_mem hxRanking))
  rw [hGetY, hGetX] at hRel
  exact hCross x hxS y hyS hRel

/-- Every finite nested Boolean-lattice chain is simultaneously realized by
prefixes of one full permutation.  This is the missing ranking-free bridge. -/
theorem finite_inclusion_chain_extends_to_full_ranking
    (C : Finset (Finset I)) (hChain : InclusionChain C) :
    ∃ ranking : List I, IsFullRanking ranking ∧
      ∀ S ∈ C, prefixSet ranking S.card = S := by
  classical
  let base : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let key : I → (ℕ ×ₗ Fin (Fintype.card I)) := fun x ↦
    toLex (C.card - membershipCount C x, base x)
  have hKey : Function.Injective key := by
    intro x y h
    exact base.injective (Prod.mk.inj (toLex.injective h)).2
  letI : LinearOrder I := LinearOrder.lift' key hKey
  let ranking : List I := Finset.univ.sort (fun x y : I ↦ x ≤ y)
  have hFull : IsFullRanking ranking := by
    constructor
    · exact Finset.sort_nodup _ _
    · exact Finset.sort_toFinset _ _
  refine ⟨ranking, hFull, ?_⟩
  intro S hSC
  apply sorted_prefix_eq_of_cross_lt ranking hFull S (fun x y : I ↦ x ≤ y)
    (Finset.pairwise_sort _ _)
  intro x hx y hy
  have hCount := membershipCount_lt_of_mem_notMem C hChain S hSC hx hy
  have hxBound : membershipCount C x ≤ C.card := Finset.card_filter_le _ _
  have hyBound : membershipCount C y ≤ C.card := Finset.card_filter_le _ _
  have hKeyLt : key x < key y := by
    rw [show key x = toLex (C.card - membershipCount C x, base x) by rfl,
      show key y = toLex (C.card - membershipCount C y, base y) by rfl,
      Prod.Lex.toLex_lt_toLex]
    left
    omega
  have hxy : x < y := by
    change key x < key y
    exact hKeyLt
  exact not_le_of_gt hxy

private theorem ranking_realizes_chain_from_extension
    (C : Finset (Finset I)) (hC : InclusionChain C) :
    ∃ ranking : List I, RankingRealizes ranking C := by
  rcases finite_inclusion_chain_extends_to_full_ranking C hC with
    ⟨ranking, hFull, hPrefix⟩
  exact ⟨ranking, hFull, hPrefix⟩

theorem prefixChainWidthAtMost_implies_inclusionChainCoverAtMost
    (X : Finset (Finset I)) (K : ℕ)
    (h : PrefixChainWidthAtMost X K) :
    InclusionChainCoverAtMost X K := by
  classical
  rcases h with ⟨menu, hCard, hFull, hRealize⟩
  let chainOf : List I → Finset (Finset I) := fun ranking ↦
    X.filter fun S ↦ prefixSet ranking S.card = S
  let cover := menu.image chainOf
  refine ⟨cover, (Finset.card_image_le.trans hCard), ?_, ?_⟩
  · intro C hC
    rcases Finset.mem_image.mp hC with ⟨ranking, hRanking, rfl⟩
    exact rankingRealizes_is_inclusion_chain ranking (chainOf ranking)
      ⟨hFull ranking hRanking, by simp [chainOf]⟩
  · intro S hSX
    rcases hRealize S hSX with ⟨ranking, hRanking, hPrefix⟩
    refine ⟨chainOf ranking, Finset.mem_image.mpr ⟨ranking, hRanking, rfl⟩, ?_⟩
    simp [chainOf, hSX, hPrefix]

theorem inclusionChainCoverAtMost_implies_prefixChainWidthAtMost
    (X : Finset (Finset I)) (K : ℕ)
    (h : InclusionChainCoverAtMost X K) :
    PrefixChainWidthAtMost X K := by
  classical
  rcases h with ⟨cover, hCard, hChains, hCover⟩
  let rankingOf : Finset (Finset I) → List I := fun C ↦
    if hC : C ∈ cover then
      Classical.choose (ranking_realizes_chain_from_extension C (hChains C hC))
    else []
  let menu := cover.image rankingOf
  refine ⟨menu, Finset.card_image_le.trans hCard, ?_, ?_⟩
  · intro ranking hRanking
    rcases Finset.mem_image.mp hRanking with ⟨C, hC, rfl⟩
    simp only [rankingOf, dif_pos hC]
    exact (Classical.choose_spec
      (ranking_realizes_chain_from_extension C (hChains C hC))).1
  · intro S hSX
    rcases hCover S hSX with ⟨C, hC, hSC⟩
    refine ⟨rankingOf C, Finset.mem_image.mpr ⟨C, hC, rfl⟩, ?_⟩
    simp only [rankingOf, dif_pos hC]
    exact (Classical.choose_spec
      (ranking_realizes_chain_from_extension C (hChains C hC))).2 S hSC

/-- Exact equivalence between the old ranking-defined cover and a genuinely
ranking-free ordinary inclusion-chain cover. -/
theorem prefixChainWidthAtMost_iff_inclusionChainCoverAtMost
    (X : Finset (Finset I)) (K : ℕ) :
    PrefixChainWidthAtMost X K ↔ InclusionChainCoverAtMost X K := by
  exact ⟨prefixChainWidthAtMost_implies_inclusionChainCoverAtMost X K,
    inclusionChainCoverAtMost_implies_prefixChainWidthAtMost X K⟩

/-- The desired ordinary-chain transversal characterization. -/
theorem prefixCoverDimensionAtMost_iff_layerTransversal_inclusionChainCover
    (objective : Finset I → ℝ) (eps : ℝ) (K : ℕ) :
    PrefixCoverDimensionAtMost objective eps K ↔
      ∃ X : Finset (Finset I),
        IsLayerTransversal objective eps X ∧
          InclusionChainCoverAtMost X K := by
  rw [S3_prefix_dimension_iff_minimum_transversal_prefix_width]
  constructor
  · rintro ⟨X, hTrans, hWidth⟩
    exact ⟨X, hTrans,
      prefixChainWidthAtMost_implies_inclusionChainCoverAtMost X K hWidth⟩
  · rintro ⟨X, hTrans, hWidth⟩
    exact ⟨X, hTrans,
      inclusionChainCoverAtMost_implies_prefixChainWidthAtMost X K hWidth⟩

end CIGAMF.P13.StructuralOrdinaryChainCharacterization
