import Mathlib
import «LeanStructuralPrefixCoverDimensionV1»

/-!
# Minimum transversal prefix width

The epsilon-optimal sets form a layered subposet of the Boolean lattice.
Prefix-cover dimension does not cover every point of that poset: it first
chooses a transversal hitting every cardinality layer, then covers that
transversal by maximal Boolean-lattice chains (prefixes of full rankings).

This file proves the exact bounded form of that statement.  The object called
`TransversalPrefixWidthAtMost` is the chain-cover-number formulation.  The
separate identification with maximum-antichain width is precisely the finite
Dilworth step and is not assumed here.
-/

namespace CIGAMF.P13.StructuralMinimumTransversalWidth

open CIGAMF.V4.StructuralRankability
open CIGAMF.P13.StructuralPrefixCoverDimension

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The layered epsilon-optimal-set poset, represented by its finite carrier.
The order is ordinary finset inclusion. -/
noncomputable def EpsilonOptimalPoset (objective : Finset I → ℝ) (eps : ℝ) :
    Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S ↦
    EpsilonOptimalAt objective eps S.card S

theorem mem_epsilonOptimalPoset_iff
    (objective : Finset I → ℝ) (eps : ℝ) (S : Finset I) :
    S ∈ EpsilonOptimalPoset objective eps ↔
      EpsilonOptimalAt objective eps S.card S := by
  simp [EpsilonOptimalPoset]

/-- A finite subfamily of the epsilon-optimal poset that hits every budget
layer.  Only one member of each layer is required. -/
def IsLayerTransversal (objective : Finset I → ℝ) (eps : ℝ)
    (X : Finset (Finset I)) : Prop :=
  X ⊆ EpsilonOptimalPoset objective eps ∧
    ∀ k, k ≤ Fintype.card I →
      ∃ S ∈ X, EpsilonOptimalAt objective eps k S

/-- One full ranking realizes a family when every member is the prefix whose
length is that member's cardinality.  Such a family is automatically an
inclusion chain. -/
def RankingRealizes (ranking : List I) (X : Finset (Finset I)) : Prop :=
  IsFullRanking ranking ∧
    ∀ S ∈ X, prefixSet ranking S.card = S

/-- `X` is covered by at most `K` maximal prefix chains.  This is the
chain-cover-number presentation of its Boolean-poset width. -/
def PrefixChainWidthAtMost (X : Finset (Finset I)) (K : ℕ) : Prop :=
  ∃ menu : Finset (List I), menu.card ≤ K ∧
    (∀ ranking ∈ menu, IsFullRanking ranking) ∧
    ∀ S ∈ X, ∃ ranking ∈ menu,
      prefixSet ranking S.card = S

/-- There is a layer transversal whose prefix-chain cover number is at most
`K`. -/
def TransversalPrefixWidthAtMost
    (objective : Finset I → ℝ) (eps : ℝ) (K : ℕ) : Prop :=
  ∃ X : Finset (Finset I),
    IsLayerTransversal objective eps X ∧ PrefixChainWidthAtMost X K

/-- The epsilon-optimal prefixes contributed by a particular ranking menu.
This is the canonical transversal used in the forward implication. -/
noncomputable def menuTransversal (objective : Finset I → ℝ) (eps : ℝ)
    (menu : Finset (List I)) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S ↦
    EpsilonOptimalAt objective eps S.card S ∧
      ∃ ranking ∈ menu, prefixSet ranking S.card = S

theorem menuTransversal_mem
    (objective : Finset I → ℝ) (eps : ℝ)
    (menu : Finset (List I)) (S : Finset I) :
    S ∈ menuTransversal objective eps menu ↔
      EpsilonOptimalAt objective eps S.card S ∧
        ∃ ranking ∈ menu, prefixSet ranking S.card = S := by
  simp [menuTransversal]

theorem prefixCover_gives_layer_transversal
    (objective : Finset I → ℝ) (eps : ℝ)
    (menu : Finset (List I))
    (hCover : PrefixCover objective eps menu) :
    IsLayerTransversal objective eps
      (menuTransversal objective eps menu) := by
  constructor
  · intro S hS
    rw [menuTransversal_mem] at hS
    rw [mem_epsilonOptimalPoset_iff]
    exact hS.1
  · intro k hk
    rcases hCover.2.2 k hk with ⟨ranking, hrank, hopt⟩
    let S := prefixSet ranking k
    have hcard : S.card = k := by
      exact CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
        ranking (hCover.2.1 ranking hrank) k hk
    refine ⟨S, ?_, hopt⟩
    rw [menuTransversal_mem]
    refine ⟨?_, ranking, hrank, ?_⟩
    · simpa [hcard] using hopt
    · simpa [S, hcard]

theorem prefixCover_gives_prefix_chain_cover
    (objective : Finset I → ℝ) (eps : ℝ)
    (menu : Finset (List I)) (K : ℕ)
    (hCard : menu.card ≤ K)
    (hCover : PrefixCover objective eps menu) :
    PrefixChainWidthAtMost (menuTransversal objective eps menu) K := by
  refine ⟨menu, hCard, hCover.2.1, ?_⟩
  intro S hS
  exact (menuTransversal_mem objective eps menu S).1 hS |>.2

/-- Forward half of S3: any `K`-ranking prefix cover canonically selects a
layer transversal of prefix-chain width at most `K`. -/
theorem prefix_dimension_implies_transversal_width
    (objective : Finset I → ℝ) (eps : ℝ) (K : ℕ) :
    PrefixCoverDimensionAtMost objective eps K →
      TransversalPrefixWidthAtMost objective eps K := by
  rintro ⟨menu, hCard, hCover⟩
  exact ⟨menuTransversal objective eps menu,
    prefixCover_gives_layer_transversal objective eps menu hCover,
    prefixCover_gives_prefix_chain_cover objective eps menu K hCard hCover⟩

/-- Reverse half of S3: a transversal covered by `K` maximal prefix chains
already supplies a `K`-ranking prefix cover. -/
theorem transversal_width_implies_prefix_dimension
    (objective : Finset I → ℝ) (eps : ℝ) (K : ℕ) :
    TransversalPrefixWidthAtMost objective eps K →
      PrefixCoverDimensionAtMost objective eps K := by
  rintro ⟨X, hTrans, menu, hCard, hFull, hRealize⟩
  refine ⟨menu, hCard, ?_⟩
  refine ⟨?_, hFull, ?_⟩
  · rcases hTrans.2 0 (Nat.zero_le _) with ⟨S, hSX, hOpt⟩
    rcases hRealize S hSX with ⟨ranking, hRanking, hPrefix⟩
    exact ⟨ranking, hRanking⟩
  · intro k hk
    rcases hTrans.2 k hk with ⟨S, hSX, hOpt⟩
    rcases hRealize S hSX with ⟨ranking, hRanking, hPrefix⟩
    refine ⟨ranking, hRanking, ?_⟩
    have hcard : S.card = k := hOpt.1
    rw [← hcard]
    rw [hPrefix]
    simpa [hcard] using hOpt

/-- Exact bounded form of the proposed S3 identity.  Equality of the two
finite minima follows extensionally from this equivalence for every `K`. -/
theorem S3_prefix_dimension_iff_minimum_transversal_prefix_width
    (objective : Finset I → ℝ) (eps : ℝ) (K : ℕ) :
    PrefixCoverDimensionAtMost objective eps K ↔
      TransversalPrefixWidthAtMost objective eps K := by
  exact ⟨prefix_dimension_implies_transversal_width objective eps K,
    transversal_width_implies_prefix_dimension objective eps K⟩

/-- Minimum feasible number of prefix chains.  `sInf` avoids attaching an
irrelevant decidability choice to the mathematical value. -/
noncomputable def prefixDimensionValue
    (objective : Finset I → ℝ) (eps : ℝ) : ℕ :=
  sInf {K : ℕ | PrefixCoverDimensionAtMost objective eps K}

/-- Minimum transversal prefix-chain width. -/
noncomputable def minimumTransversalPrefixWidth
    (objective : Finset I → ℝ) (eps : ℝ) : ℕ :=
  sInf {K : ℕ | TransversalPrefixWidthAtMost objective eps K}

/-- Literal equality of the two minimum values.  The bounded predicates are
extensionally equal, so no separate minimizer construction is needed here. -/
theorem S3_minimum_values_equal
    (objective : Finset I → ℝ) (eps : ℝ) :
    prefixDimensionValue objective eps =
      minimumTransversalPrefixWidth objective eps := by
  unfold prefixDimensionValue minimumTransversalPrefixWidth
  congr 1
  ext K
  exact S3_prefix_dimension_iff_minimum_transversal_prefix_width
    objective eps K

/-- Every family realized by one ranking is an inclusion chain. -/
theorem rankingRealizes_is_inclusion_chain
    (ranking : List I) (X : Finset (Finset I))
    (h : RankingRealizes ranking X) :
    ∀ A ∈ X, ∀ B ∈ X, A ⊆ B ∨ B ⊆ A := by
  intro A hA B hB
  have hA' := h.2 A hA
  have hB' := h.2 B hB
  rcases le_total A.card B.card with hcard | hcard
  · left
    rw [← hA', ← hB']
    intro x hx
    have hp : ranking.take A.card <+: ranking.take B.card :=
      List.take_prefix_take_left hcard
    have hxList : x ∈ ranking.take A.card := by
      simpa [prefixSet] using hx
    have : x ∈ ranking.take B.card := hp.subset hxList
    simpa [prefixSet] using this
  · right
    rw [← hA', ← hB']
    intro x hx
    have hp : ranking.take B.card <+: ranking.take A.card :=
      List.take_prefix_take_left hcard
    have hxList : x ∈ ranking.take B.card := by
      simpa [prefixSet] using hx
    have : x ∈ ranking.take A.card := hp.subset hxList
    simpa [prefixSet] using this

/-- Ordinary finite-poset antichain predicate for inclusion. -/
def IsInclusionAntichain (A : Finset (Finset I)) : Prop :=
  ∀ S ∈ A, ∀ T ∈ A, S ⊆ T → S = T

/-- Maximum-antichain width is at most `K`, expressed without selecting a
maximum antichain. -/
def InclusionWidthAtMost (X : Finset (Finset I)) (K : ℕ) : Prop :=
  ∀ A : Finset (Finset I), A ⊆ X → IsInclusionAntichain A → A.card ≤ K

private theorem sets_realized_by_same_ranking_comparable
    (ranking : List I) (A B : Finset I)
    (hA : prefixSet ranking A.card = A)
    (hB : prefixSet ranking B.card = B) :
    A ⊆ B ∨ B ⊆ A := by
  rcases le_total A.card B.card with hcard | hcard
  · left
    rw [← hA, ← hB]
    intro x hx
    have hp : ranking.take A.card <+: ranking.take B.card :=
      List.take_prefix_take_left hcard
    have hxList : x ∈ ranking.take A.card := by
      simpa [prefixSet] using hx
    simpa [prefixSet] using hp.subset hxList
  · right
    rw [← hA, ← hB]
    intro x hx
    have hp : ranking.take B.card <+: ranking.take A.card :=
      List.take_prefix_take_left hcard
    have hxList : x ∈ ranking.take B.card := by
      simpa [prefixSet] using hx
    simpa [prefixSet] using hp.subset hxList

/-- Any cover by `K` prefix chains bounds the ordinary antichain width by
`K`.  The converse is the finite Dilworth-plus-chain-extension step. -/
theorem prefixChainWidthAtMost_implies_inclusionWidthAtMost
    (X : Finset (Finset I)) (K : ℕ)
    (hCover : PrefixChainWidthAtMost X K) :
    InclusionWidthAtMost X K := by
  classical
  rcases hCover with ⟨menu, hMenuCard, hFull, hRealize⟩
  intro A hAX hAnti
  let chosen : Finset I → List I := fun S ↦
    if hS : S ∈ A then
      Classical.choose (hRealize S (hAX hS))
    else []
  have hChosenMem : ∀ S ∈ A, chosen S ∈ menu := by
    intro S hS
    simp only [chosen, dif_pos hS]
    exact (Classical.choose_spec (hRealize S (hAX hS))).1
  have hChosenPrefix : ∀ S ∈ A,
      prefixSet (chosen S) S.card = S := by
    intro S hS
    simp only [chosen, dif_pos hS]
    exact (Classical.choose_spec (hRealize S (hAX hS))).2
  have hInjective : (A : Set (Finset I)).InjOn chosen := by
    intro S hS T hT hEq
    have hSPrefix := hChosenPrefix S hS
    have hTPrefix := hChosenPrefix T hT
    rw [hEq] at hSPrefix
    rcases sets_realized_by_same_ranking_comparable
        (chosen T) S T hSPrefix hTPrefix with hST | hTS
    · exact hAnti S hS T hT hST
    · exact (hAnti T hT S hS hTS).symm
  exact (Finset.card_le_card_of_injOn chosen
    (fun S hS ↦ hChosenMem S hS) hInjective).trans hMenuCard

/-- Consequently S3's prefix width always dominates the minimum transversal
ordinary width.  Equality with maximum-antichain width additionally uses
finite Dilworth and the fact that every Boolean-lattice chain extends to a
full ranking. -/
theorem prefix_dimension_gives_transversal_ordinary_width
    (objective : Finset I → ℝ) (eps : ℝ) (K : ℕ)
    (h : PrefixCoverDimensionAtMost objective eps K) :
    ∃ X : Finset (Finset I),
      IsLayerTransversal objective eps X ∧ InclusionWidthAtMost X K := by
  rcases prefix_dimension_implies_transversal_width objective eps K h with
    ⟨X, hTrans, hWidth⟩
  exact ⟨X, hTrans,
    prefixChainWidthAtMost_implies_inclusionWidthAtMost X K hWidth⟩

/-- A pairwise-incomparable family of forced layer representatives gives a
lower bound on every prefix cover.  This is the reusable combinatorial core
for constructing growing `chi_prefix` families: the realization problem is
separated from the antichain obstruction. -/
theorem forced_antichain_lower_bound
    (objective : Finset I → ℝ) (eps : ℝ)
    (A : Finset (Finset I)) (K : ℕ)
    (hAnti : IsInclusionAntichain A)
    (hForced : ∀ S ∈ A,
      EpsilonOptimalAt objective eps S.card S ∧
        ∀ T, EpsilonOptimalAt objective eps S.card T → T = S)
    (hCover : PrefixCoverDimensionAtMost objective eps K) :
    A.card ≤ K := by
  classical
  rcases hCover with ⟨menu, hMenuCard, hNonempty, hFull, hLayers⟩
  let chosen : Finset I → List I := fun S ↦
    if hS : S ∈ A then
      Classical.choose (hLayers S.card (Finset.card_le_univ S))
    else []
  have hChosenMem : ∀ S ∈ A, chosen S ∈ menu := by
    intro S hS
    simpa [chosen, hS] using
      (Classical.choose_spec
        (hLayers S.card (Finset.card_le_univ S))).1
  have hChosenPrefix : ∀ S ∈ A,
      prefixSet (chosen S) S.card = S := by
    intro S hS
    have hOpt := (Classical.choose_spec
      (hLayers S.card (Finset.card_le_univ S))).2
    have hUnique := (hForced S hS).2
    have hOpt' : EpsilonOptimalAt objective eps S.card
        (prefixSet (chosen S) S.card) := by
      simpa [chosen, hS] using hOpt
    exact hUnique _ hOpt'
  have hInjective : (A : Set (Finset I)).InjOn chosen := by
    intro S hS T hT hEq
    have hSPrefix := hChosenPrefix S hS
    have hTPrefix := hChosenPrefix T hT
    rw [hEq] at hSPrefix
    rcases sets_realized_by_same_ranking_comparable
        (chosen T) S T hSPrefix hTPrefix with hST | hTS
    · exact hAnti S hS T hT hST
    · exact (hAnti T hT S hS hTS).symm
  exact (Finset.card_le_card_of_injOn chosen
    (fun S hS ↦ hChosenMem S hS) hInjective).trans hMenuCard

end CIGAMF.P13.StructuralMinimumTransversalWidth
