import Mathlib
import «LeanStructuralRankabilityV4»
import «LeanStructuralRankabilityCharacterizationV1»

/-!
# Prefix-cover dimension of the layered epsilon-optimal-set poset

This file formalizes the exact finite cover predicate and its relation to the
earlier ranking-menu language.  It does not invoke ordinary chain-cover or
Dilworth results: only one epsilon-optimal set per budget layer must be hit.
-/

namespace CIGAMF.P13.StructuralPrefixCoverDimension

open CIGAMF.V4.StructuralRankability
open CIGAMF.V7.StructuralRankabilityCharacterization

variable {I : Type*} [Fintype I] [DecidableEq I]

def EpsilonOptimalAt (objective : Finset I → ℝ) (eps : ℝ)
    (k : ℕ) (S : Finset I) : Prop :=
  S.card = k ∧ ∀ T : Finset I, T.card = k →
    objective S ≤ objective T + eps

def PrefixCover (objective : Finset I → ℝ) (eps : ℝ)
    (menu : Finset (List I)) : Prop :=
  menu.Nonempty ∧
    (∀ ranking ∈ menu, IsFullRanking ranking) ∧
    ∀ k, k ≤ Fintype.card I →
      ∃ ranking ∈ menu,
        EpsilonOptimalAt objective eps k (prefixSet ranking k)

/- The old menu language and the prefix-cover language are extensionally the
same finite object. -/
def RankingMenuCovers (objective : Finset I → ℝ) (eps : ℝ)
    (menu : Finset (List I)) : Prop :=
  menu.Nonempty ∧
    (∀ ranking ∈ menu, IsFullRanking ranking) ∧
    ∀ k, k ≤ Fintype.card I →
      ∃ ranking ∈ menu,
        EpsilonOptimalAt objective eps k (prefixSet ranking k)

theorem STRUCT_B1_prefix_cover_iff_ranking_menu
    (objective : Finset I → ℝ) (eps : ℝ) (menu : Finset (List I)) :
    PrefixCover objective eps menu ↔ RankingMenuCovers objective eps menu := by
  rfl

def PrefixCoverDimensionAtMost (objective : Finset I → ℝ)
    (eps : ℝ) (K : ℕ) : Prop :=
  ∃ menu : Finset (List I), menu.card ≤ K ∧ PrefixCover objective eps menu

def RankingMenuComplexityAtMost (objective : Finset I → ℝ)
    (eps : ℝ) (K : ℕ) : Prop :=
  ∃ menu : Finset (List I), menu.card ≤ K ∧
    RankingMenuCovers objective eps menu

theorem STRUCT_B1_dimension_iff_old_menu_complexity
    (objective : Finset I → ℝ) (eps : ℝ) (K : ℕ) :
    PrefixCoverDimensionAtMost objective eps K ↔
      RankingMenuComplexityAtMost objective eps K := by
  simp only [PrefixCoverDimensionAtMost, RankingMenuComplexityAtMost,
    STRUCT_B1_prefix_cover_iff_ranking_menu]

def OnePrefixChain (objective : Finset I → ℝ) (eps : ℝ) : Prop :=
  ∃ ranking : List I, IsFullRanking ranking ∧
    ∀ k, k ≤ Fintype.card I →
      EpsilonOptimalAt objective eps k (prefixSet ranking k)

theorem singleton_prefix_cover_iff_one_prefix_chain
    (objective : Finset I → ℝ) (eps : ℝ) :
    (∃ ranking : List I, PrefixCover objective eps {ranking}) ↔
      OnePrefixChain objective eps := by
  constructor
  · rintro ⟨ranking, hCover⟩
    refine ⟨ranking, hCover.2.1 ranking (by simp), ?_⟩
    intro k hk
    rcases hCover.2.2 k hk with ⟨candidate, hmem, hOptimal⟩
    have hCandidate : candidate = ranking := Finset.mem_singleton.1 hmem
    subst candidate
    exact hOptimal
  · rintro ⟨ranking, hFull, hOptimal⟩
    refine ⟨ranking, ?_⟩
    refine ⟨by simp, ?_, ?_⟩
    · intro candidate hmem
      have hCandidate : candidate = ranking := Finset.mem_singleton.1 hmem
      subst candidate
      exact hFull
    · intro k hk
      exact ⟨ranking, by simp, hOptimal k hk⟩

theorem STRUCT_B2_one_prefix_zero_iff_scalar_prefix
    (objective : Finset I → ℝ) :
    OnePrefixChain objective 0 ↔ ScalarPrefixRankable objective := by
  constructor
  · rintro ⟨ranking, hFull, hOptimal⟩
    refine ⟨ranking, hFull, ?_⟩
    intro k hk S hCard
    have h := (hOptimal k hk).2 S hCard
    linarith
  · rintro ⟨ranking, hFull, hOptimal⟩
    refine ⟨ranking, hFull, ?_⟩
    intro k hk
    refine ⟨CIGAMF.V4.AuxiliaryBH6Structural.prefixSet_card_of_full
      ranking hFull k hk, ?_⟩
    intro S hCard
    have h := hOptimal k hk S hCard
    linarith

theorem STRUCT_B2_chi_one_iff_nested_optimal_chain
    (objective : Finset I → ℝ) :
    OnePrefixChain objective 0 ↔ NestedOptimalChain objective := by
  rw [STRUCT_B2_one_prefix_zero_iff_scalar_prefix]
  exact SR0_scalarPrefix_iff_nestedOptimalChain objective

theorem epsilonOptimal_mono
    (objective : Finset I → ℝ) (eps₁ eps₂ : ℝ)
    (hEps : eps₁ ≤ eps₂) (k : ℕ) (S : Finset I)
    (hOptimal : EpsilonOptimalAt objective eps₁ k S) :
    EpsilonOptimalAt objective eps₂ k S := by
  refine ⟨hOptimal.1, ?_⟩
  intro T hCard
  have hBase := hOptimal.2 T hCard
  linarith

theorem STRUCT_B3_tolerance_monotonicity
    (objective : Finset I → ℝ) (eps₁ eps₂ : ℝ)
    (hEps : eps₁ ≤ eps₂) (K : ℕ)
    (hCover : PrefixCoverDimensionAtMost objective eps₁ K) :
    PrefixCoverDimensionAtMost objective eps₂ K := by
  rcases hCover with ⟨menu, hCard, hMenu⟩
  refine ⟨menu, hCard, hMenu.1, hMenu.2.1, ?_⟩
  intro k hk
  rcases hMenu.2.2 k hk with ⟨ranking, hRanking, hOptimal⟩
  exact ⟨ranking, hRanking,
    epsilonOptimal_mono objective eps₁ eps₂ hEps k _ hOptimal⟩

/- Prefix-cover is a layer-hitting property, not a cover of every member of
the epsilon-optimal-set poset. -/
theorem STRUCT_B4_hits_one_set_per_budget_layer
    (objective : Finset I → ℝ) (eps : ℝ) (menu : Finset (List I))
    (hCover : PrefixCover objective eps menu) :
    ∀ k, k ≤ Fintype.card I →
      ∃ ranking ∈ menu,
        EpsilonOptimalAt objective eps k (prefixSet ranking k) :=
  hCover.2.2

end CIGAMF.P13.StructuralPrefixCoverDimension
