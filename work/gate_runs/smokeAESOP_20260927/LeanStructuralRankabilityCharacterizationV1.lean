import Mathlib
import «LeanStructuralRankabilityV4»
import «LeanAuxiliaryBH6StructuralV4»
import «LeanStructuralGeometryWitnessesV4»

/-! Generic nested-chain scaffolding for scalar-prefix rankability.

The definition records the common ranking that realizes the chain.  This makes
the equivalence below an exact interface theorem between the existing
`ScalarPrefixRankable` predicate and cardinality-optimal nested prefixes.  It is
not presented as a new characterization of the CIG-AMF support-radius class.

Finite discovery accompanying this module rejected the tested specialized
submodular, supermodular, exchange, accessibility, and extrema-compatibility
candidate characterizations; consequently no `SR1` iff is asserted here. -/

namespace CIGAMF.V7.StructuralRankabilityCharacterization

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralRankability
open CIGAMF.V4.AuxiliaryBH6Structural

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def CardinalityOptimal
    (objective : Finset ι → ℝ) (S : Finset ι) (k : ℕ) : Prop :=
  S.card = k ∧ ∀ T : Finset ι, T.card = k → objective S ≤ objective T

def NestedOptimalChain (objective : Finset ι → ℝ) : Prop :=
  ∃ ranking : List ι,
    IsFullRanking ranking ∧
    (∀ k, k ≤ Fintype.card ι →
      CardinalityOptimal objective (prefixSet ranking k) k) ∧
    (∀ k, k < Fintype.card ι →
      prefixSet ranking k ⊂ prefixSet ranking (k + 1))

private theorem ranking_prefix_strict
    (ranking : List ι) (hfull : IsFullRanking ranking)
    (k : ℕ) (hk : k < Fintype.card ι) :
    prefixSet ranking k ⊂ prefixSet ranking (k + 1) := by
  have hsubset := prefixSet_nested ranking k
  have hk0 : k ≤ Fintype.card ι := Nat.le_of_lt hk
  have hk1 : k + 1 ≤ Fintype.card ι := Nat.succ_le_iff.mpr hk
  have hcard0 := prefixSet_card_of_full ranking hfull k hk0
  have hcard1 := prefixSet_card_of_full ranking hfull (k + 1) hk1
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, by
    intro heq
    have := congrArg Finset.card heq
    rw [hcard0, hcard1] at this
    omega⟩

theorem SR0_scalarPrefix_iff_nestedOptimalChain
    (objective : Finset ι → ℝ) :
    ScalarPrefixRankable objective ↔ NestedOptimalChain objective := by
  constructor
  · rintro ⟨ranking, hfull, hoptimal⟩
    refine ⟨ranking, hfull, ?_, ?_⟩
    · intro k hk
      exact ⟨prefixSet_card_of_full ranking hfull k hk, hoptimal k hk⟩
    · intro k hk
      exact ranking_prefix_strict ranking hfull k hk
  · rintro ⟨ranking, hfull, hoptimal, _hnested⟩
    refine ⟨ranking, hfull, ?_⟩
    intro k hk S hcard
    exact (hoptimal k hk).2 S hcard

theorem SR0_selectedRadius_scalarPrefix_iff_nestedOptimalChain
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : ι → Ω → ℝ) :
    ScalarPrefixRankable (selectedRadius f) ↔
      NestedOptimalChain (selectedRadius f) :=
  SR0_scalarPrefix_iff_nestedOptimalChain (selectedRadius f)

end CIGAMF.V7.StructuralRankabilityCharacterization
