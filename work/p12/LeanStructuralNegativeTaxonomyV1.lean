import Mathlib
import «LeanStructuralRankabilityCharacterizationV1»
import «LeanStructuralGeometryWitnessesV4»

/-! Final structural pivot: exact finite state-space facts and a compact
negative taxonomy inside the actual `selectedRadius` class.  No new exact iff
characterization is claimed. -/

namespace CIGAMF.V7.StructuralNegativeTaxonomy

open CIGAMF.V4.SupportGeometry
open CIGAMF.V4.StructuralRankability
open CIGAMF.V4.AuxiliaryBH6Structural
open CIGAMF.V4.StructuralGeometryWitnesses

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem SRALG_subset_state_count :
    Fintype.card (Finset ι) = 2 ^ Fintype.card ι := by simp

theorem SRALG_ranking_search_count :
    Fintype.card (Equiv.Perm ι) = Nat.factorial (Fintype.card ι) := by
  exact Fintype.card_perm

/- These three witnesses form the final negative taxonomy:
  W1: a scalar-prefix chain exists but Top-C is wrong;
  W2: Top-C is exact at every budget without global co-extremizability;
  W3: unique optima at adjacent budgets are nonnested, so no prefix exists.
All objectives below are genuine support-radius objectives. -/
theorem STAX_actual_support_radius_three_way_taxonomy :
    (ScalarPrefixRankable (selectedRadius w1F) ∧
      ¬ TopCExactAllBudgets (selectedRadius w1F) w1TopC) ∧
    (TopCExactAllBudgets (selectedRadius antiF) antiTopC ∧
      ¬ GloballyCoextremizable antiF) ∧
    ¬ ScalarPrefixRankable (selectedRadius w3F) := by
  exact ⟨W1_geometry_strictness,
    W2_topC_exact_not_global_coextremizable,
    W3_geometry_not_scalar_prefix_rankable⟩

end CIGAMF.V7.StructuralNegativeTaxonomy
