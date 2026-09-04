import Mathlib
import «LeanD6InteractionContrastAnchorInvarianceV1»
import «LeanD6ContrastRankPhaseDefinitionsV2»
import «LeanD6StrictMarginTernaryCounterexampleV1»
import «LeanD6TernaryInteractionContrastRankV1»

namespace CIGAMF.P13.D6StrictMarginRankNonOneCounterexample

open scoped BigOperators
open CIGAMF.P13.D6ActiveDecisionCell
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6InteractionContrastAnchorInvariance
open CIGAMF.P13.D6ContrastRankPhaseDefinitionsV2
open CIGAMF.P13.D6StrictMarginTernaryCounterexample
open CIGAMF.P13.D6TernaryInteractionContrastRank
open CIGAMF.P13.D6NormalizedBalancedTernaryCounterexample

theorem strictMarginTernary_coordinate_zero_not_rankOne :
    ¬ InteractionContrastRankOne
      pointMassTernary4 strictMarginWorld 0 0 := by
  apply interactionContrastProfile_determinant_obstruction
    (u := (1 : Fin 3)) (v := (2 : Fin 3))
    (x := ternaryProfileContextX) (y := ternaryProfileContextY)
  have hdet :
      CIGAMF.P13.D6InteractionContrastProfile.interactionContrastProfile
          pointMassTernary4 strictMarginWorld 0 0 1 ternaryProfileContextX *
        CIGAMF.P13.D6InteractionContrastProfile.interactionContrastProfile
          pointMassTernary4 strictMarginWorld 0 0 2 ternaryProfileContextY -
        CIGAMF.P13.D6InteractionContrastProfile.interactionContrastProfile
          pointMassTernary4 strictMarginWorld 0 0 1 ternaryProfileContextY *
        CIGAMF.P13.D6InteractionContrastProfile.interactionContrastProfile
          pointMassTernary4 strictMarginWorld 0 0 2 ternaryProfileContextX = -1 := by
    simp_rw [strictMarginTernary_profile_eq]
    exact ternaryBalancedWorld4_coordinate_zero_profile_determinant
  rw [hdet]
  norm_num

theorem strictMarginTernary_not_allCoordinatesRankOne :
    ¬ AllCoordinatesInteractionContrastRankOne
      pointMassTernary4 strictMarginWorld := by
  intro hAll
  have hCanonical := hAll (0 : Fin 4)
  have hAtZero : InteractionContrastRankOne
      pointMassTernary4 strictMarginWorld 0 0 := by
    exact interactionContrastRankOne_anchor
      pointMassTernary4 strictMarginWorld (0 : Fin 4)
      canonicalInteractionContrastAnchor (0 : Fin 3) hCanonical
  exact strictMarginTernary_coordinate_zero_not_rankOne hAtZero

theorem strictMarginCell_balanced : strictMarginCell.BalancedComplement := by
  change 3 + 1 = 2 * ternarySelected4.card ∧
    Disjoint ternarySelected4 ternaryCompetitor4 ∧
    ternarySelected4 ∪ ternaryCompetitor4 = Finset.univ
  exact ternaryBalancedCell4_balanced

theorem strictMarginTernary_rankNonOne_saturates_three :
    RankNonOneSaturates strictMarginCell 3 := by
  refine ⟨strictMarginWorld, ?_, ?_⟩
  refine ⟨pointMassTernary4_hWeight, pointMassTernary4_hNorm,
    strictMarginCell_balanced, strictMarginTernary_cell_valid,
    strictMarginTernary_delta_le_one,
    strictMarginTernary_not_allCoordinatesRankOne⟩
  change (3 : ℝ) ≤ 2 *
    (CIGAMF.V4.ProductMixedDifference.productCompressionLoss strictMarginWorld
        (CIGAMF.V4.ProductMixedDifference.productResponse pointMassTernary4 strictMarginWorld)
        ternarySelected4 -
      CIGAMF.V4.ProductMixedDifference.productCompressionLoss strictMarginWorld
        (CIGAMF.V4.ProductMixedDifference.productResponse pointMassTernary4 strictMarginWorld)
        ternaryCompetitor4)
  rw [strictMarginTernary_violates_m_minus_one]
  norm_num

theorem strictMarginTernary_strictTopC : StrictTopC strictMarginCell strictMarginWorld := by
  exact strictMarginTernary_is_strict_topC

theorem strictMarginTernary_rankNonOne_violates_three :
    RankNonOneViolates strictMarginCell 3 := by
  refine ⟨strictMarginWorld, ?_, ?_⟩
  refine ⟨pointMassTernary4_hWeight, pointMassTernary4_hNorm,
    strictMarginCell_balanced, strictMarginTernary_cell_valid,
    strictMarginTernary_delta_le_one,
    strictMarginTernary_not_allCoordinatesRankOne⟩
  change (3 : ℝ) < 2 *
    (CIGAMF.V4.ProductMixedDifference.productCompressionLoss strictMarginWorld
        (CIGAMF.V4.ProductMixedDifference.productResponse pointMassTernary4 strictMarginWorld)
        ternarySelected4 -
      CIGAMF.V4.ProductMixedDifference.productCompressionLoss strictMarginWorld
        (CIGAMF.V4.ProductMixedDifference.productResponse pointMassTernary4 strictMarginWorld)
        ternaryCompetitor4)
  rw [strictMarginTernary_violates_m_minus_one]
  norm_num

theorem strictMarginTernary_strict_rankNonOne_violates_three :
    StrictRankNonOneViolates strictMarginCell 3 := by
  refine ⟨strictMarginWorld, ?_, strictMarginTernary_strictTopC, ?_⟩
  refine ⟨pointMassTernary4_hWeight, pointMassTernary4_hNorm,
    strictMarginCell_balanced, strictMarginTernary_cell_valid,
    strictMarginTernary_delta_le_one,
    strictMarginTernary_not_allCoordinatesRankOne⟩
  change (3 : ℝ) < 2 *
    (CIGAMF.V4.ProductMixedDifference.productCompressionLoss strictMarginWorld
        (CIGAMF.V4.ProductMixedDifference.productResponse pointMassTernary4 strictMarginWorld)
        ternarySelected4 -
      CIGAMF.V4.ProductMixedDifference.productCompressionLoss strictMarginWorld
        (CIGAMF.V4.ProductMixedDifference.productResponse pointMassTernary4 strictMarginWorld)
        ternaryCompetitor4)
  rw [strictMarginTernary_violates_m_minus_one]
  norm_num

end CIGAMF.P13.D6StrictMarginRankNonOneCounterexample
