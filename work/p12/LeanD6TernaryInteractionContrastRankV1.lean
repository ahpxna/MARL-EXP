import Mathlib
import «LeanD6NormalizedBalancedTernaryCounterexampleV1»
import «LeanD6InteractionContrastProfileV1»
import «LeanD6InteractionContrastRankOneV1»

/-!
# Exact rank-at-least-two interaction-profile witness

This module evaluates the centered profiles of the compiled normalized ternary
D6 counterexample.  The determinant is computed from the literal finite world
definition, not from the external LP search that discovered it.
-/

namespace CIGAMF.P13.D6TernaryInteractionContrastRank

open CIGAMF.V4.ProductMixedDifference
open CIGAMF.P13.D6InteractionContrastProfile
open CIGAMF.P13.D6InteractionContrastRankOne
open CIGAMF.P13.D6NormalizedBalancedTernaryCounterexample

def ternaryProfileContextX : Fin 4 → Fin 3 := a4t 0 0 0 1
def ternaryProfileContextY : Fin 4 → Fin 3 := a4t 0 0 2 1

private theorem update_a4t_coordinate_zero
    (a b c d u : Fin 3) :
    Function.update (a4t a b c d) 0 u = a4t u b c d := by
  funext j
  fin_cases j <;> simp [a4t, Function.update, Fin.mk.injEq]

private theorem profile_0_1_at_x :
    interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
      0 0 1 ternaryProfileContextX = -1 := by
  unfold interactionContrastProfile
  change ternaryBalancedWorld4 (Function.update (a4t 0 0 0 1) 0 1) -
      ternaryBalancedWorld4 (Function.update (a4t 0 0 0 1) 0 0) -
      (productResponse pointMassTernary4 ternaryBalancedWorld4 0 1 -
        productResponse pointMassTernary4 ternaryBalancedWorld4 0 0) = -1
  rw [update_a4t_coordinate_zero, update_a4t_coordinate_zero]
  simp only [ternaryBalanced_response_table]
  norm_num [ternaryProfileContextX, ternaryBalancedWorld4,
    ternaryResponseTable4]

private theorem profile_0_2_at_x :
    interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
      0 0 2 ternaryProfileContextX = 0 := by
  unfold interactionContrastProfile
  change ternaryBalancedWorld4 (Function.update (a4t 0 0 0 1) 0 2) -
      ternaryBalancedWorld4 (Function.update (a4t 0 0 0 1) 0 0) -
      (productResponse pointMassTernary4 ternaryBalancedWorld4 0 2 -
        productResponse pointMassTernary4 ternaryBalancedWorld4 0 0) = 0
  rw [update_a4t_coordinate_zero, update_a4t_coordinate_zero]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [ternaryBalanced_response_table]
  norm_num [ternaryProfileContextX, ternaryBalancedWorld4,
    ternaryResponseTable4, h20, h21]

private theorem profile_0_1_at_y :
    interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
      0 0 1 ternaryProfileContextY = 0 := by
  unfold interactionContrastProfile
  change ternaryBalancedWorld4 (Function.update (a4t 0 0 2 1) 0 1) -
      ternaryBalancedWorld4 (Function.update (a4t 0 0 2 1) 0 0) -
      (productResponse pointMassTernary4 ternaryBalancedWorld4 0 1 -
        productResponse pointMassTernary4 ternaryBalancedWorld4 0 0) = 0
  rw [update_a4t_coordinate_zero, update_a4t_coordinate_zero]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [ternaryBalanced_response_table]
  norm_num [ternaryProfileContextY, ternaryBalancedWorld4,
    ternaryResponseTable4, h20, h21]

private theorem profile_0_2_at_y :
    interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
      0 0 2 ternaryProfileContextY = 1 := by
  unfold interactionContrastProfile
  change ternaryBalancedWorld4 (Function.update (a4t 0 0 2 1) 0 2) -
      ternaryBalancedWorld4 (Function.update (a4t 0 0 2 1) 0 0) -
      (productResponse pointMassTernary4 ternaryBalancedWorld4 0 2 -
        productResponse pointMassTernary4 ternaryBalancedWorld4 0 0) = 1
  rw [update_a4t_coordinate_zero, update_a4t_coordinate_zero]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [ternaryBalanced_response_table]
  norm_num [ternaryProfileContextY, ternaryBalancedWorld4,
    ternaryResponseTable4, h20, h21]

theorem ternaryBalancedWorld4_coordinate_zero_profile_determinant :
    interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
        0 0 1 ternaryProfileContextX *
      interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
        0 0 2 ternaryProfileContextY -
      interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
        0 0 1 ternaryProfileContextY *
      interactionContrastProfile pointMassTernary4 ternaryBalancedWorld4
        0 0 2 ternaryProfileContextX = -1 := by
  rw [profile_0_1_at_x, profile_0_2_at_y,
    profile_0_1_at_y, profile_0_2_at_x]
  norm_num

theorem ternaryBalancedWorld4_coordinate_zero_not_rank_one :
    ¬ InteractionContrastRankOne pointMassTernary4 ternaryBalancedWorld4 0 0 := by
  apply interactionContrastProfile_determinant_obstruction
    (u := (1 : Fin 3)) (v := (2 : Fin 3))
    (x := ternaryProfileContextX) (y := ternaryProfileContextY)
  rw [ternaryBalancedWorld4_coordinate_zero_profile_determinant]
  norm_num

/-- The normalized ternary falsifier has at least two independent centered
interaction directions; its third action label is not a merely redundant
encoding of a binary profile. -/
theorem ternaryBalancedWorld4_has_interaction_contrast_rank_ge_two :
    ¬ InteractionContrastRankOne pointMassTernary4 ternaryBalancedWorld4 0 0 :=
  ternaryBalancedWorld4_coordinate_zero_not_rank_one

end CIGAMF.P13.D6TernaryInteractionContrastRank
