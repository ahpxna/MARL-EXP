import Mathlib
import «LeanD6StrictRankOneM6WitnessV1»
import «LeanStructuralStaircaseExactPrefixCoverV1»
import «LeanD6ProfileFibreAdditiveSteeringV1»
import «LeanD6RankOneReferenceInvarianceV1»
import «LeanD6InteractionContrastRankOneMinorsV1»

/-!
Axiom audit.  A source file with no `sorry` token can still depend on one
through an import, in which case `sorryAx` appears in the axiom list.  The only
acceptable output for every line below is
`[propext, Classical.choice, Quot.sound]` (and NOT `sorryAx`, NOT
`Lean.ofReduceBool` which would indicate `native_decide`).
-/

-- Structural: the exact extremal law
#print axioms CIGAMF.P13.StructuralStaircaseExactPrefixCover.STRUCT_staircase_prefix_cover_at_most_r
#print axioms CIGAMF.P13.StructuralStaircaseExactPrefixCover.STRUCT_staircase_prefix_dimension_eq
#print axioms CIGAMF.P13.StructuralStaircaseExactPrefixCover.STRUCT_staircase_chi_eq_half_ground_set

-- D6: the witness world
#print axioms CIGAMF.P13.D6StrictRankOneM6Witness.cornerQ6_normalized
#print axioms CIGAMF.P13.D6StrictRankOneM6Witness.witnessWorld_allCoordinatesRankOne
#print axioms CIGAMF.P13.D6StrictRankOneM6Witness.witnessWorld_atMostTwoProfiles
#print axioms CIGAMF.P13.D6StrictRankOneM6Witness.witnessWorld_allMinorsZero

-- D6: mechanism and infrastructure
#print axioms CIGAMF.P13.D6ProfileFibreAdditiveSteering.interactionContrastRankOne_same_lambda_implies_additive_difference
#print axioms CIGAMF.P13.D6RankOneReferenceInvariance.interactionContrastRankOne_reference_free
#print axioms CIGAMF.P13.D6InteractionContrastRankOneMinors.interactionContrastRankOne_iff_all_minors_zero
