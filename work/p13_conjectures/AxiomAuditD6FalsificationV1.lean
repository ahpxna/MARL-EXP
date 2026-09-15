import «LeanD6StrictTwoProfileRankOneM6CounterexampleV2»

open CIGAMF.P13.D6StrictTwoProfileRankOneM6CounterexampleV2

/- The two falsification statements. -/
#print axioms witness_rankOne_constant_five_false
#print axioms strict_twoProfile_rankOne_m6_violates_m_minus_one

/- The HYPOTHESES of D6, proved for this witness rather than assumed.
   A refutation is only a refutation if the premises actually hold. -/
#print axioms cornerQ6_nonnegative
#print axioms cornerQ6_normalized
#print axioms witnessWorld_unitInteraction
#print axioms witness_allCoordinatesRankOne
#print axioms witness_atMostTwoProfiles
#print axioms witness_strictTopC
#print axioms witness_balanced
#print axioms witness_cell_valid
#print axioms witness_rankOneNormalizedBalanced

/- The exact arithmetic the violation rests on. -/
#print axioms witness_response_spans
#print axioms witness_selected_loss
#print axioms witness_competitor_loss
#print axioms witness_doubled_gap
#print axioms witness_violates_five
