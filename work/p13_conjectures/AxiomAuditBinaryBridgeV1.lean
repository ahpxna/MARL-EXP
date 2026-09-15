import «LeanD6BinaryBridgeV1»

/-! Axiom audit for the bridge.  Admissible only if nothing appears beyond
[propext, Classical.choice, Quot.sound]; a strict subset is stronger.
`Lean.ofReduceBool` anywhere would mean `native_decide` leaked in. -/

open CIGAMF.P13.D6BinaryBridgeV1

#print axioms CIGAMF.P13.D6BinaryBridgeV1.cornerQ2_nonnegative
#print axioms CIGAMF.P13.D6BinaryBridgeV1.cornerQ2_jointWeight
#print axioms CIGAMF.P13.D6BinaryBridgeV1.cornerQ2_normalized
#print axioms CIGAMF.P13.D6BinaryBridgeV1.cornerQ2_expectation
#print axioms CIGAMF.P13.D6BinaryBridgeV1.cornerQ2_response
#print axioms CIGAMF.P13.D6BinaryBridgeV1.Wr_apply
#print axioms CIGAMF.P13.D6BinaryBridgeV1.rawWorld_update_eq_resp
#print axioms CIGAMF.P13.D6BinaryBridgeV1.resp_zero
#print axioms CIGAMF.P13.D6BinaryBridgeV1.comp_eq_resp
#print axioms CIGAMF.P13.D6BinaryBridgeV1.gSel_eq_residual
#print axioms CIGAMF.P13.D6BinaryBridgeV1.gCom_eq_residual
#print axioms CIGAMF.P13.D6BinaryBridgeV1.md0
#print axioms CIGAMF.P13.D6BinaryBridgeV1.md1
#print axioms CIGAMF.P13.D6BinaryBridgeV1.md2
#print axioms CIGAMF.P13.D6BinaryBridgeV1.md3
#print axioms CIGAMF.P13.D6BinaryBridgeV1.md4
#print axioms CIGAMF.P13.D6BinaryBridgeV1.md5
#print axioms CIGAMF.P13.D6BinaryBridgeV1.rawWorld_mixed_le_seventeen
#print axioms CIGAMF.P13.D6BinaryBridgeV1.residual_selected_bounds
#print axioms CIGAMF.P13.D6BinaryBridgeV1.residual_competitor_bounds
#print axioms CIGAMF.P13.D6BinaryBridgeV1.residual_selected_values
#print axioms CIGAMF.P13.D6BinaryBridgeV1.residual_competitor_values
#print axioms CIGAMF.P13.D6BinaryBridgeV1.response_extremes
#print axioms CIGAMF.P13.D6BinaryBridgeV1.strict_topC_integer
#print axioms CIGAMF.P13.D6BinaryBridgeV1.Wr_response
#print axioms CIGAMF.P13.D6BinaryBridgeV1.Wr_retained_selected
#print axioms CIGAMF.P13.D6BinaryBridgeV1.Wr_retained_competitor
#print axioms CIGAMF.P13.D6BinaryBridgeV1.retained_sel_max_val
#print axioms CIGAMF.P13.D6BinaryBridgeV1.retained_sel_min_val
#print axioms CIGAMF.P13.D6BinaryBridgeV1.retained_com_max_val
#print axioms CIGAMF.P13.D6BinaryBridgeV1.retained_com_min_val
#print axioms CIGAMF.P13.D6BinaryBridgeV1.Wr_unitInteraction
#print axioms CIGAMF.P13.D6BinaryBridgeV1.witness2_balanced
#print axioms CIGAMF.P13.D6BinaryBridgeV1.span_eq
#print axioms CIGAMF.P13.D6BinaryBridgeV1.witness2_cell_valid
#print axioms CIGAMF.P13.D6BinaryBridgeV1.witness2_strictTopC
#print axioms CIGAMF.P13.D6BinaryBridgeV1.witness2_doubled_gap
#print axioms CIGAMF.P13.D6BinaryBridgeV1.witness2_violates_five
#print axioms CIGAMF.P13.D6BinaryBridgeV1.binary_decisionInteraction_constant_five_false
#print axioms CIGAMF.P13.D6BinaryBridgeV1.binary_witness_summary
#print axioms CIGAMF.P13.D6BinaryBridgeV1.Wr_allCoordinatesRawRankOne
#print axioms CIGAMF.P13.D6BinaryBridgeV1.raw_rankOne_does_not_rescue_m_minus_one
