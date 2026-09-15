import «LeanD6ThresholdConstructionV1»

/-! Fails on any axiom outside the three standard kernel foundations. -/

#print axioms CIGAMF.P13.D6Threshold.corner_normalized
#print axioms CIGAMF.P13.D6Threshold.mixed_bound
#print axioms CIGAMF.P13.D6Threshold.world_response
#print axioms CIGAMF.P13.D6Threshold.actual_loss
#print axioms CIGAMF.P13.D6Threshold.actual_regret
#print axioms CIGAMF.P13.D6Threshold.complement_optimal
#print axioms CIGAMF.P13.D6Threshold.actual_support_bridge
#print axioms CIGAMF.P13.D6Threshold.support_observed_coordinates_equal
#print axioms CIGAMF.P13.D6Threshold.joint_measurement
#print axioms CIGAMF.P13.D6Threshold.randomized_actual_lower
#print axioms CIGAMF.P13.D6Threshold.uniform_family_value
#print axioms CIGAMF.P13.D6Threshold.selected_is_top
#print axioms CIGAMF.P13.D6Threshold.exact_top_gap
#print axioms CIGAMF.P13.D6Threshold.mixed_bound_attained
#print axioms CIGAMF.P13.D6Threshold.response_rule_actual_lower

run_cmd do
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    `CIGAMF.P13.D6Threshold.corner_normalized,
    `CIGAMF.P13.D6Threshold.mixed_bound,
    `CIGAMF.P13.D6Threshold.world_response,
    `CIGAMF.P13.D6Threshold.actual_loss,
    `CIGAMF.P13.D6Threshold.actual_regret,
    `CIGAMF.P13.D6Threshold.complement_optimal,
    `CIGAMF.P13.D6Threshold.actual_support_bridge,
    `CIGAMF.P13.D6Threshold.support_observed_coordinates_equal,
    `CIGAMF.P13.D6Threshold.joint_measurement,
    `CIGAMF.P13.D6Threshold.randomized_actual_lower,
    `CIGAMF.P13.D6Threshold.uniform_family_value,
    `CIGAMF.P13.D6Threshold.selected_is_top,
    `CIGAMF.P13.D6Threshold.exact_top_gap,
    `CIGAMF.P13.D6Threshold.mixed_bound_attained,
    `CIGAMF.P13.D6Threshold.response_rule_actual_lower]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  Lean.logInfo "PASS: all 15 D6 construction headline theorems use only standard axioms."
