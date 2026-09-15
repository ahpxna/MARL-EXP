import «LeanD6SameResponseMarginCertificateV1»

/-! Enforcing audit for the same-response minimax chain: loss formula, the
two-action upper strategy, and the equaliser prior lower certificate.
Fails on any axiom outside the three standard kernel foundations. -/

#print axioms CIGAMF.P13.D6SameResponseMarginLoss.common_response
#print axioms CIGAMF.P13.D6SameResponseMarginLoss.mixed_unchanged
#print axioms CIGAMF.P13.D6SameResponseMarginLoss.actual_loss_formula
#print axioms CIGAMF.P13.D6SameResponseMarginGame.actual_regret_formula
#print axioms CIGAMF.P13.D6SameResponseMarginGame.complement_optimal
#print axioms CIGAMF.P13.D6SameResponseMarginGame.actual_two_action_risk
#print axioms CIGAMF.P13.D6SameResponseMarginGame.adversary_equalizer
#print axioms CIGAMF.P13.D6SameResponseMarginGame.mixture_weights_valid
#print axioms CIGAMF.P13.D6SameResponseMarginCertificate.singleton_valid
#print axioms CIGAMF.P13.D6SameResponseMarginCertificate.singleton_average
#print axioms CIGAMF.P13.D6SameResponseMarginCertificate.actual_dual_equalizer
#print axioms CIGAMF.P13.D6SameResponseMarginCertificate.randomized_dual_equalizer

run_cmd do
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let names : Array Lean.Name := #[
    `CIGAMF.P13.D6SameResponseMarginLoss.common_response,
    `CIGAMF.P13.D6SameResponseMarginLoss.mixed_unchanged,
    `CIGAMF.P13.D6SameResponseMarginLoss.actual_loss_formula,
    `CIGAMF.P13.D6SameResponseMarginGame.actual_regret_formula,
    `CIGAMF.P13.D6SameResponseMarginGame.complement_optimal,
    `CIGAMF.P13.D6SameResponseMarginGame.actual_two_action_risk,
    `CIGAMF.P13.D6SameResponseMarginGame.adversary_equalizer,
    `CIGAMF.P13.D6SameResponseMarginGame.mixture_weights_valid,
    `CIGAMF.P13.D6SameResponseMarginCertificate.singleton_valid,
    `CIGAMF.P13.D6SameResponseMarginCertificate.singleton_average,
    `CIGAMF.P13.D6SameResponseMarginCertificate.actual_dual_equalizer,
    `CIGAMF.P13.D6SameResponseMarginCertificate.randomized_dual_equalizer]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
  Lean.logInfo "PASS: all 12 same-response minimax theorems use only standard axioms."
