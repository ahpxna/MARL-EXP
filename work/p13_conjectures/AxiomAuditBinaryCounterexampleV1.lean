import «LeanD6BinaryIntegerCounterexampleV1»

/-!
# Axiom audit: the unconditional binary m = 6 counterexample

Absence of `sorry` does not license the word PROVED in this corpus; an axiom
audit does.  Every theorem of `LeanD6BinaryIntegerCounterexampleV1` is printed
below.  The result is admissible only if EVERY line reads exactly

    [propext, Classical.choice, Quot.sound]

Anything else -- in particular `Lean.ofReduceBool`, which `native_decide` would
introduce -- means the module is NOT axiom-clean and the claim stays at
EXACT_RATIONAL_COUNTEREXAMPLE_INDEPENDENTLY_RECOMPUTED.  The module uses `decide`
over the 2^6 = 64 points precisely so that no such axiom can appear.
-/

open CIGAMF.P13.D6BinaryIntegerCounterexampleV1

#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.osc_table
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.strict_top_three
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gSel_upper
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gSel_lower
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gSel_max_attained
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gSel_min_attained
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gCom_upper
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gCom_lower
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gCom_max_attained
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.gCom_min_attained
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.rho_spreads_le_seventeen
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.rho0_spread_attained
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.doubled_selected_loss
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.doubled_competitor_loss
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.doubled_decision_gap
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.integer_violation
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.rescaled_violation
#print axioms CIGAMF.P13.D6BinaryIntegerCounterexampleV1.exact_ratio
