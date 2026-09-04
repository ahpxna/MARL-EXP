# P13 quarantined conjectures

These files are intentionally **not** part of the active verified Lean build.
They are a theorem-discovery queue. `sorry` is permitted here only so that a
strong scientific conjecture can be stated before proof engineering is funded.

Promotion rule:

1. finite/exact and adversarial falsification must not find a counterexample;
2. theorem statement must be checked against the current P12 semantics;
3. replace every `sorry` with a proof;
4. compile in the pinned Lean/Mathlib environment;
5. only then copy the proved theorem into `work/p12` and add it to the active ledger.

Experiments can **falsify, prioritize, or stress** these conjectures. They never
turn a `sorry` into a universal proof.

`LeanFunctionalUnknownVarianceConjecture.lean` is a historical filename: its
three deterministic robustness theorems now contain zero `sorry` and fresh
compile under the pinned runtime. It remains quarantined until the active
ledger/promotion gate is updated and does not certify an acquisition policy.

`LeanReferenceResponseTopKBudgetConjecture.lean` is the only new P13 bridge in
the redesign batch.  Its conditional Top-K wrapper is compiled with zero
`sorry`; the statistical coverage premise and the 2/3-power allocation optimum
remain separate open dependencies and are not proved by that wrapper.
