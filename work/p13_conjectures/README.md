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
