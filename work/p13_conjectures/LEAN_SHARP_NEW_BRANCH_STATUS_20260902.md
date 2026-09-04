# CIG-AMF sharp-programme new branch status — 2026-09-02

This branch preserves the PAEC/Abel/cycle files as historical proof routes.
No legacy theorem was weakened or deleted.  The files below implement the
new uniform decision-cell and transversal formulations.

## D6 decision--interaction complexity

| Result | Status | Source |
|---|---|---|
| Fixed active decision cell and exact linear decision functional | COMPILED ZERO-SORRY | `LeanD6ActiveDecisionCellV1.lean` |
| Uniform functional certificate and soundness | COMPILED ZERO-SORRY | `LeanD6UniformDecisionCertificateV1.lean` |
| Literal `kappaDI` as a supremum over all admissible worlds in one cell | COMPILED ZERO-SORRY | `LeanD6DecisionInteractionComplexityV1.lean` |
| Uniform certificate mass upper-bounds `kappaDI` | COMPILED ZERO-SORRY | `LeanD6DecisionInteractionComplexityV1.lean` |
| `kappaDI <= m-1` outside balanced-complement cells | COMPILED ZERO-SORRY | `LeanD6DecisionInteractionComplexityV1.lean` |
| Odd coordinate-count corollary | COMPILED ZERO-SORRY | `LeanD6DecisionInteractionComplexityV1.lean` |
| All-cell theorem reduces exactly to balanced-complement cells | COMPILED ZERO-SORRY | `LeanD6DecisionInteractionComplexityV1.lean` |
| Legacy unnormalised `BalancedDecisionInteractionBound` | FALSIFIED EXACTLY | `LeanD6BalancedLawCounterexampleV1.lean`; the counterexample has joint reference mass four |
| `kappaDI <= m-1` for every balanced-complement cell under nonnegative normalized product weights | OPEN BLOCKER | precisely stated in `LeanD6NormalizedBalancedTargetV1`; compiled equivalence shows this is the only missing normalized all-cell branch |
| Global equality/sharpness `sup_cell kappaDI = m-1` | OPEN | requires a uniform sharp family |

The old instance-wise `paecAtomicMass` has also been audited.  With arbitrary
real coefficients on one already-observed numerical world it equals the
normalized observed positive decision gap whenever a nonzero cycle is
available; if the certificate set is empty, real `sInf` also returns zero.
Therefore it remains a sound legacy certificate API but is not used as the
new complexity definition.

## Product-expectation bridge

| Result | Status | Source |
|---|---|---|
| Product response mean equals product baseline from global normalization alone | COMPILED ZERO-SORRY | `LeanD6ResidualGlobalNormV1.lean` |
| One-path residual update equals an actual product-weighted cycle sum | COMPILED ZERO-SORRY | `LeanD6BalancedProductCoreScratchV1.lean` |
| Exact signed two-endpoint path identity | COMPILED ZERO-SORRY | `LeanD6BalancedProductCoreScratchV1.lean` |
| Crude `2 * card * delta` bound for the two paths | COMPILED ZERO-SORRY | `LeanD6BalancedProductCoreScratchV1.lean` |
| One-free-unit aggregate splice | OPEN BLOCKER | `OneFreeProductCycleSplice` is defined but not assumed |

This closes the requested numerical two-path/product-expectation layer without
claiming the still-open balanced sharp theorem.

## Structural prefix-cover formulation

| Result | Status | Source |
|---|---|---|
| Exact prefix dimension = minimum layer-transversal prefix-chain cover number | COMPILED ZERO-SORRY | `LeanStructuralMinimumTransversalWidthV1.lean` |
| Prefix-chain cover implies the ordinary antichain-width bound | COMPILED ZERO-SORRY | same |
| Forced unique-optimum antichain lower bound | COMPILED ZERO-SORRY | same |
| `supportOsc`/`selectedRadius` is a finite maximum of modular pair-scenario functions | COMPILED ZERO-SORRY | `LeanStructuralSupportOscMaxModularV1.lean` |
| Actual five-relation supportOsc witness has prefix dimension at least three | COMPILED ZERO-SORRY | `LeanStructuralActualTransversalChi3V1.lean` |
| Actual seven-relation, two-support-point supportOsc witness has prefix dimension at least five | COMPILED ZERO-SORRY | `LeanStructuralScalarChi5WitnessV1.lean` |
| Equality with ordinary poset width via Dilworth | OPEN | requires finite Dilworth plus extension of Boolean chains to rankings |
| Unbounded/growing actual supportOsc family | COMPILED ZERO-SORRY | `LeanStructuralStaircaseFamilyV1`, `LeanStructuralStaircaseUnboundedV1`, and `LeanStructuralUnboundedPrefixCoverFamilyV1` prove `chi_prefix(F_r,0) >= r` for every `r > 0` using actual finite support/component functions |

The exact theorem deliberately uses prefix-chain cover number.  It does not
rename that object as ordinary width without proving the missing Dilworth and
ranking-extension bridge.

## Legacy routes retained

PAEC existence, canonical PAEC, Abel/surplus, cycle atoms, one-free-unit,
martingale/gauge, and historical counterexample modules remain in
`work/p13_conjectures/`.  They are dependencies or audit lineage, not the
novelty claim of this new branch.

## Typed obstruction branch

The generic TCC theorem is now instantiated by exact finite CIG witnesses for
all five declared types: response/score, reference, support,
first-order-versus-interaction, and query semantics.  The query instance uses
the existing zero/interacting worlds: their complete pairwise-response
summaries coincide while their interaction-query targets are four units apart,
so no response-summary controller is uniformly unit-accurate on both worlds.
The response/score instance uses two actual finite response surfaces whose
unique capacity-maximizing relation is reversed while all non-response
evidence is held fixed.

Structural elimination adapters are separated from necessity witnesses:
zero mixed differences make `F = productA q F`; co-extremizability makes the
support deficit zero; strict covered score-interval separation establishes
the exact Top-K relation; exact reference invariance yields zero reference
error.  These are conditions under which obligations disappear, not claims
that the corresponding evidence types are generally interchangeable.
