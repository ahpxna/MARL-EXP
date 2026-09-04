# CIG-AMF novelty-critical Lean handoff

## Scope and immutable baseline

This handoff adds P13/quarantine extensions only. It does **not** modify the
frozen P12/D6 baseline or relabel any existing unresolved P13 conjecture as
proved.

Pinned build environment:

- Lean `4.34.0-rc2`
- Mathlib `1f495c611d05d2215058cd77c7897d625bc3b445`
- compiler: `/private/tmp/cig-amf-lean-v7-runtime/lean-dist/lean-4.34.0-rc2-darwin_aarch64/bin/lean`

The reproducible batch command is:

```bash
cd /Users/phanan/cig-amf-main
bash compile_logs/run_novelty_critical_batch.sh
```

It independently recompiles each listed source and replaces its `.olean` only
after a successful compile.

## Actual CIG results added in this handoff

| Module | Status | Hard result |
|---|---|---|
| `LeanD6FirstOrderInsufficiencyWitnessV2` | COMPILED ZERO-SORRY | Full singleton D6-B7: complete first-order product-response tables agree across two worlds, yet **all** zero-regret singleton decisions are disjoint; no deterministic response-only singleton controller is universal. |
| `LeanD6PAECCostAwareAdapterV1` | COMPILED ZERO-SORRY | Connects real `HasPAECForPair` / `cycleFunctional` objects to Cost-Aware PAEC interval certificates. Measured cycle intervals safely bound the actual compression gap. |
| `LeanD6PAECCanonicalWitnessesV1` | COMPILED ZERO-SORRY | Constructs actual PAEC witnesses of mass 3 (`m=4`) and mass 5 (`m=6`) for the compiled canonical point-mass/binary branches; also derives the Fin4 correction order from Top-C under its stated negative-row branch. |
| `LeanSupportCompressionCriticalWitnessV1` | COMPILED ZERO-SORRY | Actual support-compression witness: two supports differ only in cell `2`, their zero-regret decision sets are disjoint, and a controller observing `erase 2` cannot be universally zero-regret. |
| `LeanSupportCompressionCriticalWitnessTighteningV1` | COMPILED ZERO-SORRY | Strengthens the actual witness: for every `eps < 1/2`, cell `2` is necessary, `{2}` is sufficient, and the exact finite membership-query minimum is one. |
| `LeanTCCReferenceSeparationV1` | COMPILED ZERO-SORRY | Actual reference-identifiability separation: identical observed reference rows need not support universal Top-1 reference decisions. |
| `LeanTCCActualSeparationsV1` | COMPILED ZERO-SORRY | Packages the actual reference, support, and interaction separations: these evidence types are not interchangeable. |
| `LeanStructuralPrefixCoverWitnessesV1` | COMPILED ZERO-SORRY | Actual CIG support-radius witness with exact `chi_prefix(0) = 2`: two prefix rankings suffice and no single ranking covers every exact budget. |
| `LeanStructuralPrefixCoverChi3WitnessV1` | COMPILED CANDIDATE-DATA / OPEN | Stores an exact finite `m=5` candidate for a `chi_prefix(0) >= 3` search. It deliberately makes no lower-bound claim. |
| `LeanStructuralPrefixCoverChi3ProofAttemptV1` | COMPILED ZERO-SORRY / OPEN DIAGNOSTIC | Isolates the remaining `m=5` proof work to finite table normalisation and 26 strict-comparison obligations; it deliberately makes no `chi >= 3` claim. |

### B7: full singleton interaction necessity

`D6_B7_full_singleton_response_only_not_universally_zero_regret` is the
scientific statement to cite. It has three formally connected layers:

1. `firstOrderResponses_equal`: every coordinate/action entry of the complete
   first-order product-response table agrees;
2. `D6_B7_full_singleton_opposite_strict_ordering`: the two worlds have
   opposite strict compression ordering, including the third singleton;
3. `D6_B7_full_singleton_zero_good_decisions_disjoint` plus TCC-2 rules out
   every deterministic controller whose output is any singleton in `Fin 3`.

Thus the result has no “perhaps choose singleton 2” loophole. It is a finite
exact necessity result: first-order responses alone cannot universally certify
the D6 singleton compression decision.

### PAEC: real-object Cost-Aware specialization

The adapter proves:

```text
HasPAECForPair -> exists ValidCertificate
                 (atomValue r = cycleFunctional ... F)
measured cycle intervals -> actual compression gap <= PAEC robust bound
robust bound <= epsilon -> actual compression gap <= epsilon
```

The relevant theorems are `hasPAEC_to_validCertificate`,
`hasPAEC_measured_cycle_intervals_sound`, and
`hasPAEC_cycle_interval_stop_safe`.

This is intentionally **conditional** on a supplied valid PAEC certificate.
It does not smuggle in the unresolved universal theorem.

`canonical_fin4_hasPAEC` and `canonical_fin6_hasPAEC` additionally certify
the two symbolic canonical branches as real `HasPAECForPair` witnesses. They
are not a relabeling theorem: arbitrary `q`, arbitrary action domains, and
arbitrary active extrema cannot be reduced to those binary point-mass branches
from Top-C ordering alone.

### Typed Certificate Completion now has actual separations

`TCC_actual_evidence_types_not_interchangeable` combines three exact CIG
instantiations of the generic TCC-2 impossibility theorem:

- insufficient observed reference rows for a reference-derived Top-1 target;
- insufficient support evidence when the decision-critical support cell is
  hidden;
- insufficient complete first-order product responses for the interaction
  compression target.

This is stronger than typed enums alone: there are concrete worlds where a
missing evidence semantic cannot be silently substituted by another one.

### Structural result and its honest boundary

`STRUCT_W3_prefix_cover_dimension_exact_two` proves an actual CIG
`selectedRadius` instance has exactly two required prefix chains at zero
tolerance. The `m=5` file is only a compiled candidate encoding; the finite
radius/uniqueness obligations needed for `chi_prefix(0) >= 3` are still open.
No growing-family claim is made.

The support witness is also now quantitative within its finite two-world
setting: `actual_support_witness_minimum_query_cardinality` proves that the
membership-query complexity is exactly one for every `eps < 1/2`; this is an
actual `radiusOn` compression statement, not a generic arbitrary-regret
specialization.

## Existing zero-sorry infrastructure retained

| Module | Status | Content |
|---|---|---|
| `LeanTypedCertificateCompletionV1` | COMPILED ZERO-SORRY | typed discharge, completion safety, TCC-2 indistinguishability, finite minimum-cost completion |
| `LeanD6CostAwarePAECCompletionV1` | COMPILED ZERO-SORRY | robust interval evaluation, best valid certificate, refinement, cost/width minimizers, switching soundness |
| `LeanFunctionalSelectiveMaintenanceV1` | COMPILED ZERO-SORRY | selective refresh safety, monotonicity, finite minimum-cost refresh, dependency locality |
| `LeanSupportCriticalIdentificationV1` | COMPILED ZERO-SORRY | generic critical-cell/separating-set/finite-minimum support-evidence framework |
| `LeanQueryIdentifiabilityVerifierV1` | COMPILED ZERO-SORRY | finite verifier, witness-producing insufficiency, three-state status, quantitative lower-bound API |
| `LeanStructuralPrefixCoverDimensionV1` | COMPILED ZERO-SORRY | exact definitions, `chi=1` nested-chain characterization, tolerance monotonicity |
| `LeanD6FirstOrderInsufficiencyWitnessV1` | COMPILED ZERO-SORRY | restricted two-decision precursor; superseded scientifically by V2, retained as provenance |

## Open blockers — unchanged and not weakened

| Target | Status | Why it remains open |
|---|---|---|
| Arbitrary Top-C pair `-> HasPAECForPair` | OPEN BLOCKER | The current PAEC existence module only supplies a conditional interface. |
| Universal D6 half-factor | OPEN BLOCKER | `LeanD6DecisionHalfFactorConjecture.lean` still contains its quarantined headline `sorry`. |
| `chi_prefix(0) >= 3` / growing family | OPEN | Candidate data are present, but no proof or claim exists. |
| Reference-response budget law | OPEN | Its two quarantined `sorry` obligations remain. |
| all-optimal-extension structural bound | OPEN | Its placeholder theorem remains quarantined and is not used by these results. |

## Static integrity

The compiled extension sources in this handoff have zero `sorry`, zero
`admit`, and zero user `axiom`. Archive-wide P13 still intentionally contains
the four quarantined proof holes listed above; they are not part of any
“COMPILED ZERO-SORRY” claim here.

## Compile logs

Per-module successful logs:

- `compile_logs/d6_first_order_insufficiency_v2_fix2.log`
- `compile_logs/d6_paec_cost_aware_adapter_v1.log`
- `compile_logs/support_compression_critical_witness_fix3.log`
- `compile_logs/actual_hard_additions_batch.log` (the support-tightening and
  structural diagnostic modules pass; its first PAEC-canonical attempt records
  the fixed source-level errors before the final recompile)
- `compile_logs/tcc_reference_separation_fix2.log`
- `compile_logs/tcc_actual_separations_fix2.log`
- `compile_logs/structural_prefix_cover_witnesses_v1.log`
- `compile_logs/structural_prefix_cover_chi3_candidate_v1.log`

## Fresh expanded batch evidence

The expanded independent batch completed with **exit code 0** on 2026-09-01:

```text
14 modules compiled / 14 modules passed / 0 Lean errors
```

The exact command is `bash compile_logs/run_novelty_critical_batch.sh`; its
fresh `bash -x` output is retained as
`compile_logs/novelty_critical_batch_expanded.log`. The source and `.olean`
SHA-256 manifest is `compile_logs/novelty_critical_batch_sha256.txt`.

The subsequent actual-hard-additions batch also completed with **exit code 0**:

```text
LeanD6PAECCanonicalWitnessesV1                 PASS
LeanSupportCompressionCriticalWitnessTighteningV1 PASS
LeanStructuralPrefixCoverChi3ProofAttemptV1    PASS
```

Its command and exact output are retained in
`compile_logs/run_actual_hard_additions_batch.sh` and
`compile_logs/actual_hard_additions_batch_final.log`.
