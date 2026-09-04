# D6 strict-margin candidate — legacy provenance note

Status: **LEGACY / NOT USED TO FALSIFY THE UNIVERSAL BOUND**.

An earlier source-local reproduction produced a rational Fin-6 candidate with
selected set `{0,1,2}`, rejected spans `9/10`, selected spans `1`,
`delta_square = 1`, and reported losses `67/20` and `1/2`.  That result was
subsequently superseded by the authoritative active-cell LP discovery
artifact, whose recorded search has `any_counterexample = false` and whose
best verified Fin-6 cell saturates Gamma `= 5 = m - 1`.

Consequently:

- no Lean theorem in the active branch uses the earlier candidate;
- it does not mark the universal balanced route as falsified;
- it is retained only to document the provenance discrepancy;
- promotion would require exact Lean validation against the same pinned
  scientific semantics and the original generating artifact.

The exact source-local rational vector and cell metadata are preserved in
`D6_STRICT_MARGIN_SOURCE_LOCAL_CANDIDATE_20260902.json`; preservation is not
certification.

The active result is formalized in
`LeanD6Fin6GammaFiveSaturationV1.lean`.
