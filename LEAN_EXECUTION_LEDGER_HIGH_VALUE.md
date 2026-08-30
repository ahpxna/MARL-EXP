# Lean Execution Ledger — High-Value Extensions

Environment:

- Lean: `4.34.0-rc2`, commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`;
- Mathlib: `1f495c611d05d2215058cd77c7897d625bc3b445`;
- platform: `arm64-apple-darwin24.6.0`;
- build mode: fresh source-to-olean compilation in isolated staging directories;
- historical `LeanUnifiedChainsV2.lean`: excluded.

Baseline validation:

- 14 immutable active modules;
- 199 theorem declarations (`194 theorem` plus `5 private theorem`);
- every baseline module exit code 0;
- four prior V7 extension modules exit code 0;
- full records and source/olean SHA256: `ACTIVE_COMPILE_RESULTS_V7.tsv`.

High-value validation:

| Module | Exit |
|---|---:|
| LeanMasterReferenceUncertaintyV1 | 0 |
| LeanD6SharpnessV1 | 0 |
| LeanD6WeightedInteractionV1 | 0 |
| LeanQueryRepresentationNecessityV1 | 0 |
| LeanReferenceIdentifiabilityV1 | 0 |
| LeanFunctionalCovarianceDesignV1 | 0 |
| LeanStructuralNegativeTaxonomyV1 | 0 |

Exact durations and source/olean SHA256 are in `HIGH_VALUE_COMPILE_RESULTS.tsv`; stdout/stderr is retained under `compile_logs/high_value/`.

Static gate across the 14 baseline modules, four prior extensions, and seven high-value extensions:

```text
sorry = 0
admit = 0
user axiom = 0
```

The zero-line scan output is retained at `compile_logs/high_value/static_gate.txt`.
