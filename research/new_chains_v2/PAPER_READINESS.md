# Paper-readiness verdict after code refactor

This file separates code readiness from scientific success.

| Chain | Verdict | Remaining blocker |
|---|---|---|
| B/H certified support geometry | READY_FOR_DEVELOPMENT_EXPERIMENT | Fresh Lean + empirical certificate nonvacuity under structured supports |
| R_iso -> PAIRWISE -> B/H | READY_FOR_DEVELOPMENT_EXPERIMENT | Fresh Lean; statistically certified score/reference/support intervals in learned MARL |
| R_feas | READY_FOR_DEVELOPMENT_EXPERIMENT | Must define a downstream feasible-effect objective before reusing primitive-compression claims |
| Structural rankability | READY_FOR_FORMALIZATION_ONLY | No iff characterization yet; exhaustive m=3 search is theorem-discovery evidence only |
| A functional-specific estimability | READY_FOR_DEVELOPMENT_EXPERIMENT | Main H1 runner still needs explicit frozen-nu* standardization path for that target; natural AIPW is now typed correctly |
| E query benchmark | READY_FOR_DEVELOPMENT_EXPERIMENT | Build larger primitive-world benchmark; current new lab only establishes exact semantic witnesses |
| F3 moving estimand | NOT_READY | Generic paired-shadow API exists but production CIG-AMF learner shadow adapter is not implemented |
| G systems | NOT_READY | Defer until upstream score/certificate chain passes development gates |

No chain is labelled confirmatory-ready by this refactor.

## Clean-ZIP runtime check update — 2026-08-29

Actual experiment runners (not test fixtures) were executed after packaging. B/H, R/P, A, structural, reference-fidelity, E, F3-plumbing, Omni clone-state bridge, H1 mini training, and Paper-B matched-budget mini execution all reached their intended development artifact paths after the runtime fixes recorded in `ACTUAL_EXPERIMENT_RUN_CHECK.md`.

This does not change any chain to confirmatory-ready. H1 mini runs correctly keep the scientific claim gate false; F3 remains plumbing-only; fresh Lean remains unavailable in this runtime.
