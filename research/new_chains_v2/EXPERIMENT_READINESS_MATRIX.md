# Experiment readiness matrix

| Chain | Deterministic theory lab | Synthetic/stat lab | Clone-state env bridge | Learned MARL adapter | Fresh Lean | Verdict |
|---|---|---|---|---|---|---|
| B/H certified support geometry | PASS | PASS | PASS (generic support oracle) | PARTIAL | BLOCKED | READY_FOR_DEVELOPMENT_EXPERIMENT |
| R_iso -> PAIRWISE | PASS | PASS | PASS | PARTIAL | BLOCKED | READY_FOR_DEVELOPMENT_EXPERIMENT |
| R_feas | PASS semantics/API | PASS | PASS | PARTIAL | BLOCKED | READY_FOR_DEVELOPMENT_EXPERIMENT |
| Structural rankability | PASS exhaustive m=3 search | N/A | N/A | N/A | BLOCKED | READY_FOR_FORMALIZATION_ONLY |
| A functional-specific estimability | PASS deterministic | PASS 3k rep | existing H1 bridge + new standardization contract | PARTIAL | BLOCKED | READY_FOR_DEVELOPMENT_EXPERIMENT |
| E query semantics | PASS | PASS primitive worlds | existing typed-query runner | existing benchmark adapters | historical only | READY_FOR_DEVELOPMENT_EXPERIMENT |
| F3 moving estimand | PASS plumbing | PASS toy smoke | generic paired-shadow API | NOT_IMPLEMENTED production adapter | BLOCKED | NOT_READY |
| G systems | existing code | existing Paper-B runners | existing | existing | N/A | DEFER_UNTIL_UPSTREAM |
