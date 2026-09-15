# Contents

- `baseline/`: immutable P12 Lean sources and compiled objects.
- `baseline_archive/`: the supplied final D6 baseline ZIP.
- `extensions/`: P13 source files; only entries with exit code zero and zero
  `sorry` in `ACTIVE_COMPILE_RESULTS_P13.tsv` are verified.
- `search/`: exact and directed D6 falsification artifacts.
- `scripts/`: the exact-search and counterexample-directed optimizer sources.
- `compile_logs/`: Lean compiler and static-scan logs.
- `P13_REDESIGN_STATUS.md`: scientific and formal status.

Quarantined files are intentionally retained for provenance. Their presence in
the ZIP does not make their conjectures verified.
