# Actual experiment run check — 2026-08-29

These are **development smoke executions of real runners**, not unit-test evidence and not paper results. They exist to verify that the refactored code actually executes end-to-end and writes semantically typed artifacts.

## Deterministic / synthetic chain runners

Executed directly from a clean extraction of the packaged repository:

- B/H exact lab: 120 worlds, 0 violations.
- R/P reference + PAIRWISE lab: 120 worlds, 0 violations.
- A functional lab: 400 replicates per configured run; plugin-C bias increased from unique-extrema to near-tie to exact-null regimes, while D bias stayed near zero. Same-budget targeted D allocation had lower theoretical variance than uniform allocation.
- Reference-fidelity search: 500 kernels, 0 harness failures.
- Structural rankability quick search: 415 processed worlds; observed both scalar-prefix-rankable and non-rankable patterns.
- Primitive-world query semantic lab: PASS.
- F3 paired-shadow runner: PASS as `PLUMBING_SMOKE_ONLY`; not learned-policy evidence.
- Omni clone-state joint oracle bridge: 36 requested cells, 1 executed-support cell at the sampled state; nonrectangular executed support detected. This is a plumbing diagnostic, not a scientific prevalence claim.
- `python scripts/run_new_chain_suite.py --quick`: PASS from direct script invocation after packaging bootstrap fix.

## Actual MARL / episode-based executions

### H1 mini, seed 3001, 2 training episodes

Command used `scripts.run_h1_calibration` with `plugin_eps005`, 2 proxy-training episodes, 2 evaluation states, max 8 steps, development thresholds.

Observed:

- run completed and immutable run/summary artifacts were written;
- scientific claim gate: **False**;
- actions seen: 12 / 13;
- action-coverage gate: **False**;
- cross-fit estimator: `fitted=False`;
- unavailable cross-fit metrics remain `NaN`, not numeric zero;
- `dr_requested=False`, `dr_estimator_applied=False`, while `dr_integrity_gate_pass=True` for the plugin arm.

### H1 mini, seed 3002, 5 training episodes

Command used 5 proxy-training episodes, 3 evaluation states and max 12 steps.

Observed:

- run completed;
- scientific claim gate: **False**;
- actions seen: 13 / 13;
- action-coverage gate: **True**;
- support-poor rows still 45 / 45 in this tiny run;
- cross-fit remains not fitted and unavailable metrics remain `NaN`.

These numbers are not scientific evidence; they show that the training/evaluation/artifact path works and that gates fail closed at tiny budgets.

### Paper-B matched-budget mini execution

Executed one pretraining episode and one end-to-end episode on OmniArena with one seed, 5 agents, core budget 1, 2 selector states, 2 independent oracle replicas, `Oracle-C-Core` and `Random-Core`.

The runner completed and wrote `summary_paper_b_allocation.csv`.

A real runtime bug was found and fixed before this successful run: supplying `--variants` without `Full-Explicit` caused selector isolation to fail because the code used `Full-Explicit` as a neutral fidelity reference but only instantiated user-requested variants. `Full-Explicit` is now included internally as the neutral reference without forcing it into the reported variant list.

A second usability guard was added: `--agent-count < 5` now fails at argument validation for the current single-zone OmniArena P2-role contract instead of reaching an environment assertion.

## Packaging bug found and fixed

New chain runners initially worked as `python -m scripts.<runner>` but direct execution such as:

```bash
python scripts/run_chain_bh_lab.py ...
```

failed with `ModuleNotFoundError` because the repository root was not on `sys.path`.

All new chain entry points now bootstrap the repository root and support both invocation forms.

## Interpretation

This check establishes **runtime/plumbing readiness**, not theorem truth, novelty, or confirmatory scientific success. Fresh Lean verification remains blocked in this runtime because Lean/lake is not installed. F3 still lacks a production learned-CIG-AMF shadow-learner adapter.
