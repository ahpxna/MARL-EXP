# Audit execution ledger

## Executed PASS

- `python -m compileall -q .`
- full pytest after refactor: see final test run; all tests passed.
- `python smoke_test.py`: 35 PASS, 0 FAIL, 0 SKIP.
- `python test_bc_loss_control.py`: T1 PASS, T2a PASS, T2b PASS.
- `bash -n scripts/run_all.sh`
- `bash -n scripts/setup_external_envs.sh`
- B/H exact/random lab: 1,000 worlds, 0 violations.
- R/P exact/random lab: 1,000 worlds, 0 violations.
- A functional lab: 3,000 replicates; near-tie/null plugin-C pathology and D contrast reproduced.
- structural rankability search: exhaustive binary `m=3`, 12,352 nontrivial worlds processed.
- universal reference-fidelity search: 5,000 kernels, 0 characterization-harness failures.
- primitive query semantic lab: PASS.
- existing P11 typed query gates: Q0-Q4 PASS.
- existing P11 Omni D0 quick collector: completed, SMOKE_ONLY.
- F3 paired-shadow harness: PASS as PLUMBING_SMOKE_ONLY.
- OmniArena clone-state joint-oracle bridge: executed; support was strongly nonrectangular in the sampled state (1/36 requested two-source cells executed exactly), demonstrating why executed support must be typed rather than assumed Cartesian.

## BLOCKED / deliberately not claimed

- Fresh Lean verification: `lean`/`lake` unavailable in this runtime.
- F3 learned CIG-AMF evidence: generic shadow interface exists, but no production learner adapter is claimed.
- Confirmatory runs: intentionally not opened.
- External benchmark full training: not run in this refactor pass.
