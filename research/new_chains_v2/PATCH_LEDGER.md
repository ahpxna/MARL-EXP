# Patch ledger

## Added package

- `research_chains/contracts.py`
- `research_chains/support.py`
- `research_chains/finite_world.py`
- `research_chains/certificates.py`
- `research_chains/reference.py`
- `research_chains/pairwise.py`
- `research_chains/functionals.py`
- `research_chains/structural.py`
- `research_chains/provenance.py`
- `research_chains/estimation.py`
- `research_chains/oracle.py`
- `research_chains/f3.py`

## Added runners

- `scripts/run_chain_bh_lab.py`
- `scripts/run_chain_rp_lab.py`
- `scripts/run_chain_a_functional_lab.py`
- `scripts/run_chain_structural_search.py`
- `scripts/run_chain_reference_fidelity_search.py`
- `scripts/run_chain_e_semantic_lab.py`
- `scripts/run_chain_f3_shadow_smoke.py`
- `scripts/run_chain_oracle_bridge_omni.py`
- `scripts/run_new_chain_suite.py`

## Legacy hardening

- `models/crossfit_aipw.py`: explicit natural-history target; reject silent frozen/transported use; episode/fold diagnostics.
- `run_experiment.py`: unavailable metrics are no longer encoded as zero; DR application telemetry is separated from protocol integrity.

## Added regression tests

- `tests/test_new_chain_harness.py`
- `tests/test_new_chain_random_labs.py`
- `tests/test_new_chain_extended.py`
- `tests/test_new_chain_legacy_semantics.py`
- `tests/test_new_chain_oracle_adapter.py`

## Runtime experiment hardening after clean-ZIP execution

- All new chain runner scripts now bootstrap the repository root so both `python -m scripts.<runner>` and direct `python scripts/<runner>.py` execution work from a clean checkout/ZIP.
- `scripts/run_paper_b_allocation.py` now always constructs `Full-Explicit` internally as the neutral fidelity reference even when `--variants` requests only a subset. This fixes a real end-to-end runtime failure discovered by a one-episode OmniArena execution.
- `scripts/run_paper_b_allocation.py` now validates `agent_count >= 5` for the current single-zone OmniArena P2-role contract before environment construction.
- Added `research/new_chains_v2/ACTUAL_EXPERIMENT_RUN_CHECK.md` and small development-smoke artifacts under `research/new_chains_v2/actual_runcheck/`.
