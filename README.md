# CIG-AMF

The active development portfolio now contains **six scientific reports**:
MASTER, Functional, Support, Structural, D6, and Query. Historical Paper-A /
Paper-B runners remain in the repository for provenance, but they are not the
current portfolio entry point.

Use `CURRENT_SIX_REPORTS_RUNBOOK.md` and
`config/CURRENT_SIX_REPORT_TEST_PLAN.json` for the current claim-to-test map.
The one-command local validation entry point is:

```bash
python scripts/run_current_six_report_validation.py --profile quick
```

The validation path is deliberately fail-closed. A green local suite does not
stand in for unavailable external capabilities, disjoint-seed confirmatory
evidence, or open formal theorems. In particular, the unrestricted normalized
D6 `m-1` law is historical/falsified; the current live D6 program adversarially
tests the rank-one restricted replacement conjecture.

## First checks

```bash
python -m pip install -r requirements.txt
python -m compileall -q .
python -m pytest -q
python smoke_test.py
python test_bc_loss_control.py
```

For the full protocol and artifact-generation order, read `RUN_GUIDE.md`.

## External benchmark status

External adapters are capability-gated.  A benchmark is not counted as causal
validation unless its adapter exposes the operations required by that claim
(e.g. clone/restore plus the relevant intervention oracle).  Do not reinterpret
an unavailable capability as a negative experimental result.

External repositories are centralized under `external_envs/repos/` and are
resolved through `envs.external.registry`.  Use `scripts/setup_external_envs.sh`
and `scripts/external_env_manager.py status` rather than adding ad-hoc
`sys.path` entries or cloning benchmark copies elsewhere in the project.

### Python environments for external benchmarks

Pinned external benchmarks are intentionally isolated from the main CIG-AMF
environment. Run `scripts/setup_external_envs.sh --install` with Python 3.12;
the managed runtime lives at `external_envs/runtime/` and external runners
switch to it automatically. See `RUN_GUIDE.md` for macOS commands.

### External benchmark isolation

Pinned Flatland, RWARE, CybORG and CityFlow checkouts live under
`external_envs/repos/` and execute through the isolated
`external_envs/runtime/` environment. This keeps benchmark-specific dependency
constraints out of the main CIG-AMF Python environment and prevents third-party
test suites from being collected by the project's `pytest` run. See
`RUN_GUIDE.md` for setup and verification commands.
