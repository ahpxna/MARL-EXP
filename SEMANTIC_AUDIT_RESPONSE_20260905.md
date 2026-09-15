# Response to the 2026-09-05 semantic audit

Every finding below was reproduced against the code before it was changed.  A
finding is only listed as CONFIRMED when the defect was exhibited, not merely
read.  The suite was green throughout: none of these were caught by tests, which
is exactly why they needed an audit.

## CONFIRMED and FIXED

### QUERY Bug A -- one evaluability flag gated two different endpoints
`_query_discriminativeness` returned a single `scientific_evaluable`, set to
False for a constant target AND for a tied k/(k+1) boundary.  The aggregate then
filtered on that one flag, so a tied ranking boundary deleted `R_m_to_q`, the
declared PRIMARY endpoint, even though regret is perfectly well defined on a
tied target.  That is a selection bias: it removes exactly the states where
ranking is hard.

Fixed by splitting the gate:

    regret_evaluable   <=> osc(T_q) > tol
    ranking_evaluable  <=> regret_evaluable and TopK boundary gap > tol

`status` and `reason` keep their original values so existing artifacts stay
comparable.  `scientific_evaluable` is retained as the LEGACY STRICT flag
(identical to `ranking_evaluable`) and is documented as not fit to gate the
primary endpoint.

### QUERY Bug B -- the matched-budget mode was advertised but never aggregated
Cells carried both `full_information` and `matched_budget`, and a cell over
budget was marked `METHOD_EXCEEDS_MATCHED_INFORMATION_BUDGET`.  But the
aggregate read the TOP-LEVEL keys, which are the full-information values, so
`benchmark_modes = [full_information_transfer, matched_budget_transfer]` was
half fiction: only `R^full_{m->q}` existed.

Fixed by lifting the aggregation to a module-level, testable
`aggregate_transfer_matrix(state_rows, methods, queries, mode)` and emitting
BOTH `aggregate_transfer_matrix` and `aggregate_transfer_matrix_matched_budget`,
each with its own denominators (`aggregate_denominators_*`), and per-metric
denominators inside every cell: regret metrics over `regret_evaluable` states,
Top-k metrics over `ranking_evaluable` states.

### QUERY Bug C -- the execution receipt verified only the intervened coordinates
`CloneStateJointOracle.evaluate` computed

    verified = all(executed[source] == action for source, action in zip(source_agents, assignment))

so an environment that honours the intervention while overriding some OTHER
agent's baseline action still recorded `execution_verified = True`, although
`F(a_S, a_baseline_{-S})` was never executed.  `_coalition_values` had the same
hole, checking only `candidates`.

Demonstrated on the pre-fix module with a 3-agent environment that honours the
intervention and overrides agent 2:

    PRE-FIX  requested: (1, 1, 1)  executed: (1, 1, 0)  execution_verified = True
    POST-FIX execution_verified = False, execution_verified_sources = True

Fixed: `execution_verified` is now the full-joint check.  The weaker check is
reported separately as `execution_verified_sources`.  A caller that genuinely
wants the loose semantics must construct the oracle with
`execution_semantics="source_only"` -- the two are never silently mixed.
`_coalition_values` now verifies all `range(env.n_agents)`.

### QUERY Bug D -- "Q" was a one-step reward, not a continuation return
`evaluate` did one `env.step` and took `rewards[outcome_agent]`, i.e.
`Q^(1)_j(a)`, while the surrounding protocol called it `Q_j(a)`, which a reader
will take as a continuation return.  This was a semantic-contract defect, not an
arithmetic one.

Fixed both ways the audit suggested.  The record now carries `estimand`,
`horizon` and `discount`, defaulting to `Q_one_step`/1; the oracle accepts
`horizon`, `discount` and a frozen `continuation_policy` and computes the
discounted continuation return when `horizon > 1`, refusing `horizon > 1`
without an explicit policy.  The transfer artifact now declares
`response_estimand: Q_one_step` with its definition and an explicit statement
that it is NOT `Q^(h,rho)`.

### MASTER -- evidence keys were not unique
`EvidenceItem.__post_init__` rejected empty keys but nothing rejected duplicates,
while both solvers report SELECTED KEYS as the provenance of a solution.  With a
duplicate key that provenance no longer identifies which items were chosen, so a
reported cost is not reproducible from it.  Both solvers now fail closed via
`_require_unique_evidence_keys`.  The current generator emits unique keys, so no
existing artifact is affected.

### Archive debris
`compile_source_tree.EXCLUDED` had `__MACOSX` but not AppleDouble sidecars
(`._*.py`), `.DS_Store` or `*.rej`.  AppleDouble files are not Python, so a raw
`pytest -q` on an unpacked ZIP fails at COLLECTION and reads like a source
failure.  Added `is_archive_debris()` covering `._*`, `.DS_Store`, `*.rej`,
`*.orig`, plus `.git`, `.venv`, `.lake`.

Note: `scripts/run_external_query_transfer.py.rej` is still on disk (a leftover
from a failed patch apply) and should be deleted; it is now excluded from
compilation but it is still shipped by anything that copies the tree.

## Verification
- `compile_source_tree`: 13060 files, 0 errors.
- Targeted suite: 83 passed, 2 failed -- both failures are the pre-existing
  `ModuleNotFoundError: torch` in `run_experiment.py`, unrelated to these
  changes and absent on a machine with torch installed.
- 7 new regression tests were added.  Each one fails on the pre-audit code
  (the split flags, `aggregate_transfer_matrix`, `execution_verified_sources`
  and `estimand` simply do not exist there), so they are not vacuous.

## Agreed, no code change
- The D6 strict rank-one counterexample survives independent recomputation.
  Evidence class stays `EXACT_RATIONAL_COUNTEREXAMPLE_INDEPENDENTLY_RECOMPUTED`,
  not `PROVED FALSE`, until the exact witness is Lean-checked against the formal
  definitions.  Do not resume proving `RankOne => (m-1)`.
- Gamma-box: intervals are constructed to contain the truth, so the result is
  deterministic utility and non-vacuity, NOT statistical coverage.  Do not write
  "95% valid coverage".
- Support: exact within the generated support family; not a minimax law for
  arbitrary support classes.
- Structural: `staircaseF` takes values in {0, +/-1}, so every relevant radius is
  a dyadic rational exactly representable in binary floating point; "exact" is
  safe for this family specifically.
- Functional: protocol integrity passes.  `lambda_D_median` is inflated by
  near-zero denominators and must not be a headline.  Selecting the best-looking
  CI out of 20-30 metrics would be post-selection inference.

## Still open
- The QUERY external-transfer matrix should not be used as final scientific
  evidence until the fixed pipeline is RE-RUN.  The fixes change what is
  aggregated; existing artifacts were produced by the defective aggregation and
  must not be reinterpreted, only superseded.
- `PROTOCOL_VERSION` is now
  `external_query_transfer_v4_split_evaluability_and_matched_budget`, so old and
  new artifacts cannot be confused.
